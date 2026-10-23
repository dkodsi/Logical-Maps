#!/usr/bin/env python3
"""Globally serial, bounded Lean checks of immutable source snapshots.

Never invokes Lake or downloads. Compilation alone is not a database certificate.
"""
import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[3]
PROJECT = ROOT / "topics/classicism/lean"
HANDOFF = Path(__file__).resolve().parent
# Independent of HANDOFF, cache, wrapper, and source-root options.
GLOBAL_LOCK = Path("/tmp/classicism-lean-global-compiler.lock")
ARTIFACT_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig",
                     ".ir.sig.hash", ".ilean")
PRECOMPILED_SUFFIXES = ARTIFACT_SUFFIXES + (".so", ".dylib")


def file_hash(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def atomic_text(path, text):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    try:
        temporary.write_text(text)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


class BusyError(Exception):
    pass


@contextmanager
def compiler_lock(wait, owner):
    fd = os.open(GLOBAL_LOCK, os.O_CREAT | os.O_RDWR, 0o600)
    deadline = time.monotonic() + wait
    try:
        while True:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    try:
                        previous = json.loads(GLOBAL_LOCK.with_suffix(".owner.json").read_text())
                    except (OSError, ValueError):
                        previous = {"owner": "unavailable"}
                    raise BusyError("Compiler busy; no check started. " + json.dumps(previous))
                time.sleep(min(0.2, max(0, deadline - time.monotonic())))
        atomic_text(GLOBAL_LOCK.with_suffix(".owner.json"), json.dumps(owner, indent=2) + "\n")
        yield fd
    finally:
        # No LOCK_UN: a surviving compiler inheriting this open description must
        # retain the lock when its Python parent is terminated.
        os.close(fd)


def capture_sources(args, source_roots, binary_roots):
    """Capture a stable closure, retrying ordinary concurrent source edits."""
    paths = [(ROOT / n).resolve() for n in args.modules if n.endswith(".lean")]
    for attempt in range(3):
        standalone = {p.stem: p for parent in {p.parent for p in paths}
                      for p in parent.glob("*.lean")}
        standalone.update({p.stem: p for p in paths})
        ordered, seen, external = [], set(), set()

        def visit(name):
            if name in seen:
                return
            seen.add(name)
            relative = name.replace(".", "/")
            source = standalone.get(name)
            if source is None:
                source = next((root / (relative + ".lean") for root in source_roots
                               if (root / (relative + ".lean")).exists()),
                              PROJECT / (relative + ".lean"))
            if not source.exists():
                external.add(name)
                return
            content = source.read_bytes()
            imports = []
            for line in content.decode().splitlines():
                match = re.match(r"^\s*(?:public\s+)?import\s+(.+)", line)
                if match:
                    imports.extend(match.group(1).split("--")[0].split())
            for dependency in imports:
                visit(dependency)
            ordered.append((name, source, imports, content))

        try:
            for name in args.modules:
                visit(Path(name).stem if name.endswith(".lean") else name)
            stable = all(source.read_bytes() == content for _, source, _, content in ordered)
        except FileNotFoundError:
            stable = False
        if stable:
            precompiled = {name for name in external if any(
                (root / (name.replace(".", "/") + ".olean")).exists()
                for root in binary_roots)}
            bad = sorted(name for name in external if name not in precompiled and
                         name.split(".")[0] not in {"Init", "Lean", "Std", "Lake"})
            if bad:
                raise RuntimeError("Unavailable external dependency; no fetch attempted: " + ", ".join(bad))
            return ordered, external, precompiled
    raise RuntimeError("Source closure changed during three capture attempts; retry when edits settle.")


def artifacts(out):
    base = str(out)[:-len(".olean")]
    return {suffix: Path(base + suffix) for suffix in ARTIFACT_SUFFIXES
            if Path(base + suffix).is_file()}


def reusable(out, digest):
    try:
        metadata = json.loads(out.with_suffix(".artifacts.json").read_text())
        actual = artifacts(out)
        return (metadata.get("schema_version") == 2 and
                metadata.get("fingerprint") == digest and
                out.with_suffix(".sha256").read_text() == digest and
                ".olean" in actual and
                metadata.get("artifacts") == {suffix: file_hash(path)
                                               for suffix, path in actual.items()})
    except (OSError, ValueError):
        return False


def publish_artifacts(staged, out, digest, source_hash):
    produced = artifacts(staged)
    if ".olean" not in produced:
        raise RuntimeError("Compiler exited successfully without producing the requested .olean.")
    hashes = {suffix: file_hash(path) for suffix, path in produced.items()}
    old = artifacts(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    base = str(out)[:-len(".olean")]
    for suffix, path in produced.items():
        os.replace(path, Path(base + suffix))
    for suffix, path in old.items():
        if suffix not in produced:
            path.unlink()
    # Same-lock readers cannot observe a partial publication. After a crash,
    # artifact hashes reject any mixture left before metadata/stamp publication.
    atomic_text(out.with_suffix(".artifacts.json"), json.dumps(dict(
        schema_version=2, fingerprint=digest, source_sha256=source_hash,
        artifacts=hashes), indent=2) + "\n")
    atomic_text(out.with_suffix(".sha256"), digest)
    return hashes


def overlay_artifacts(overlay, name, out):
    """Expose only checked local artifacts, never arbitrary stale cache files."""
    relative = name.replace(".", "/")
    for suffix in ARTIFACT_SUFFIXES:
        target = overlay / (relative + suffix)
        target.unlink(missing_ok=True)
    for suffix, source in artifacts(out).items():
        target = overlay / (relative + suffix)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(source)


def run_check(args, lock_fd, report, save):
    cache = Path(args.cache).resolve()
    source_roots = [PROJECT] + [Path(x).resolve() for x in args.source_root]
    binary_roots = [Path(x).resolve() for x in args.precompiled_root]
    binary_digest = hashlib.sha256()
    binary_files = []
    for root in binary_roots:
        if not root.is_dir():
            raise RuntimeError(f"Missing precompiled library root: {root}")
        binary_digest.update((str(root) + "\0").encode())
        for path in sorted(root.rglob("*")):
            # Lean 4.33 loads no IR parts when the companion .ir.sig is absent,
            # even if .ir exists. Preserve and fingerprint the complete pair.
            if path.is_file() and path.name.endswith(PRECOMPILED_SUFFIXES):
                binary_digest.update((str(path.relative_to(root)) + "\0" + file_hash(path)).encode())
                binary_files.append((root, path))
    ordered, external, precompiled = capture_sources(args, source_roots, binary_roots)
    print(f"Closure: {len(ordered)} local modules; external: {', '.join(sorted(external))}", flush=True)
    report["sources"] = {name: dict(path=str(source), sha256=hashlib.sha256(content).hexdigest())
                         for name, source, _, content in ordered}
    report["precompiled_roots"] = list(map(str, binary_roots))
    report["precompiled_sha256"] = binary_digest.hexdigest()
    if args.plan:
        for name, _, _, _ in ordered:
            print(name)
        report["state"] = "planned"
        return 0
    compiler = Path(shutil.which(args.lean) or args.lean).resolve()
    report["compiler_path"] = str(compiler)
    report["compiler_sha256"] = file_hash(compiler)
    version = subprocess.check_output([str(compiler), "--version"], text=True,
                                      timeout=min(args.timeout, 30), pass_fds=(lock_fd,)).strip()
    report["compiler"] = version
    run_dir = HANDOFF / "logs" / "runs" / report["run_id"]
    snapshot = run_dir / "sources"
    staging = cache / ".staging" / report["run_id"]
    overlay = staging / "imports"
    snapshot.mkdir(parents=True, exist_ok=True)
    overlay.mkdir(parents=True, exist_ok=True)
    # A single merged import tree avoids Lean selecting a partial namespace
    # from one LEAN_PATH root and hiding modules available in another root.
    for root, source in binary_files:
        target = overlay / source.relative_to(root)
        if not target.is_symlink():
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(source)
    for name, _, _, content in ordered:
        target = snapshot / (name.replace(".", "/") + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    report["source_snapshot"] = str(snapshot)
    save()
    env = dict(os.environ, LEAN_PATH=str(overlay))
    fingerprints = {name: binary_digest.hexdigest() + ":" + name for name in precompiled}
    failed = set()
    try:
        for name, source, deps, content in ordered:
            source_hash = hashlib.sha256(content).hexdigest()
            digest = hashlib.sha256(json.dumps(dict(
                schema_version=2, module=name, source_sha256=source_hash,
                compiler=version, compiler_sha256=report["compiler_sha256"],
                dependencies=[(dep, fingerprints.get(dep, dep)) for dep in deps]),
                sort_keys=True).encode()).hexdigest()
            fingerprints[name] = digest
            out = cache / (name.replace(".", "/") + ".olean")
            entry = dict(module=name, fingerprint=digest, source_sha256=source_hash)
            report["current_module"] = name
            if any(dep in failed for dep in deps):
                failed.add(name)
                report["checked"].append(dict(entry, skipped="dependency failed", exit_code=125))
                save()
                continue
            if reusable(out, digest):
                overlay_artifacts(overlay, name, out)
                entry["artifacts"] = {suffix: file_hash(path)
                                      for suffix, path in artifacts(out).items()}
                report["checked"].append(dict(entry, reused=True, exit_code=0))
                save()
                continue
            staged = staging / (name.replace(".", "/") + ".olean")
            staged.parent.mkdir(parents=True, exist_ok=True)
            log = run_dir / (name.replace(".", "_") + ".log")
            start = time.monotonic()
            save()
            try:
                with log.open("w") as stream:
                    result = subprocess.run([str(compiler), "-o", str(staged),
                                             name.replace(".", "/") + ".lean"],
                                            cwd=snapshot, env=env, stdout=stream,
                                            stderr=subprocess.STDOUT, timeout=args.timeout,
                                            pass_fds=(lock_fd,))
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = 124
                with log.open("a") as stream:
                    stream.write(f"\nTIMEOUT after {args.timeout} seconds.\n")
            audit_text = log.read_text()
            audits = re.findall(r": (\d+) of (\d+) theorems derived", audit_text)
            audits += re.findall(r": (\d+)/(\d+) (?:theorems pass|inside R)", audit_text)
            if code == 0 and any(int(done) != int(total) for done, total in audits):
                code = 1
                with log.open("a") as stream:
                    stream.write("\nINCOMPLETE AUDIT: successful process exit is not full certification.\n")
            if code == 0:
                try:
                    entry["artifacts"] = publish_artifacts(staged, out, digest, source_hash)
                    overlay_artifacts(overlay, name, out)
                except (OSError, RuntimeError) as error:
                    code = 1
                    with log.open("a") as stream:
                        stream.write(f"\nPUBLICATION FAILED: {error}\n")
            elapsed = round(time.monotonic() - start, 2)
            report["checked"].append(dict(entry, seconds=elapsed, exit_code=code,
                                          log=str(log.relative_to(HANDOFF))))
            save()
            print(f"{'PASS' if code == 0 else 'FAIL'} {name} ({elapsed}s)", flush=True)
            if code:
                lines = log.read_text().splitlines()
                errors = [i for i, line in enumerate(lines) if "error:" in line or "error(" in line]
                for index in errors[:3]:
                    print("\n".join(lines[index:index + 9]), flush=True)
                if not errors:
                    print("\n".join(lines[-12:]), flush=True)
                failed.add(name)
                if not args.keep_going:
                    report["state"] = "failed"
                    return code if code > 0 else 1
        drift = []
        for name, source, _, content in ordered:
            try:
                changed = source.read_bytes() != content
            except OSError:
                changed = True
            if changed:
                drift.append(name)
        report["source_drift"] = drift
        report["current_sources_match"] = not drift
        report["complete"] = not failed and not drift
        report["state"] = "failed" if failed else "source_changed" if drift else "complete"
        if drift:
            print("Source changed after capture; snapshot results retained, rerun current sources: " + ", ".join(drift), flush=True)
        else:
            print("Requested modules checked successfully." if not failed else
                  "Some modules failed; independent checks completed.", flush=True)
        return 1 if failed else 3 if drift else 0
    finally:
        shutil.rmtree(staging, ignore_errors=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--lean", default="/tmp/classicism-lean-toolchain/lean-4.33.1-darwin_aarch64/bin/lean")
    parser.add_argument("--cache", default="/tmp/classicism-lean-cert-cache")
    parser.add_argument("--source-root", action="append", default=[])
    parser.add_argument("--precompiled-root", action="append", default=[])
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--lock-wait", type=float, default=30,
                        help="Seconds to wait for the global compiler lock; busy exits 75")
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--keep-going", action="store_true")
    args = parser.parse_args()
    if args.lock_wait < 0 or args.timeout <= 0:
        parser.error("--lock-wait must be nonnegative and --timeout must be positive")
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ") + "-" + uuid.uuid4().hex[:8]
    owner = dict(pid=os.getpid(), run_id=run_id, modules=args.modules,
                 handoff=str(HANDOFF), cache=str(Path(args.cache).resolve()))
    try:
        with compiler_lock(args.lock_wait, owner) as lock_fd:
            report = dict(schema_version=2, run_id=run_id, modules=args.modules,
                          cache=owner["cache"], state="running", complete=False, checked=[])
            manifest = HANDOFF / "checks" / (run_id + ".json")

            def save():
                text = json.dumps(report, indent=2) + "\n"
                atomic_text(manifest, text)
                atomic_text(HANDOFF / "last-check.json", text)

            save()
            try:
                code = run_check(args, lock_fd, report, save)
            except KeyboardInterrupt:
                report.update(state="interrupted", error="Interrupted", complete=False)
                code = 130
            except Exception as error:
                report.update(state="failed", error=f"{type(error).__name__}: {error}", complete=False)
                print(report["error"], file=sys.stderr)
                code = 1
            report.pop("current_module", None)
            report["exit_code"] = code
            save()
            atomic_text(GLOBAL_LOCK.with_suffix(".owner.json"), json.dumps(
                dict(owner, state="finished", exit_code=code), indent=2) + "\n")
    except BusyError as error:
        print(str(error), file=sys.stderr)
        code = 75
    if code:
        raise SystemExit(code)


if __name__ == "__main__":
    main()
