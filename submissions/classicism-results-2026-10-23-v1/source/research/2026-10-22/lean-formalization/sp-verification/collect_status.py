#!/usr/bin/env python3
"""Collect SP checks and recheck their fingerprints against current sources.

Read-only with respect to proof sources and compiler caches. Writes only the
JSON ledger and the table/snapshot of verification-status.md in this folder.
"""
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
HANDOFF = HERE.parent
ROOT = HANDOFF.parents[2]
PROJECT = ROOT / "topics/classicism/lean"
STAGE = Path("/tmp/classicism-sp-mathlib-sources")
CONFIG = json.loads((HANDOFF / "mathlib-dependencies.json").read_text())
BINARY_ROOTS = [Path(p) for p in CONFIG["precompiled_roots"]]
MAIN_MODULES = {
    "Algebra", "C", "Computability", "Disjunction", "InfinitaryNumerals",
    "MaxConservativity", "MaxDiagram", "Reflection", "Schemas",
    "SignatureSplit", "Stability", "UniversalCore",
}


@lru_cache(None)
def binary_fingerprint():
    digest = hashlib.sha256()
    for root in BINARY_ROOTS:
        for f in sorted(root.rglob("*")):
            if f.is_file() and f.name.endswith(
                (".olean", ".olean.private", ".olean.server", ".ir", ".so", ".dylib")
            ):
                digest.update(str(f.relative_to(root)).encode())
                digest.update(hashlib.sha256(f.read_bytes()).digest())
    return digest.hexdigest()


@lru_cache(None)
def fingerprint(name, compiler):
    relative = name.replace(".", "/")
    standalone = HANDOFF / (name + ".lean")
    candidates = [standalone, PROJECT / (relative + ".lean"), STAGE / (relative + ".lean")]
    source = next((f for f in candidates if f.is_file()), None)
    if source is None:
        if any((p / (relative + ".olean")).exists() for p in BINARY_ROOTS):
            return binary_fingerprint() + ":" + name
        return name
    imports = []
    for line in source.read_text().splitlines():
        m = re.match(r"^(?:public\s+)?import\s+(.+)", line)
        if m:
            imports.extend(m.group(1).split("--")[0].split())
    dependencies = "".join(fingerprint(n, compiler) for n in imports)
    return hashlib.sha256(source.read_bytes() + compiler.encode() + dependencies.encode()).hexdigest()


@lru_cache(None)
def binary_fingerprint_v2(roots, complete_ir):
    digest = hashlib.sha256()
    suffixes = (".olean", ".olean.private", ".olean.server", ".ir", ".so", ".dylib")
    if complete_ir:
        suffixes += (".ir.sig", ".ir.sig.hash", ".ilean")
    for root_name in roots:
        root = Path(root_name)
        digest.update((str(root) + "\0").encode())
        for f in sorted(root.rglob("*")):
            if f.is_file() and f.name.endswith(suffixes):
                digest.update((str(f.relative_to(root)) + "\0" +
                    hashlib.sha256(f.read_bytes()).hexdigest()).encode())
    return digest.hexdigest()


def current_v2(name, manifest, checked):
    """Validate the captured transitive inputs without launching a compiler."""
    compiler = Path(manifest["compiler_path"])
    if not compiler.exists() or hashlib.sha256(compiler.read_bytes()).hexdigest() != manifest["compiler_sha256"]:
        return False
    roots = tuple(manifest.get("precompiled_roots", []))
    # Early schema-2 manifests preceded the runner's IR-signature fix.
    # Match the recorded policy; do not reinterpret their accepted input hash.
    binary_digest = binary_fingerprint_v2(roots, True)
    if binary_digest != manifest["precompiled_sha256"]:
        binary_digest = binary_fingerprint_v2(roots, False)
    if binary_digest != manifest["precompiled_sha256"]:
        return False
    sources = manifest["sources"]

    @lru_cache(None)
    def expected(module):
        if module not in sources:
            if any((Path(r) / (module.replace(".", "/") + ".olean")).exists() for r in roots):
                return binary_digest + ":" + module
            return module
        entry = sources[module]
        path = Path(entry["path"])
        content = path.read_bytes()
        source_hash = hashlib.sha256(content).hexdigest()
        if source_hash != entry["sha256"]:
            raise ValueError("source changed")
        imports = []
        for line in content.decode().splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+)", line)
            if match:
                imports.extend(match.group(1).split("--")[0].split())
        payload = dict(schema_version=2, module=module, source_sha256=source_hash,
            compiler=manifest["compiler"], compiler_sha256=manifest["compiler_sha256"],
            dependencies=[(dependency, expected(dependency)) for dependency in imports])
        return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()

    try:
        return expected(name) == checked["fingerprint"]
    except (OSError, ValueError):
        return False


def main():
    manifest_paths = list((HANDOFF / "checks").glob("*.json"))
    for directory in (HERE, HANDOFF / "sp-universal-verification"):
        manifest_paths.extend((directory / "checks").glob("*.json"))
    histories = {}
    manifests = {}
    for path in sorted(manifest_paths, key=lambda p: p.name):
        manifest = json.loads(path.read_text())
        manifests[str(path.relative_to(HANDOFF))] = manifest
        for row in manifest.get("checked", []):
            name = row.get("module", "")
            if not name.startswith("StrongPossibilityConsequences"):
                continue
            record = dict(row, manifest=str(path.relative_to(HANDOFF)), compiler=manifest["compiler"])
            if row.get("log"):
                record["archived_log"] = str((path.parent.parent / row["log"]).relative_to(HANDOFF))
            histories.setdefault(name, []).append(record)
    records = []
    for source in sorted(HANDOFF.glob("StrongPossibilityConsequences*.lean")):
        short = source.stem.removeprefix("StrongPossibilityConsequences")
        history = histories.get(source.stem, [])
        check = dict(history[-1]) if history else None
        current = False
        if check:
            manifest = manifests[check["manifest"]]
            current = current_v2(source.stem, manifest, check) if manifest.get("schema_version") == 2 else (
                check["fingerprint"] == fingerprint(source.stem, check["compiler"]))
            check["manifest_schema_version"] = manifest.get("schema_version", 1)
        if check and not check.get("archived_log"):
            old = next((r for r in reversed(history) if r["fingerprint"] == check["fingerprint"]
                and r.get("exit_code") == 0 and r.get("archived_log")), None)
            if old:
                check["archived_log"] = old["archived_log"]
        if not check:
            status = "not yet checked"
        elif not current:
            status = "source/dependency changed; recheck required"
        elif check.get("exit_code") == 0:
            status = "passed"
            if check.get("archived_log"):
                log = (HANDOFF / check["archived_log"]).read_text()
                if "sorryAx" in log:
                    status = "axiom audit failed"
        elif check.get("exit_code") == 125:
            status = "blocked by dependency failure"
        else:
            status = "failed; repair in progress"
        owner = "SP author; completed"
        if short in {"UniversalCore", "Disjunction"}:
            owner = "dedicated universal-schema proof agent"
        elif short in {"Schemas", "SignatureSplit", "Reflection", "MaxConservativity", "C", "Stability"}:
            owner = "core integration task"
        records.append(dict(module=source.stem, short_name=short, status=status,
            source_sha256_at_report=hashlib.sha256(source.read_bytes()).hexdigest(),
            current_fingerprint_matches_check=current, owner=owner, check=check,
            kind="ordinary metatheory; not an object-language C certificate"
                if short in {"Algebra", "Computability", "InfinitaryNumerals"}
                else "C certificates or metatheory concluding actual C derivations"))
    additional = [r for r in records if r["short_name"] not in MAIN_MODULES]
    records = [r for r in records if r["short_name"] in MAIN_MODULES]
    now = datetime.now(timezone.utc).isoformat()
    passed = sum(r["status"] == "passed" for r in records)
    data = dict(reported_at_utc=now, source_scope="twelve SP/Max source modules; not the full repository",
        passed_count=passed, module_count=len(records),
        core_thread_id="01a1664d-7c13-7701-b52c-2070ee16eb06", modules=records,
        additional_modules=additional)
    (HERE / "verification-status.json").write_text(json.dumps(data, indent=2) + "\n")
    report = HERE / "verification-status.md"
    text = report.read_text()
    text = re.sub(r"Snapshot: .*", f"Snapshot: {now}. **{passed} of {len(records)} modules have successful saved Lean checks matching current sources and dependencies.**", text, count=1)
    start = text.index("| Module (common")
    end = text.index("\n## Work completed", start)
    lines = ["| Module (common StrongPossibilityConsequences prefix omitted) | Latest check | Evidence |",
        "| --- | --- | --- |"]
    for row in records:
        check = row["check"]
        evidence = "Assigned for checking."
        if check:
            evidence = f"[Saved check](../{check.get('archived_log', check['manifest'])})"
        lines.append(f"| {row['short_name']} | {row['status']} | {evidence} |")
    for row in additional:
        check = row["check"]
        evidence = (f"[Saved check](../{check.get('archived_log', check['manifest'])})"
            if check else "No saved check yet.")
        lines.append(f"| {row['short_name']} (additional audit; outside the twelve-module count) | {row['status']} | {evidence} |")
    report.write_text(text[:start] + "\n".join(lines) + "\n" + text[end:])
    print(f"{passed}/{len(records)} modules pass with matching current source/dependency fingerprints.")
    for row in records:
        print(row["short_name"], row["status"])
    for row in additional:
        print(row["short_name"], "(additional)", row["status"])


if __name__ == "__main__":
    main()
