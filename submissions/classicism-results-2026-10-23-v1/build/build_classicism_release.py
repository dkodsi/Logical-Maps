#!/usr/bin/env python3
"""Assemble a traceable source/evidence release. Never compiles Lean or edits inputs."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
SPEC = HERE / "classicism-release-spec.json"
RESEARCH = Path("research/2026-10-22")
LF = RESEARCH / "lean-formalization"


def digest(p):
    h = hashlib.sha256()
    with Path(p).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def dump(p, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n")


def text(p, content):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content.rstrip() + "\n")


def source_link(path, label=None):
    return f"[{label or Path(path).name}](source/{path})"


VERIFY = r'''#!/usr/bin/env python3
"""Verify a directory or ZIP using only Python's standard library; never runs Lean."""
import argparse, hashlib, json
from pathlib import Path
import zipfile

def hashed(f):
    h=hashlib.sha256()
    for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--archive',type=Path);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args()
    failures=[]
    if a.archive:
        with zipfile.ZipFile(a.archive) as z:
            names=z.namelist();roots=[n[:-len('SHA256SUMS')] for n in names if n.count('/')==1 and n.endswith('/SHA256SUMS')]
            if len(roots)!=1:raise SystemExit('Expected one package root and checksum list')
            prefix=roots[0];rows=z.read(prefix+'SHA256SUMS').decode().splitlines()
            expected=set()
            for row in rows:
                sha,p=row.split('  ',1);expected.add(prefix+p)
                try:
                    with z.open(prefix+p) as f:got=hashed(f)
                    if got!=sha:failures.append(p+': hash mismatch')
                except KeyError:failures.append(p+': missing')
            actual={n for n in names if not n.endswith('/')}
            failures += ['unexpected: '+n for n in actual-expected-{prefix+'SHA256SUMS'}]
            if len(names)!=len(set(names)):failures.append('duplicate ZIP entries')
    else:
        rows=(a.root/'SHA256SUMS').read_text().splitlines();expected=set()
        for row in rows:
            sha,p=row.split('  ',1);expected.add(p)
            try:
                with (a.root/p).open('rb') as f:got=hashed(f)
                if got!=sha:failures.append(p+': hash mismatch')
            except FileNotFoundError:failures.append(p+': missing')
        actual={p.relative_to(a.root).as_posix() for p in a.root.rglob('*') if p.is_file()}
        failures += ['unexpected: '+p for p in actual-expected-{'SHA256SUMS'}]
    print(json.dumps({'verified_files':len(rows),'failures':failures,'lean_compilation_performed':False}))
    raise SystemExit(bool(failures))
if __name__=='__main__':main()
'''


REPRODUCE = r'''#!/usr/bin/env python3
"""Relocate a saved manifest's exact sources and invoke the original serial checker.
Requires an existing matching Lean/Mathlib installation; never downloads.
The default prints a plan. Compilation requires --run explicitly.
"""
import argparse,json,shutil,subprocess,sys
from pathlib import Path

def main():
    p=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser();ap.add_argument('--manifest',required=True);ap.add_argument('--lean',required=True)
    ap.add_argument('--precompiled-root',action='append',default=[]);ap.add_argument('--cache',type=Path,required=True)
    ap.add_argument('--timeout',type=int,default=180);ap.add_argument('--lock-wait',type=int,default=30);ap.add_argument('--run',action='store_true')
    a=ap.parse_args();audit=json.loads((p/'CERTIFICATE-AUDIT.json').read_text())
    entry=next((e for e in audit['manifests'] if e['path']==a.manifest or Path(e['path']).name==a.manifest),None)
    if entry is None:raise SystemExit('Manifest not in release certificate audit')
    if entry['format']=='legacy':raise SystemExit('Legacy manifest: use its archived driver and reproduction notes; no per-file source map was recorded')
    if entry['missing_or_changed']:raise SystemExit('This manifest has missing or changed source files; inspect CERTIFICATE-AUDIT.json before reproducing it')
    root=p/'source';m=json.loads((root/entry['path']).read_text());deps=json.loads((p/'DEPENDENCY-SOURCES.json').read_text())
    by_key={(e['module'],e['sha256']):e for e in deps['entries']}
    staged=a.cache.resolve()/'recorded-external-sources'
    cmd=[sys.executable,str(root/'research/2026-10-22/lean-formalization/check_module.py'),'--lean',str(Path(a.lean).resolve()),'--cache',str(a.cache.resolve()),'--source-root',str(staged),'--timeout',str(a.timeout),'--lock-wait',str(a.lock_wait)]
    for r in a.precompiled_root:cmd += ['--precompiled-root',str(Path(r).resolve())]
    targets=[]
    for target in m['modules']:
        if target.endswith('.lean') and Path(target).is_absolute():
            original=json.loads((p/'PROVENANCE.json').read_text())['original_workspace'];target=str(Path(target).relative_to(original))
        targets.append(target)
    if any('MaxAtomicityInconsistency' in t for t in targets):
        targets=['Mathlib.Lean.Expr.Rat','Mathlib.Algebra.Order.Ring.Unbundled.Rat','Mathlib.Tactic.Ring.Basic','Mathlib.Data.PNat.Basic','Mathlib.Util.AtomM.Recurse']+targets
    cmd += targets
    print(json.dumps({'command':cmd,'cwd':str(root),'run_requested':a.run},indent=2))
    if not a.run:return
    if not a.precompiled_root:raise SystemExit('Provide the pinned dependency binary roots; the toolchain alone is insufficient')
    for mod,s in m['sources'].items():
        e=by_key.get((mod,s['sha256']))
        if e:
            dest=staged/(mod.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p/e['package_path'],dest)
    raise SystemExit(subprocess.call(cmd,cwd=root))
if __name__=='__main__':main()
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--python", default="/private/tmp/classicism-followup-venv/bin/python")
    args = ap.parse_args()
    spec = json.loads(SPEC.read_text())
    out = HERE / spec["release_id"]
    archive = out.with_suffix(".zip")
    if out.exists() or archive.exists():
        raise SystemExit("Release destination already exists; use a fresh release ID rather than overwrite a delivered snapshot")
    for result in spec["results"]:
        for key in ["lean_sources", "proofs", "manifests", "evidence"]:
            for path in result[key]:
                if not (ROOT / path).is_file():
                    raise SystemExit(f"Missing specified input: {path}")
    out.mkdir(parents=True)
    captured = datetime.now(timezone.utc).isoformat()
    copied = []
    excluded = []

    def copy(src, rel, origin):
        dest = out / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        before = digest(src)
        shutil.copyfile(src, dest)
        if before != digest(dest) or before != digest(src):
            raise RuntimeError(f"Source changed during snapshot: {src}")
        copied.append({"path": rel, "sha256": before, "bytes": dest.stat().st_size,
                       "origin": origin})

    extensions = {".md", ".json", ".yaml", ".yml", ".lean", ".py", ".toml", ".txt", ".log", ".patch"}
    for base in [ROOT / "topics/classicism", ROOT / RESEARCH, ROOT / "scripts", ROOT / "schema"]:
        for p in sorted(base.rglob("*")):
            if not p.is_file() or any(x in p.relative_to(base).parts for x in [".git", ".lake", "__pycache__"]):
                continue
            rel = p.relative_to(ROOT).as_posix()
            keep_zip = p.name == "max-atomicity-lean-certificates.zip"
            required_pdf = rel == "topics/classicism/sources/prop-2-11-counterexample.pdf"
            if p.suffix not in extensions and p.name != "lean-toolchain" and not keep_zip and not required_pdf:
                if p.suffix in {".zip", ".pdf"}:
                    excluded.append({"path": rel, "sha256": digest(p), "bytes": p.stat().st_size,
                                     "reason": "Superseded partial compiled archive" if p.suffix == ".zip" else "Reference PDF; citation/source metadata retained"})
                continue
            copy(p, "source/" + rel, rel)
    for name in ["README.md", "AGENTS.md", "requirements.txt", "LICENSE", "LICENSE.md"]:
        p = ROOT / name
        if p.is_file():
            copy(p, "source/" + name, name)
    copy(SPEC, "build/classicism-release-spec.json", "release specification")
    copy(Path(__file__), "build/build_classicism_release.py", "release assembly script")

    selected = {m for r in spec["results"] for m in r["manifests"]}
    lane_updates = []
    for p in sorted((out / "source" / LF / "verification-updates").glob("*.json")):
        d = json.loads(p.read_text())
        m = d.get("manifest")
        if m:
            candidates = [Path(m), LF / m]
            found = next((x.as_posix() for x in candidates if (ROOT / x).is_file()), None)
            if found:
                selected.add(found)
        lane_updates.append({"path": p.relative_to(out).as_posix(), "report": d})
    audits, external = [], {}
    for name in sorted(selected):
        p = ROOT / name
        d = json.loads(p.read_text())
        entry = {"path": name, "sha256": digest(p), "format": "source-map" if d.get("sources") else "legacy",
                 "reported_complete": d.get("complete"), "reported_exit_code": d.get("exit_code"),
                 "reported_current_sources_match_at_run": d.get("current_sources_match"),
                 "requested_targets": d.get("modules", []), "source_checks": [], "missing_or_changed": [],
                 "successful_modules": [x.get("module") for x in d.get("checked", []) if x.get("exit_code") == 0]}
        for mod, info in d.get("sources", {}).items():
            original = Path(info["path"])
            expected = info["sha256"]
            current = digest(original) if original.is_file() else None
            good = current == expected
            try:
                relative = original.resolve().relative_to(ROOT.resolve()).as_posix()
                package_path = "source/" + relative
                if not (out / package_path).is_file() or digest(out / package_path) != expected:
                    good = False
            except ValueError:
                package_path = "dependencies/sources/" + expected[:16] + "/" + mod.replace(".", "/") + ".lean"
                key = (mod, expected)
                if good and key not in external:
                    copy(original, package_path, {"external_original_path": str(original), "module": mod})
                    external[key] = {"module": mod, "sha256": expected, "package_path": package_path,
                                     "original_path": str(original)}
            check = {"module": mod, "original_path": str(original), "expected_sha256": expected,
                     "observed_sha256": current, "matches": good, "package_path": package_path}
            entry["source_checks"].append(check)
            if not good:
                entry["missing_or_changed"].append(check)
        audits.append(entry)
    # Licenses for the preserved pinned third-party source subset.
    for name, p in [("mathlib", Path("/private/tmp/classicism-mathlib/LICENSE")),
                    ("batteries", Path("/private/tmp/classicism-mathlib/.lake/packages/batteries/LICENSE"))]:
        if p.exists():
            copy(p, f"dependencies/licenses/{name}-LICENSE", {"external_original_path": str(p)})
    dump(out / "DEPENDENCY-SOURCES.json", {"scope": "Only exact matching external sources from the selected saved manifests; full dependencies/toolchain are pinned separately, not bundled.", "entries": list(external.values())})
    dump(out / "CERTIFICATE-AUDIT.json", {"captured_at_utc": captured,
         "method": "Read saved manifests; hash current inputs and copied sources. No Lean compiler was run. Legacy manifests have no later per-file source map. Binary dependency roots are recorded, not rehashed by this packaging run.", "manifests": audits})
    dump(out / "LANE-CHECKPOINTS.json", {"snapshots": lane_updates})
    dump(out / "MAIN-RESULTS.json", spec)
    original = json.loads((out / "source" / RESEARCH / "consolidation/results.json").read_text())
    related = {}
    for result in spec["results"]:
        for key in result["registry_ids"]:
            related.setdefault(key, []).append(result["id"])
    catalog = [{"id": e["id"], "statement_as_recorded": e["statement_or_contribution_as_recorded"],
                "original_registry_status": e["lean"]["registry_category"],
                "original_sources": e["natural_language_sources"],
                "original_lean_mapping": e["lean"], "release_main_result_crossreferences": related.get(e["id"], [])}
               for e in original["entries"]]
    dump(out / "CATALOG.json", {"source_index_generated_at_utc": original.get("generated_at_utc"),
         "warning": "Original registry categories are preserved historical evidence. MAIN-RESULTS and LANE-CHECKPOINTS contain later scoped updates; crossreferences are not wholesale upgrades of aggregate families.", "entries": catalog})

    lines = ["# Main results and Lean status", "", f"Release: `{spec['release_id']}`. Evidence captured {captured}.", "",
             "All results use the original finitary relational Classicism unless a scope explicitly says otherwise. C5 means C + boxed ND; B means C + boxed Plenitude; F means C + boxed Functional Choice. `Checked` below means a saved successful Lean certificate for the stated scope, not a new compilation during packaging. `Partial` means the whole headline theorem or construction has not been certified. A proposed or conditional claim is not counted as an unconditional theorem.", "",
             "The strongest change since the early synthesis is the final Max–Atomicity inconsistency certificate. Older source notes are preserved byte for byte; later evidence below supersedes their earlier verification-status prose.", "",
             "| Result | Lean status |", "|---|---|"]
    lines += [f"| [{r['title']}](#{r['id'].lower()}) | {r['lean_status']} |" for r in spec["results"]]
    for r in spec["results"]:
        lines += ["", f"<a id=\"{r['id'].lower()}\"></a>", f"## {r['title']}", "", f"**{r['statement']}**", "",
                  f"**Scope:** {r['scope']}", "", f"**Lean:** {r['lean_status']}.", "", r["notes"], "",
                  "Trace IDs: " + ", ".join(f"`{x}`" for x in r["registry_ids"]) + ".", ""]
        if r["declarations"]:
            lines += ["Principal declarations:", ""] + [f"- `{x}`" for x in r["declarations"]] + [""]
        for label, key in [("Prose proofs", "proofs"), ("Lean sources", "lean_sources"), ("Compiler manifests", "manifests"), ("Audits and status", "evidence")]:
            if r[key]:
                lines += [f"{label}: " + " · ".join(source_link(x) for x in r[key]), ""]
    lines += ["## Remaining boundaries", "", "Strong Possibility consistency is not proved. Relational Choice alone implying Transversal Choice and the full all-type Tame Rigidity + Rigid Power implication remain separate unresolved questions. The finite-Choice negative theorem, probability classifications, full profile/model classifications and broad arithmetic/effective comparisons retain the partial formalization boundaries above. The package is a complete snapshot of the selected collection, not a claim that every tracked mathematical family is complete."]
    text(out / "MAIN-RESULTS.md", "\n".join(lines))

    index = ["# Traceable result catalog", "", f"The {len(catalog)} original tracked keys are preserved. These include conditional and unfinished entries; this is not a theorem count.", "", "The original per-family registry status is shown verbatim. Later release crossreferences have exact narrower scopes and must be read before using the historical status.", "", "| ID | Original registry category | Later release crossreference | Original proof navigation |", "|---|---|---|---|"]
    for e in catalog:
        refs = ", ".join(f"[{x}](MAIN-RESULTS.md#{x.lower()})" for x in e["release_main_result_crossreferences"]) or "See lane checkpoint"
        proofs = " · ".join(source_link(p) for p in e["original_sources"] if (out / "source" / p).is_file())
        index.append(f"| `{e['id']}` | {e['original_registry_status']} | {refs} | {proofs} |")
    text(out / "CATALOG.md", "\n".join(index))

    readme = f'''# Classicism results and Lean certificate evidence

Release **{spec['release_id']}**, captured **{captured}**.

This is a shareable, hashed snapshot for the database owners. It combines the original research, database context, Lean proof sources, saved compiler manifests and axiom reports, and the final author checkpoints. **It does not change or automatically import any database verdict.**

Start with [Main results and Lean status](MAIN-RESULTS.md), then the [160-key catalog](CATALOG.md). The machine-readable counterparts are [MAIN-RESULTS.json](MAIN-RESULTS.json) and [CATALOG.json](CATALOG.json). [Database handoff](DATABASE-HANDOFF.md) explains attribution, corrections and import boundaries.

## Traceability

- `source/` preserves original repository-relative paths and original bytes, including historical notes and failed-check reports. Such reports are evidence of chronology, not accepted certificates.
- [CERTIFICATE-AUDIT.json](CERTIFICATE-AUDIT.json) records the selected compiler reports and freshly compared source hashes. It distinguishes later source-map manifests from legacy reports.
- [LANE-CHECKPOINTS.json](LANE-CHECKPOINTS.json) contains the final inspected author reports, including unfinished work.
- [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) maps preserved files to original paths and content hashes. [PROVENANCE.json](PROVENANCE.json) records the collection boundary and exclusions.
- `SHA256SUMS` hashes every other archive file, including the inventories. Run `python3 verify_package.py` after extraction, or `python3 verify_package.py --archive ../{spec['release_id']}.zip` to check the archive directly.

## Lean evidence and reproduction

The package contains source proofs and recorded successful checks, with their exact limitations. The existing complete Max–Atomicity author archive, including its local compiled artifacts, is retained at its original relative path under `source/research/2026-10-22/lean-formalization/`. Its older partial-background archive is excluded as redundant and identified by hash in PROVENANCE.

Lean **4.33.1**, the exact Mathlib commit and all dependency revisions are pinned in the preserved `lean-toolchain` and `lake-manifest.json`. The exact available third-party source subset referenced by selected reports is included with licenses. **The complete external Lean/Mathlib installation and its platform-specific binary caches are not bundled.** [Reproducing checks](REPRODUCING.md) documents installation prerequisites, the portable relocation helper and the serial compiler protocol.

No Lean compiler was run for this packaging operation. Source-hash verification establishes correspondence to saved evidence, not a new kernel check. Legacy manifests without per-file maps are explicitly identified; their saved axiom logs and coordinating review remain available.

## Reading older material

Use MAIN-RESULTS for delivery status. The original consolidation index predates some final checks; the earlier synthesis's open/conditional Max–Atomicity wording is superseded by the final certificate. [Release notes](RELEASE-NOTES.md) list these changes. Original absolute `/tmp` paths and older broken note links are preserved for provenance; [LINK-AUDIT.json](LINK-AUDIT.json) inventories them. All new release navigation is checked against the actual package.

This release makes no literature-novelty claim and does not equate supporting Lean modules with fully formalized headline theorems. The user-selected working package remains Classicism + necessary Functional Choice + quantified Infinity at every admitted type.
'''
    text(out / "README.md", readme)
    text(out / "DATABASE-HANDOFF.md", '''# Handoff to the database owners

This is a source-and-evidence submission for review. Preserve the original framework C, type grammar and schema theoremhood restrictions. The database snapshot is included for exact ID lookup, but research verdicts have not been merged into it.

1. Locate a tracked key in CATALOG.json. Follow its prose proof, corrected version, principal declaration and saved compiler/axiom evidence in MAIN-RESULTS or the final lane checkpoint. A thematic crossreference does not upgrade every claim in an aggregate family.
2. Check local versus boxed premises, pure versus named signatures, each admitted type/tuple, internal versus external finiteness, and whether the theorem is conditional. Countermodel results belong in model records, not implication records.
3. Use the notes' actual attribution. Session-created proofs use direct source `misc`; background papers keep their actual theorem/page citations. Do not put an AI audit into a human `checked_by` field or attribute a new proof to a paper merely used for background.
4. The old/new model needs its correction: the external even-haecceity family was not admitted; full local BC at E is now proved. The original human/source construction is preserved. Add the corrected argument and history rather than rewriting an original proof.
5. Pure Maximalism + unboxed Atomicity_t now has a complete final certificate. Older conditional-only reports and the historical synthesis must not control that final verdict. The exact bare-C non-theorem and final inconsistency declarations are both linked.
6. Necessary Functional Choice decompositions, central-signature models and numerical transfer have exact scope boundaries. In particular, the checked one-constant model is not a certificate for all richer signatures, and a boxed ordinary-section equivalence is not the unboxed strong-section formulation.
7. Do not import draft or partial mathematics as proved merely because an associated source exists. Full probability, finite-Choice negative forcing/extraction, full profile/model classifications and broad arithmetic/effective comparisons retain their own gaps. SP consistency remains unresolved.
8. Use the repository's existing validation and certificate workflow before changing official `lean: verified` flags. A passing research-module check does not automatically update a generated record statement. Run validation after any eventual database edits.

All source files and historical reports are byte-preserved. Later evidence is an overlay in the release catalog, never a silent change to an old proof. Missing external bibliographic locators, including the explicitly noted Howard–Tachtsis input, remain review items.
''')
    text(out / "RELEASE-NOTES.md", '''# Delivery status changes since the early consolidation

- **Max + Atomicity:** the final unconditional pure-C inconsistency declaration passed at the 05:47 UTC run, with the final author checkpoint at 05:51 UTC. It replaces the earlier conditional-only status, not the historical source files.
- **OldNew:** the complete Tame Rigidity/future-BC assembly passed in the 04:58 UTC run, in addition to the earlier central separator.
- **Choice and sections/retractions:** the 05:39 UTC aggregate includes reverse ordinary constructions, necessitated ordinary-splitting equivalences, and the declared persistence/representation laws. The necessary-Actuality plus unboxed-strong-sections equivalence remains separately unfinished.
- **Central models:** a concrete one-predicate Logical-Necessity/boxed-BF/boxed-Relational-Choice separator is checked, including the separately reported Vicinity failure. The arbitrary-signature/full-completeness variants retain their own gaps.
- **Elementary signature models:** the finite and natural individual-domain constructions and twelve displayed applications passed. This is not completion of the nominal-world classification program.
- **Rigidity and SP:** the exact local-rigidity schema assembly and twelve SP/Max modules have completed evidence. No SP consistency theorem is inferred.
- **Arithmetic, probability and cores:** later foundational certificates are included; they do not certify every higher-level interpretation, probability classification or effective comparison.

The original index and synthesis remain in the source tree, with their original hashes. MAIN-RESULTS, exact declarations and the final checkpoints provide the release overlay. This is a fixed source/evidence snapshot, not a claim of independent human review or complete formalization of all 160 tracked entries.
''')
    text(out / "REPRODUCING.md", '''# Reproducing the recorded checks

## 1. Check the delivered bytes

Run `python3 verify_package.py`. Python's standard library is sufficient. This hashes the delivered files and does not execute Lean or any archived script. The adjacent `.zip.sha256` file supplies the outer archive hash.

## 2. Prerequisites

The preserved `source/topics/classicism/lean/lean-toolchain` pins Lean 4.33.1. `lake-manifest.json` pins Mathlib to commit `0df444a360eaa60ab8c11dca51a86af692955474` and records the exact remaining package commits. Use those revisions on the recipient's platform. The toolchain and full dependency binaries are prerequisites, not included distributions; this release has performed no downloads. The `dependencies/` subset preserves the exact matching external sources used in selected checks, with their licenses and hash inventory.

Do not use a whole-library default build as evidence for a specific result: the tree intentionally includes draft modules. Reproduce only the relevant exact target and its dependencies. The existing globally serial runner is preserved, including its lock and bounded timeout behavior. Never remove another process's compiler lock.

## 3. Portable source-map reproduction

`reproduce_certificate.py` relocates a selected saved manifest, uses only matching supplied source bytes, and delegates to the original serial checker. It prints a plan by default. Supply an existing matching Lean executable, the required compiled dependency roots from your pinned installation, and a fresh writable output cache:

```sh
python3 reproduce_certificate.py \
  --manifest 20261023T054730505817Z-9a834f08.json \
  --lean /your/lean-4.33.1/bin/lean \
  --precompiled-root /your/mathlib/.lake/build/lib/lean \
  --precompiled-root /your/mathlib/.lake/packages/batteries/.lake/build/lib/lean \
  --cache /your/writable/check-cache
```

Add the other compiled dependency roots required by the target, as recorded in its manifest. Review the plan, then append `--run` to compile. The helper supplies the five explicit Mathlib roots required by the documented public-meta-import parser omission for the final Max target. It does not silently rewrite the original checker. Run in a separate working copy if you want to keep the verified package directory unchanged: new compiler logs/cache reports will otherwise be written under its source tree and will no longer match the delivered SHA256SUMS inventory.

Legacy-format reports do not contain the newer per-file source map. The helper refuses to pretend otherwise. For modal propagation, use the included actual axiom driver and original successful manifest; the coordinating historical fingerprint review is preserved in the research reports. No clean-environment Lean rebuild was performed as part of packaging, so these portable commands are a reproduction procedure, not a report that a second machine has passed them.

## 4. Expected result and scope

Require a completed successful manifest, matching captured sources and the exact target declaration. Inspect its printed axioms. A timeout, busy lock, changed-source report or skipped target is not success. A helper lemma, semantic framework or conditional reduction cannot be substituted for a principal theorem. Distinguish shallow C inference rules such as Classicism.em from the axioms of their translated derivations. Supporting sources can intentionally contain unverified work; the accepted declaration and successful manifest determine scope.

Repository validation is independent: install the source project's small Python requirements if necessary, then run `python3 scripts/pmap.py validate` from `source/`. The package's saved validation log records the packaging run; it is not a Lean certificate.
''')
    text(out / "verify_package.py", VERIFY)
    text(out / "reproduce_certificate.py", REPRODUCE)

    # Original links are preserved, not silently rewritten. All new reader navigation must resolve.
    unresolved, new_missing = [], []
    for p in out.rglob("*.md"):
        if "dependencies" in p.relative_to(out).parts:
            continue
        for target in re.findall(r"\]\(([^)\n]+)\)", p.read_text(errors="replace")):
            target = target.strip("<>").split("#", 1)[0]
            if not target or "://" in target or target.startswith(("mailto:", "data:")):
                continue
            if not (p.parent / target).exists():
                row = {"source": p.relative_to(out).as_posix(), "target_as_written": target}
                unresolved.append(row)
                if p.parent == out:
                    new_missing.append(row)
    # These release reports are written immediately below; not broken reader links.
    planned = {"PROVENANCE.json", "SOURCE-MANIFEST.json", "LINK-AUDIT.json"}
    new_missing = [e for e in new_missing if e["target_as_written"] not in planned]
    if new_missing:
        raise RuntimeError(f"Broken new release links: {new_missing}")
    dump(out / "LINK-AUDIT.json", {"new_release_navigation_missing": new_missing,
         "historical_unresolved_links": [e for e in unresolved if e["source"].startswith("source/")],
         "note": "Original notes and absolute temporary paths were preserved byte for byte; no guessed replacement is treated as the original source."})
    validation = subprocess.run([args.python, "scripts/pmap.py", "validate"], cwd=out / "source", capture_output=True, text=True)
    text(out / "REPOSITORY-VALIDATION.log", validation.stdout + validation.stderr)
    if validation.returncode:
        raise RuntimeError("Snapshot repository validation failed; inspect saved log")
    git = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=ROOT, capture_output=True, text=True)
    git_info = {"repository_root": git.stdout.strip() if git.returncode == 0 else None}
    if git.returncode == 0:
        git_info["head"] = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
        git_info["note"] = "File hashes, not a Git commit alone, identify this possibly modified workspace snapshot."
    dump(out / "PROVENANCE.json", {"release_id": spec["release_id"], "captured_at_utc": captured,
         "original_workspace": str(ROOT), "git": git_info, "scope": spec["description"],
         "included": ["All selected original research prose, Lean sources, metadata and logs", "Classicism records, definitions and validation scripts", "Selected exact external source dependencies and licenses", "Final compiled Max-Atomicity author archive"],
         "not_included": ["Full external Lean/Mathlib distributions and binary caches", "Reference PDFs except the locally catalogued counterexample required by repository validation", "One superseded partial-background archive", "Unrelated projects, private memory or chat histories"],
         "excluded_source_artifacts": excluded, "new_lean_compilation": False,
         "source_records_edited": False, "registry_snapshot_generated_at_utc": original.get("generated_at_utc"),
         "validation_exit_code": validation.returncode,
         "historical_unresolved_link_count": len([e for e in unresolved if e["source"].startswith("source/")])})
    dump(out / "SOURCE-MANIFEST.json", {"captured_at_utc": captured, "files": copied})
    payload = []
    for p in sorted(out.rglob("*")):
        if p.is_file():
            payload.append(f"{digest(p)}  {p.relative_to(out).as_posix()}")
    text(out / "SHA256SUMS", "\n".join(payload))
    verified = subprocess.run([sys.executable, str(out / "verify_package.py")], capture_output=True, text=True)
    if verified.returncode:
        raise RuntimeError(verified.stdout + verified.stderr)
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6, allowZip64=True) as z:
        for p in sorted(out.rglob("*")):
            if p.is_file():
                z.write(p, (Path(out.name) / p.relative_to(out)).as_posix())
    zipped = subprocess.run([sys.executable, str(out / "verify_package.py"), "--archive", str(archive)], capture_output=True, text=True)
    if zipped.returncode:
        raise RuntimeError(zipped.stdout + zipped.stderr)
    archive_sha = digest(archive)
    text(Path(str(archive) + ".sha256"), archive_sha + "  " + archive.name)
    print(json.dumps({"archive": str(archive), "archive_bytes": archive.stat().st_size,
          "sha256": archive_sha, "files": len(payload) + 1, "curated_result_groups": len(spec["results"]),
          "original_keys": len(catalog), "manifest_audits": len(audits),
          "source_map_mismatches": sum(len(e["missing_or_changed"]) for e in audits),
          "external_source_variants": len(external), "directory_verified": json.loads(verified.stdout),
          "archive_verified": json.loads(zipped.stdout)}, indent=2))


if __name__ == "__main__":
    main()
