"""Index actual compiler evidence for the Max/Atomicity source family.

This is a read-only evidence audit, not a Lean checker. A successful module
entry counts only when its current local source closure matches the snapshot.
External binary/compiler hashes remain recorded in the original manifest.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]
SOURCE = ROOT / "topics/classicism/lean/Classicism/Results/Research"
PREFIX = "Classicism.Results.Research."
TARGET = PREFIX + "MaxAtomicityInconsistency"
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)")
AXIOMS = re.compile(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", re.S)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(path):
    result = []
    for line in path.read_text().splitlines():
        match = IMPORT.match(line)
        if match:
            result.extend(match.group(1).split("--")[0].split())
    return result


def closure_matches(manifest, module):
    seen = set()
    def visit(name):
        if name in seen:
            return True
        seen.add(name)
        source = manifest.get("sources", {}).get(name)
        if source is None:
            # An external dependency is represented by the manifest's pinned
            # binary hashes rather than by a project source snapshot.
            return not name.startswith("Classicism.")
        path = Path(source["path"])
        if not path.is_file() or digest(path) != source["sha256"]:
            return False
        return all(visit(dep) for dep in imports(path))
    return visit(module)


def run():
    manifests = []
    for path in sorted((BASE / "checks").glob("*.json"), reverse=True):
        try:
            data = json.loads(path.read_text())
        except (ValueError, OSError):
            continue
        if data.get("schema_version") == 2:
            manifests.append((path, data))
    entries = []
    for source in sorted(SOURCE.glob("MaxAtomicity*.lean")):
        module = PREFIX + source.stem
        row = {"module": module, "source": str(source.relative_to(ROOT)),
               "source_sha256": digest(source), "status": "pending"}
        for path, data in manifests:
            entry = next((e for e in data.get("checked", [])
                          if e.get("module") == module), None)
            if entry is None or entry.get("exit_code") != 0:
                continue
            if not closure_matches(data, module):
                continue
            row.update(status="checked_current_source_closure",
                       manifest=str(path.relative_to(ROOT)),
                       fingerprint=entry.get("fingerprint"))
            log = entry.get("log")
            if not log:
                for _, older in manifests:
                    candidate = next((e for e in older.get("checked", [])
                                      if e.get("module") == module
                                      and e.get("fingerprint") == entry.get("fingerprint")
                                      and e.get("exit_code") == 0 and e.get("log")), None)
                    if candidate:
                        log = candidate["log"]
                        break
            if log and (BASE / log).is_file():
                row["log"] = str((BASE / log).relative_to(ROOT))
                text = (BASE / log).read_text()
                reports = {name: [a.strip() for a in axioms.split(",") if a.strip()]
                           for name, axioms in AXIOMS.findall(text)}
                row["printed_axiom_reports"] = reports
                row["reported_nonstandard_axioms"] = sorted({
                    a for axioms in reports.values() for a in axioms
                    if a not in {"propext", "Classical.choice", "Quot.sound"}})
            break
        if row["status"] == "pending":
            for path, data in manifests:
                entry = next((e for e in data.get("checked", [])
                              if e.get("module") == module), None)
                if entry:
                    row["latest_attempt_manifest"] = str(path.relative_to(ROOT))
                    row["latest_attempt"] = entry
                    break
        entries.append(row)
    final = next(row for row in entries if row["module"] == TARGET)
    return {
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "method": "Successful serial compiler entry plus current local source closure hash match; this script performs no Lean compilation.",
        "external_dependencies": "Pinned compiler and precompiled binary hashes are recorded in the linked manifests; this audit does not rehash those external roots.",
        "exact_target": "¬ Classicism.Meta.AxiomSet.Consistent (Classicism.Meta.AxiomSet.maximalist ∪ Classicism.P.AtomicityT.schema)",
        "final_module_checked": final["status"] == "checked_current_source_closure",
        "checked_module_count": sum(row["status"] == "checked_current_source_closure" for row in entries),
        "module_count": len(entries),
        "entries": entries,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")
