#!/usr/bin/env python3
"""Join existing research evidence without changing mathematical or Lean status.

Run from the bundle root. This indexes files; it does not run Lean, reinterpret
compiler evidence, count independent theorems, or edit the source records.
"""

from __future__ import annotations

import hashlib
import json
import os
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RESEARCH = ROOT / "research/2026-10-22"
OUT = Path(__file__).resolve().parent
REGISTRY = RESEARCH / "lean-formalization/coverage-and-ownership.json"

ENTRYPOINTS = {
    "historical_overview": "research/2026-10-22/README.md",
    "thematic_catalog": "research/2026-10-22/RESULT-CATALOG.md",
    "historical_count_and_chat_summaries": "research/2026-10-22/COUNT-AUDIT.md",
    "historical_synthesis_handoff": "research/2026-10-22/SYNTHESIS-HANDOFF.md",
    "followup_and_refinement_inventory": "research/2026-10-22/lean-formalization/INVENTORY.md",
    "coverage_and_ownership": "research/2026-10-22/lean-formalization/coverage-and-ownership.json",
    "current_integration_status": "research/2026-10-22/lean-formalization/integration-status.md",
    "significance_assessment": "research/2026-10-22/lean-formalization/significant-results.json",
    "coordination": "research/2026-10-22/lean-formalization/COORDINATION.md",
    "current_verification_queue": "research/2026-10-22/lean-formalization/verification-queue.json",
    "verification_protocol": "research/2026-10-22/lean-formalization/VERIFICATION-PROTOCOL.md",
    "frozen_original_note_archive": "research/2026-10-22/archive-manifest.json",
}

CORRECTIONS = [
    {
        "issue": "Old/new Boolean Completeness verdict",
        "scope": "rigidity.31 and every use of the old/new model",
        "paths": [
            "research/2026-10-22/notes/old-new-boolean-completeness-source-caveat.md",
            "research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md",
        ],
        "qualification": "The corrected proof supersedes the earlier BC-failure argument at E; the original database record is preserved.",
    },
    {
        "issue": "Finite Choice hierarchy negative results",
        "scope": "Strictness and nonfinite axiomatizability",
        "paths": ["research/2026-10-22/lean-formalization/finite-choice-negative-audit.md"],
        "qualification": "Fresh-column and finite-support lemmas do not supply the full C separation model.",
    },
    {
        "issue": "Max plus Atomicity verification boundary",
        "scope": "Maximalism and principal negative claims",
        "paths": ["research/2026-10-22/lean-formalization/max-lean-verification-status.md"],
        "qualification": "Use the exact current bridge and certificate status; a conditional reduction is not the completed inconsistency proof.",
    },
    {
        "issue": "Central question signature scope",
        "scope": "Negative central-question rows and subsequent gluing arguments",
        "paths": [
            "research/2026-10-22/central-questions-audit.md",
            "research/2026-10-22/followup/central-map.md",
        ],
        "qualification": "Preserve the signature assumptions of each individual construction.",
    },
]


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def read_stable(path: Path) -> bytes:
    before = path.stat()
    data = path.read_bytes()
    after = path.stat()
    if (before.st_mtime_ns, before.st_size) != (after.st_mtime_ns, after.st_size):
        raise RuntimeError(f"Source changed while indexing; rerun: {rel(path)}")
    return data


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def mdlink(path: str, label: str | None = None) -> str:
    target = os.path.relpath(ROOT / path, OUT)
    return f"[{label or Path(path).name}](<{target}>)"


def atomic_write(path: Path, data: str) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(data, encoding="utf-8")
    temporary.replace(path)


def inventory_paths() -> dict[Path, str]:
    paths = {path: "research_prose_inventory" for path in RESEARCH.rglob("*.md")
             if OUT not in path.parents}
    paths.update({path: "lean_library_inventory" for path in
                  (ROOT / "topics/classicism/lean/Classicism").rglob("*.lean")})
    paths[ROOT / "topics/classicism/lean/Classicism.lean"] = "lean_library_inventory"
    paths.update({path: "research_lean_driver_inventory" for path in
                  (RESEARCH / "lean-formalization").rglob("*.lean")})
    paths.update({path: "current_lane_verification_update" for path in
                  (RESEARCH / "lean-formalization/verification-updates").glob("*.json")})
    synthesis = OUT / "DELIVERY-SYNTHESIS.md"
    if synthesis.is_file():
        paths[synthesis] = "editorial_delivery_synthesis"
    return paths


def main() -> None:
    registry_bytes = read_stable(REGISTRY)
    registry = json.loads(registry_bytes)
    inventory = inventory_paths()
    rows = registry["families"] + registry["additional_families"]
    ids = [row["queue_id"] for row in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate coverage keys")

    crosswalk = {}
    for item in registry["catalog_crosswalk"]:
        for key in item["coverage_references"]:
            crosswalk.setdefault(key, []).append(item)

    files = {}

    def file_entry(path_string: str, role: str) -> str:
        path = ROOT / path_string
        if not path.is_file():
            raise FileNotFoundError(path_string)
        if path_string not in files:
            data = read_stable(path)
            files[path_string] = {
                "path": path_string,
                "sha256": digest(data),
                "bytes": len(data),
                "roles": [],
                "result_keys": [],
            }
        if role not in files[path_string]["roles"]:
            files[path_string]["roles"].append(role)
        return path_string

    for role, path in ENTRYPOINTS.items():
        file_entry(path, role)
    for correction in CORRECTIONS:
        for path in correction["paths"]:
            file_entry(path, "correction_or_scope_boundary")

    # Preserve live lane reports as reported evidence, not automatic family
    # promotions. The coverage registry remains the per-result authority.
    lane_updates = {}
    for update_path in sorted((RESEARCH / "lean-formalization/verification-updates").glob("*.json")):
        update_bytes = read_stable(update_path)
        update = json.loads(update_bytes)
        update_rel = file_entry(rel(update_path), "current_lane_verification_update")
        if files[update_rel]["sha256"] != digest(update_bytes):
            raise RuntimeError(f"Lane update changed while indexing; rerun: {update_rel}")
        references = []

        def add_reference(value):
            if isinstance(value, dict):
                for child in value.values():
                    add_reference(child)
            elif isinstance(value, list):
                for child in value:
                    add_reference(child)
            elif isinstance(value, str):
                candidate = next((base / value for base in
                                  (ROOT, RESEARCH / "lean-formalization", update_path.parent)
                                  if (base / value).is_file()), None)
                if candidate is None:
                    references.append({"reported_reference": value, "resolved_path": None})
                elif ROOT in candidate.resolve().parents:
                    path = file_entry(rel(candidate.resolve()), "lane_report_evidence_reference")
                    references.append({"reported_reference": value, "resolved_path": path})

        for field in ("manifest", "accepted_manifests", "prose_proof", "contribution_summary",
                      "evidence_ledger", "status_document", "handoff_manifest"):
            add_reference(update.get(field))
        lane_updates[update.get("lane", update_path.stem)] = {
            "path": update_rel,
            "sha256_at_collection": digest(update_bytes),
            "reported_update": update,
            "resolved_references": references,
            "evidence_limit": "Author-reported workflow and check evidence; not independently recertified or propagated to every family by this index.",
        }

    archive = json.loads(read_stable(ROOT / ENTRYPOINTS["frozen_original_note_archive"]))
    preservation = {"archive_manifest": ENTRYPOINTS["frozen_original_note_archive"],
                    "checked_note_files": len(archive["files"]), "missing": [], "changed": []}
    for item in archive["files"]:
        path = RESEARCH / "notes" / item["file"]
        if not path.is_file():
            preservation["missing"].append(rel(path))
        elif digest(read_stable(path)) != item["sha256"]:
            preservation["changed"].append(rel(path))
    preservation["all_original_note_hashes_match"] = not (preservation["missing"] or preservation["changed"])

    entries = []
    for row in rows:
        key = row["queue_id"]
        prose = list(dict.fromkeys([row["source_index"], *row.get("source_paths", [])]))
        for path in prose:
            file_entry(path, "result_prose_or_inventory")
            files[path]["result_keys"].append(key)

        modules = []
        for name in row.get("lean_modules", []):
            evidence = registry["module_evidence"].get(name, {})
            path = evidence.get("path", "topics/classicism/lean/" + name.replace(".", "/") + ".lean")
            file_entry(path, "mapped_lean_source")
            files[path]["result_keys"].append(key)
            modules.append({
                "module": name,
                "path": path,
                "sha256_at_collection": files[path]["sha256"],
                "reported_role": row.get("module_role"),
                "registry_evidence": evidence,
                "source_matches_registry_snapshot": (
                    files[path]["sha256"] == evidence["source_sha256_at_audit"]
                    if evidence.get("source_sha256_at_audit") else None
                ),
            })
            check = evidence.get("last_recorded_check") or {}
            if check.get("manifest"):
                file_entry(check["manifest"], "referenced_compiler_manifest")

        entries.append({
            "id": key,
            "origin": row["origin"],
            "statement_or_contribution_as_recorded": row["source_entry"],
            "natural_language_sources": prose,
            "source_qualifications": {
                field: row[field] for field in
                ("mathematical_status", "source_location_note", "note", "source_route") if field in row
            },
            "related_catalog_summaries": crosswalk.get(key, []),
            "lean": {
                "registry_category": row["evidence_category"],
                "modules": modules,
                "exact_registry_verification_evidence": row.get("lean_verification_evidence"),
                "implemented_scope": row.get("implemented_scope"),
                "principal_declarations_reported": row.get("main_source_declarations", []),
                "remaining_exact_main_obligation": row.get("remaining_exact_main_obligation"),
                "verification_authority": "Current compiler manifest with matching source/dependency fingerprints and exact main theorem coverage; never this generated index alone.",
            },
            "ownership": row["ownership"],
            "current_lane_evidence": lane_updates.get(row["ownership"].get("repair_queue_lane"), {}).get("path"),
            "innovation_summary_status": "Original contribution descriptions collected; final explanatory synthesis and literature novelty assessment remain separate.",
            "curation_status": "Exact canonical prose section and principal Lean declaration still require per-result reconciliation; module association alone is not that reconciliation.",
        })

    # Include every proof note and Lean source by reference. Unmapped files are
    # retained rather than silently omitted or counted as additional results.
    for path, role in sorted(inventory.items()):
        file_entry(rel(path), role)

    for item in files.values():
        item["result_keys"] = sorted(set(item["result_keys"]))
    identical = {}
    for path, item in files.items():
        identical.setdefault(item["sha256"], []).append(path)

    generated = datetime.now(timezone.utc).isoformat()
    index = {
        "schema_version": 1,
        "generated_at_utc": generated,
        "purpose": "Collection spine for results, prose proofs, Lean sources, evidence and contribution summaries; not a completed edited compendium.",
        "registry_snapshot": {
            "path": rel(REGISTRY), "sha256": digest(registry_bytes),
            "audit_time_utc": registry.get("audit_time_utc"),
            "implementation_updated_at_utc": registry.get("implementation_updated_at_utc"),
            "verification_updated_at_utc": registry.get("verification_updated_at_utc"),
        },
        "scope": {
            "primary_keys": len(registry["families"]),
            "supplemental_keys": len(registry["additional_families"]),
            "thematic_catalog_rows": len(registry["catalog_crosswalk"]),
            "indexed_files": len(files),
            "count_limit": "Inventory keys, broad catalog groups, source files and independent results are different units; do not add these counts.",
            "current_assignment": "Prepare existing research for delivery. New formalizations, supporting lemmas, repairs and complete model certificates for existing results remain authorized. No new open-conjecture research, explicitly including Strong Possibility consistency.",
        },
        "entrypoints": ENTRYPOINTS,
        "corrections_and_boundaries": CORRECTIONS,
        "entries": entries,
        "current_lane_verification_updates": lane_updates,
        "original_note_preservation": preservation,
        "delivery_synthesis": {
            "path": rel(OUT / "DELIVERY-SYNTHESIS.md"),
            "present_at_collection": (OUT / "DELIVERY-SYNTHESIS.md").is_file(),
            "note": "Prepared by the existing synthesis task; may arrive after this snapshot. Its prose does not independently certify mathematical or Lean claims.",
        },
        "catalog_crosswalk": registry["catalog_crosswalk"],
        "files": files,
        "identical_content_groups": [paths for paths in identical.values() if len(paths) > 1],
        "release_obligations": [
            "Reconcile every exact theorem/model statement with its latest full prose proof and corrections.",
            "Map each principal claim to exact Lean declarations and reproducible current source/dependency certificates.",
            "Distinguish session discoveries, simpler definitions/proofs, extensions of earlier work and literature novelty unassessed.",
            "Deduplicate results mathematically without deleting original notes or treating file identity as theorem identity.",
            "Retain open questions, failed arguments and conditional results with their exact scope.",
            "Do not initiate new open-conjecture research while preparing this delivery; preserve unresolved questions in the appendix.",
            "Refresh this collection and freeze a reproducible source bundle only when the release is ready.",
        ],
    }
    if read_stable(REGISTRY) != registry_bytes:
        raise RuntimeError("Coverage registry changed during generation; rerun")
    if inventory_paths() != inventory:
        raise RuntimeError("Research source inventory changed during generation; rerun")

    lines = [
        "# Classicism result and proof index", "",
        "This index joins the tracked research contributions to their prose and Lean sources. "
        "Statements and status labels are preserved from the coverage registry. "
        "It is a collection aid, not a fresh mathematical audit or Lean certificate.", "",
        f"Generated {generated}. The {len(entries)} entries preserve "
        f"{len(registry['families'])} primary keys and {len(registry['additional_families'])} "
        "supplemental keys. They are not an independent theorem count.", "",
        "The current assignment is delivery of existing research, including new formalizations and repairs of existing results. "
        "New open-conjecture research, explicitly Strong Possibility consistency, is outside this phase. "
        "Exact evidence and source hashes are in [results.json](results.json).", "",
        "## Current lane evidence", "",
        "These are current author reports, separate from the per-result registry statuses below. "
        "A passing helper or a lane workflow state does not certify all of its assigned results.", "",
        "| Lane | Reported workflow state | Evidence |", "|---|---|---|",
    ]
    for name, item in lane_updates.items():
        lines.append("| " + name.replace("_", " ") + " | " +
                     str(item["reported_update"].get("state", "unspecified")).replace("_", " ") +
                     " | " + mdlink(item["path"], "current report") + " |")
    lines += ["", "Original-note preservation: " +
              (f"all {preservation['checked_note_files']} archived note hashes match."
               if preservation["all_original_note_hashes_match"] else
               "archive differences require review; see results.json.") + "", ""]
    for entry in entries:
        lines += ["## " + entry["id"].replace(".", " ").replace("_", " "), "",
                  entry["statement_or_contribution_as_recorded"], "",
                  "Prose: " + "; ".join(mdlink(p) for p in entry["natural_language_sources"]) + ".", ""]
        modules = entry["lean"]["modules"]
        lines += ["Lean: " + ("; ".join(mdlink(m["path"], m["module"]) for m in modules)
                                  if modules else "No mapped module in the coverage registry") + ".", "",
                  "Registry status: " + entry["lean"]["registry_category"].replace("_", " ") + ".", ""]
        if entry["lean"]["remaining_exact_main_obligation"]:
            lines += ["Remaining obligation: " + entry["lean"]["remaining_exact_main_obligation"], ""]
        if entry["current_lane_evidence"]:
            lines += ["Current lane evidence: " + mdlink(entry["current_lane_evidence"], "author update") +
                      " (does not automatically change this family's registry status).", ""]
    atomic_write(OUT / "results.json", json.dumps(index, ensure_ascii=False, indent=2) + "\n")
    atomic_write(OUT / "RESULTS.md", "\n".join(lines))
    print(json.dumps({"entries": len(entries), "files": len(files), "all_referenced_files_exist": True,
                      "outputs": [rel(OUT / "results.json"), rel(OUT / "RESULTS.md")]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
