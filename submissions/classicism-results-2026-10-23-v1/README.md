# Classicism results and Lean certificate evidence

Release **classicism-results-2026-10-23-v1**, captured **2026-10-23T12:40:20.509353+00:00**.

This is a shareable, hashed snapshot for the database owners. It combines the original research, database context, Lean proof sources, saved compiler manifests and axiom reports, and the final author checkpoints. **It does not change or automatically import any database verdict.**

Start with [Main results and Lean status](MAIN-RESULTS.md), then the [160-key catalog](CATALOG.md). The machine-readable counterparts are [MAIN-RESULTS.json](MAIN-RESULTS.json) and [CATALOG.json](CATALOG.json). [Database handoff](DATABASE-HANDOFF.md) explains attribution, corrections and import boundaries.

## Traceability

- `source/` preserves original repository-relative paths and original bytes, including historical notes and failed-check reports. Such reports are evidence of chronology, not accepted certificates.
- [CERTIFICATE-AUDIT.json](CERTIFICATE-AUDIT.json) records the selected compiler reports and freshly compared source hashes. It distinguishes later source-map manifests from legacy reports.
- [LANE-CHECKPOINTS.json](LANE-CHECKPOINTS.json) contains the final inspected author reports, including unfinished work.
- [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) maps preserved files to original paths and content hashes. [PROVENANCE.json](PROVENANCE.json) records the collection boundary and exclusions.
- `SHA256SUMS` hashes every other archive file, including the inventories. Run `python3 verify_package.py` after extraction, or `python3 verify_package.py --archive ../classicism-results-2026-10-23-v1.zip` to check the archive directly.

## Lean evidence and reproduction

The package contains source proofs and recorded successful checks, with their exact limitations. The existing complete Max–Atomicity author archive, including its local compiled artifacts, is retained at its original relative path under `source/research/2026-10-22/lean-formalization/`. Its older partial-background archive is excluded as redundant and identified by hash in PROVENANCE.

Lean **4.33.1**, the exact Mathlib commit and all dependency revisions are pinned in the preserved `lean-toolchain` and `lake-manifest.json`. The exact available third-party source subset referenced by selected reports is included with licenses. **The complete external Lean/Mathlib installation and its platform-specific binary caches are not bundled.** [Reproducing checks](REPRODUCING.md) documents installation prerequisites, the portable relocation helper and the serial compiler protocol.

No Lean compiler was run for this packaging operation. Source-hash verification establishes correspondence to saved evidence, not a new kernel check. Legacy manifests without per-file maps are explicitly identified; their saved axiom logs and coordinating review remain available.

## Reading older material

Use MAIN-RESULTS for delivery status. The original consolidation index predates some final checks; the earlier synthesis's open/conditional Max–Atomicity wording is superseded by the final certificate. [Release notes](RELEASE-NOTES.md) list these changes. Original absolute `/tmp` paths and older broken note links are preserved for provenance; [LINK-AUDIT.json](LINK-AUDIT.json) inventories them. All new release navigation is checked against the actual package.

This release makes no literature-novelty claim and does not equate supporting Lean modules with fully formalized headline theorems. The user-selected working package remains Classicism + necessary Functional Choice + quantified Infinity at every admitted type.
