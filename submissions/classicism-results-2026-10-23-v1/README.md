# Classicism: results, proofs and certificates

Research submission for the Logical Maps database owners. The collection includes work produced with Codex; each proof retains its attribution, assumptions and limitations. Database verdicts have not been automatically changed or imported.

- **[Results and their significance](MAIN-RESULTS.md):** 26 explicit entries grouped around central implications and separations; Choice, completeness and rigidity; arithmetic and evaluation; world structure and probability; and Strong Possibility and language extensions.
- **[Complete result catalog](CATALOG.md):** all 160 tracked keys, with proof sources and formalization scope. A key can group related claims; it is not necessarily an independent theorem or a complete certificate.
- **[Proof and certificate index](evidence/RESULT-INDEX.md):** exact declarations, saved compiler evidence and outstanding obligations.
- **[Database-owner handoff](DATABASE-HANDOFF.md):** attribution, corrections and integration boundaries.
- **[Reproducing checks](REPRODUCING.md):** pinned dependencies and the portable certificate helper.

The corresponding structured indexes are [MAIN-RESULTS.json](MAIN-RESULTS.json) and [CATALOG.json](CATALOG.json). Written mathematical proofs, supporting Lean lemmas and complete Lean certificates are distinguished throughout. The guide identifies both unresolved mathematical questions and incomplete formalizations.

## Verification and provenance

Run `python3 verify_package.py` to check this directory against `SHA256SUMS`. [CERTIFICATE-AUDIT.json](CERTIFICATE-AUDIT.json) compares the selected saved reports with the supplied source hashes. No new Lean compilation was performed during this presentation cleanup. The included source/dependency subset and reproduction helper remain available; a matching Lean/Mathlib installation is required to compile.

[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) maps retained sources to their original paths and hashes. Mathematical source text and Lean sources are unchanged; recorded edits to original Markdown only repair navigation. Corrections and caveats needed to assess proofs are retained.

## Archived material

The current Git tree omits duplicate snapshots and proof documents, obsolete inventories and work queues, coordination reports, historical compiler attempts, and the nested compiled-certificate ZIP. [ARCHIVED-ARTIFACTS.json](ARCHIVED-ARTIFACTS.json) records every omitted path, hash and recovery location.

The [original release archive](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1) is unchanged and contains the historical material. Its ZIP SHA-256 is `f6366234ebcc8f3fce697129595278d3dd3385c61ded54b9b95aa9d52bca2025`. Extract recovered artifacts into a separate directory. Earlier Git commits also remain reachable; this cleanup does not rewrite published history.
