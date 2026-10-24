# Classicism research: local draft

The [canonical results package](classicism-results-2026-10-24-v2/README.md) is the entry point for the current synthesis. Release: **24 October 2026 (v2)**.

- [Main results](classicism-results-2026-10-24-v2/MAIN-RESULTS.md): implications, countermodels, representation and translation results, organized by subject.
- [Questions and negative results](classicism-results-2026-10-24-v2/CONJECTURES.md): settled cases, obstructions and remaining obligations.
- [Database integration](classicism-results-2026-10-24-v2/DATABASE-INTEGRATION.md): existing records, proposed actions and exact proof/certificate references.
- [CANDIDATES_DK](classicism-results-2026-10-24-v2/CANDIDATES_DK.md): isolated candidate records and the evaluator hierarchy with exact equivalent formulations.
- [Complete catalog](classicism-results-2026-10-24-v2/CATALOG.md) and [evidence index](classicism-results-2026-10-24-v2/evidence/RESULT-INDEX.md).

Research produced with Codex retains its source attribution. Ordinary proofs, exact Lean certificates, supporting components and unresolved claims remain distinct. The older local collection is retained outside the Git checkout for recovery; its directory now points to this package.

Run `python3 submissions/classicism-results-2026-10-24-v2/render_results.py --check` and `python3 submissions/classicism-results-2026-10-24-v2/verify_package.py` to check generated views and package bytes. The [reproduction guide](classicism-results-2026-10-24-v2/REPRODUCING.md) explains exact certificate targets and prerequisites.

The package’s original release and source snapshot are historical provenance. The branch previously incorporated upstream through commit `d41204299ba1e0853594f13eeaf0d3969b34faf4`; this note is not a claim that the branch is current with upstream today. The live database under `logical-maps/` has separate local integration work, while the package preserves its pinned sources and explicit later evidence.
