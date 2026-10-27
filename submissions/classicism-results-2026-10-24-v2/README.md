# Classicism: results, proofs and certificates — 24 October 2026 (v2)

[Cumulative integration register](../integration-register/README.md) · [25 October update](../next-update/README.md) · [Changes since this post and database integration guide](../next-update/DATABASE-HANDOFF.md).

Research submission for review by the Logical Maps database owners. Start with [Main Results](MAIN-RESULTS.md):

- [I. Resolved database questions and connections](MAIN-RESULTS.md#database-connections)
- [II. Further results about established principles](MAIN-RESULTS.md#established-principles)
- [III. Extensions and new directions](MAIN-RESULTS.md#extensions-and-new-directions)

## Guides and evidence

- [Previously known results formalized](MAIN-RESULTS.md#previously-known-results-formalized): attribution and certified scope.
- [Conjectures](CONJECTURES.md): unresolved questions, claims awaiting review, and resolved questions with contribution and attribution distinguished.
- [Logical observers](LOGICAL-OBSERVERS.md): the C and H maps, uniform definitions, simplifications and intuition; [full connection catalogue](proofs/h-observer-space/SUMMARY.md).
- [Candidates_DK](CANDIDATES_DK.md): proposed principles and equivalent formulations.
- [Full result index](evidence/RESULT-INDEX.md) and [catalogue](CATALOG.md): detailed statements, proofs and certificates.
- [Database integration](DATABASE-INTEGRATION.md) and [review guide](DATABASE-HANDOFF.md).
- [Reproduction instructions](REPRODUCING.md), [certificate index](evidence/CERTIFICATES.json) and [source provenance](SOURCE-MANIFEST.json).
- [Comparing Extensions of Classicism](papers/comparing-extensions-of-classicism.tex) and [Logical Observers and the Structure of Propositions](papers/logical-observers-and-the-structure-of-propositions.tex): companion papers.

Run `python3 verify_package.py` to verify the delivered files and `python3 certificate_sources.py` to check certificate sources and principal logs. Neither command invokes Lean. The source files and saved checks carry the exact certification scope; remaining obligations are stated in the result index.

The summary views, observer guide and observer-principle reference section are generated from the JSON records by `render_results.py`. Run `python3 render_results.py --check` to detect drift. [Proof-length ratings](MAIN-RESULTS.md#proof-length) describe selected mathematical exposition.

The package includes source proofs and successful certificate evidence. Machine-specific locations and research coordination metadata are omitted from the publication copy; original receipt hashes retain provenance. Full toolchains, compiled caches and superseded compiler diagnostics are not included. [Omission summary](ARCHIVED-ARTIFACTS.json).
