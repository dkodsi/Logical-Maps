# Classicism research collection

The collection brings together the research results, full natural-language proofs, Lean sources and explanations of the contributions. The [result and proof index](RESULTS.md) links every tracked research family to its existing sources. The [structured index](results.json) preserves source hashes, ownership, verification evidence references and thematic cross-references.

This is the foundation for the final synthesis. The exact statements, canonical proof versions, principal Lean declarations and innovation summaries still need to be reconciled entry by entry. Original notes and proof files remain in place.

## Current delivery scope

The current assignment is to prepare the existing research for delivery. New Lean formalizations, supporting lemmas, proof repairs and complete model certificates for existing results remain in scope. New investigations of open conjectures are outside this phase, explicitly including research into Strong Possibility consistency. Unresolved questions remain documented with their exact hypotheses; they are not silently converted into delivery tasks or established results.

The collection retains all 160 tracked keys, including conditional and unfinished entries. Retaining an entry does not claim that its proof or formalization is complete. The verification queue controls the remaining implementation work; this collection organizes its evidence and exposition.

The existing synthesis task is preparing `DELIVERY-SYNTHESIS.md` in this directory. It may arrive after the current index snapshot; the builder includes it when present on the next refresh. That editorial synthesis has a separate owner from the source index.

## Reading routes

| Purpose | Start here |
|---|---|
| Find a result and its prose and Lean sources | [Complete tracked index](RESULTS.md) |
| Read the broad mathematical picture | [Research overview](../README.md) and [thematic catalog](../RESULT-CATALOG.md) |
| Recover the original result accounting and all eight chat summaries | [Count audit](../COUNT-AUDIT.md) |
| Find later investigations and proof refinements | [Followup and refinement inventory](../lean-formalization/INVENTORY.md) |
| Check current formalization progress | [Latest lane updates in the index](RESULTS.md#current-lane-evidence), then their cited compiler manifests; the [integration report](../lean-formalization/integration-status.md) provides historical context |
| Read assessments of mathematical and philosophical significance | [Significance assessment](../lean-formalization/significant-results.json) |
| Find outstanding proof obligations and owners | [Coverage and ownership](../lean-formalization/coverage-and-ownership.json) |
| Find the next check and its repair owner | [Current verification queue](../lean-formalization/verification-queue.json) and [verification protocol](../lean-formalization/VERIFICATION-PROTOCOL.md) |

The earlier [synthesis handoff](../SYNTHESIS-HANDOFF.md) remains useful historical context. Its statements that the research was finished and Lean had not been requested are superseded by the ongoing formalization work. Historical summaries and inventories are not current verification reports.

## The final collection

The finished collection should have five connected parts:

1. **A synthesis of the mathematical contributions.** Explain the organizing ideas, simpler definitions, strengthenings, model constructions and philosophical implications, with precise limits on what follows.
2. **A complete result catalog.** Give each theorem or separation a stable identifier, exact premises and conclusion, type and signature scope, dependencies and status. Preserve cross-references when several formulations belong to one result.
3. **The natural-language proofs.** Select the corrected, complete version of each argument, retaining attribution and links to earlier versions and independent audits.
4. **The Lean development.** Link each principal statement to its actual declaration, source files, assumptions, compiler evidence and reproduction instructions. Include the source and dependencies needed to check the proofs.
5. **Corrections and remaining questions.** Keep incomplete formalizations, conditional results, withdrawn arguments, failed approaches and unresolved conjectures explicit.

Each result needs a short explanation of what it adds: a new result in this project, a stronger theorem, a simpler proof or definition, a new separation, or an interpretation connecting previously distinct parts of the theory. A claim of novelty in the literature requires its own assessment. The significance ranking orders exposition; it does not exclude results from the collection.

## Evidence and corrections

Mathematical proof status, Lean verification status and novelty assessment are separate. An associated Lean file may contain supporting infrastructure rather than the principal theorem. A successful historical check applies to its exact source and dependency fingerprints. The generated index preserves reported evidence without promoting it to a new certificate.

The [corrected old/new argument](../notes/old-new-boolean-completeness-and-rigidity-separation.md) and its [source caveat](../notes/old-new-boolean-completeness-source-caveat.md) must accompany the BC + ND separation: the earlier database BC-failure argument at E is not the current proof. The [finite Choice negative audit](../lean-formalization/finite-choice-negative-audit.md) and [Max verification status](../lean-formalization/max-lean-verification-status.md) identify principal bridges that supporting lemmas alone do not settle. Signature restrictions in the [central-question audit](../central-questions-audit.md) must stay attached to the individual countermodels.

The structured index inventories every research Markdown file and every Lean source in the Classicism library, plus research Lean drivers and separate verification updates from each author. Files not yet assigned to a result remain visible there. Identical files are grouped by hash for navigation; identical content is not a test for mathematical duplication.

The refreshed index copies the coverage registry's exact per-family verification evidence and the latest lane reports separately. A lane's newly checked helper or certificate does not automatically upgrade every result assigned to that lane. Source mismatches, pending model assemblies and remaining interpretation obligations stay visible.

## Concrete delivery work remaining

- **Canonical statements and proofs:** reconcile each key with its exact corrected prose section, including local/boxed assumptions, type and signature restrictions. Preserve the original notes and identify superseded arguments rather than rewriting history.
- **Claim-to-certificate mapping:** identify the principal Lean declarations for each claim, attach finalized compiler manifests and axiom reports, and distinguish complete theorem/model certificates from supporting modules. The OldNew central separator has checked evidence; its separate TR and combined assembly must retain their own check status.
- **Explanatory synthesis:** write the connected account of the main ideas and a short contribution summary for each result. Separate project discoveries, strengthenings and proof simplifications from literature novelty, which has not been systematically established.
- **Reproducible delivery bundle:** freeze a consistent source/dependency snapshot, provide the pinned toolchain and dependency reconstruction instructions, and verify the final manifest and links. The current index is a live collection, not that release archive.
- **Final reconciliation:** incorporate completed author checks, classify remaining existing-result formalization gaps precisely, and place unresolved conjectures in a clearly labeled appendix. Do not delay this editorial reconciliation by starting new conjecture research.

## Refreshing the index

Run from the bundle root:

```sh
python3 research/2026-10-22/consolidation/build_index.py
python3 scripts/pmap.py validate
```

The builder refreshes only `RESULTS.md` and `results.json`. It checks linked files, records their hashes, retains every key from the coverage registry, collects current lane evidence and checks the original note hashes against the archive manifest. It does not invoke Lean, open previews, edit proofs, change database verification flags or produce a frozen release archive. Update the coverage registry when new proof mappings become available, then refresh the index. Existing-result formalization continues, so new or edited files can postdate a generated snapshot; refresh before assembling a release.
