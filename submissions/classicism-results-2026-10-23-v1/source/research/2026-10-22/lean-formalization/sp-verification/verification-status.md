# SP/Max verification status

Snapshot: 2026-10-23T04:51:22.336418+00:00. **12 of 12 modules have successful saved Lean checks matching current sources and dependencies.**

The 23 October user request explicitly resumes verification and delegates work. The SP author used an isolated compiler cache and report directory; the core integration task retained its separate cache. No YAML certificate status was changed.

| Module (common StrongPossibilityConsequences prefix omitted) | Latest check | Evidence |
| --- | --- | --- |
| Algebra | passed | [Saved check](../sp-verification/logs/runs/20261023T040940460714Z/StrongPossibilityConsequencesAlgebra.log) |
| C | passed | [Saved check](../logs/runs/20261023T044759304508Z-f503b46f/StrongPossibilityConsequencesC.log) |
| Computability | passed | [Saved check](../sp-verification/logs/runs/20261023T041012326835Z/StrongPossibilityConsequencesComputability.log) |
| Disjunction | passed | [Saved check](../sp-universal-verification/logs/runs/20261023T044336274999Z-6b5c1cb4/StrongPossibilityConsequencesDisjunction.log) |
| InfinitaryNumerals | passed | [Saved check](../sp-verification/logs/runs/20261023T040821574277Z/StrongPossibilityConsequencesInfinitaryNumerals.log) |
| MaxConservativity | passed | [Saved check](../logs/runs/20261023T044759304508Z-f503b46f/StrongPossibilityConsequencesMaxConservativity.log) |
| MaxDiagram | passed | [Saved check](../logs/runs/20261023T044759304508Z-f503b46f/StrongPossibilityConsequencesMaxDiagram.log) |
| Reflection | passed | [Saved check](../logs/runs/20261023T044759304508Z-f503b46f/StrongPossibilityConsequencesReflection.log) |
| Schemas | passed | [Saved check](../logs/runs/20261023T040926613001Z/StrongPossibilityConsequencesSchemas.log) |
| SignatureSplit | passed | [Saved check](../logs/runs/20261023T044759304508Z-f503b46f/StrongPossibilityConsequencesSignatureSplit.log) |
| Stability | passed | [Saved check](../logs/runs/20261023T044759304508Z-f503b46f/StrongPossibilityConsequencesStability.log) |
| UniversalCore | passed | [Saved check](../sp-universal-verification/logs/runs/20261023T043010003441Z-33fa960f/StrongPossibilityConsequencesUniversalCore.log) |
| CoreAxioms (additional audit; outside the twelve-module count) | passed | [Saved check](../logs/runs/20261023T044759304508Z-f503b46f/StrongPossibilityConsequencesCoreAxioms.log) |

## Work completed in this verification run

- InfinitaryNumerals passed unchanged. Its enlarged syntax and comprehension assumptions remain explicit.
- Algebra passed after replacing an incorrect distributivity lemma name. Its 14 theorem/equivalence axiom reports were inspected.
- Computability passed after narrowing the import to the required RE module and compiling 11 missing dependencies from the existing pinned Mathlib source. No downloads. All four theorem axiom reports were inspected.
- MaxDiagram passed after replacing two unavailable tactic invocations with the same explicit classical metatheoretic argument. All eight theorem axiom reports were inspected.
- The core integration task repaired Schemas and recorded a successful check. Its proof still retains the required consistency premises.
- The core integration task also repaired Reflection; its current source and dependencies match the successful check. Its finite-proof Max reflection and conditional SP diagram statements retain their exact assumptions.
- The dedicated proof agent repaired UniversalCore and Disjunction. Both pass the locked snapshot runner. The seven UniversalCore and five Disjunction axiom reports contain no sorryAx; the latter criterion retains Con(Max).
- The core task completed SignatureSplit and MaxConservativity, then checked CoreAxioms: all 21 public declaration reports exclude sorryAx. The shallow reflected-negation certificate uses the existing Classicism.em rule; its translated C derivation uses only ordinary Lean metatheoretic axioms. SignatureSplit constructs the two actual singleton models, and MaxConservativity retains Con(Max).

No exported printed axiom report from the four author-verified modules contains sorryAx or an added mathematical axiom. Their ordinary Lean metatheory may use propext, Quot.sound and Classical.choice. For MaxDiagram the conclusions are actual derivations in the existing C calculus. The separate C and Stability modules retain their 39 gate/type/derivation certificates.

## Completed handoffs

The task **Formalize completed Classicism proofs…** (`01a1664d-7c13-7701-b52c-2070ee16eb06`) completed Schemas, Reflection, SignatureSplit and MaxConservativity, plus the 21-declaration CoreAxioms audit. See [its status](../sp-core-verification-status.md). The SP author completed Algebra, Computability, InfinitaryNumerals and MaxDiagram. The dedicated local proof agent completed UniversalCore and Disjunction; its [handoff](../sp-universal-verification/status.md) records their exact source hashes, full public axiom audits and repaired proof steps. C and Stability retain their successful checks. No result-module check remains pending in this twelve-module scope.

## Scope and reproducibility

The shared runner lock is active. Every subsequent compiler invocation uses
that runner, including the isolated wrappers. UniversalCore has passed under
the new snapshot/artifact-integrity protocol; Disjunction has also passed under this protocol. The aggregate collector accepts both historical and new manifests
and independently checks their current transitive input fingerprints. The
author's completed source checks are not needlessly rerun during other owners'
repair loops.

These checks do not prove SP consistency, Con(Max + G + D not G), a genuine Henkin quotient, the full pure/signature incompatibility, or an effective degree classification. The [AI scope audit](semantic-audit.md) and [family inventory](../sp-family-status.md) retain those distinctions.

The companion [JSON ledger](verification-status.json) records source SHA-256 values, compiler identity, source/dependency fingerprints, and exact archived check paths. Timestamped manifests preserve failed attempts as well as successful ones. The isolated runner delegates to the existing checker with an independent cache; its Mathlib source subset and pinned inputs are recorded alongside it. The [prose proofs](proof-summary.md), [reproduction instructions](reproduction.md) and [contribution summary](contribution-summary.md) explain exact scope and rerun commands for final collection.

Repository validation after the edits: 132 principles, 447 results, 162 models — OK. This is a separate check from Lean compilation.
