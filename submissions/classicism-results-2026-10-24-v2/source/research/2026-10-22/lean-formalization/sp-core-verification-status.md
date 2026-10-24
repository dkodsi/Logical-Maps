# SP core verification delivery

Both retained targets, **SignatureSplit** and **MaxConservativity**, and the new complete public-declaration audit **pass**. Verified at 2026-10-23T04:52:29.498790+00:00 through the shared globally locked runner. The completed [manifest](checks/20261023T044759304508Z-f503b46f.json) records a 72-module source closure; every captured source hash was independently compared with the live file after the run and still matched. No further proof-source edit was necessary after the two prepared repairs.

## Signature splitting: exact delivered result

For any admitted signature, signature Max derives `¬Atom(Fregean ∧ oneIndividual)`. The stronger explicit-constant theorem accepts any closed relational constant, with no finite-signature restriction. The two C-consistency side conditions are proved using constructed full extensional interpretations with one individual and all relational constants respectively top or bottom. No splitter or consistency witness is supplied as a new hypothesis.

Principal declarations in `Classicism.Meta.Research.StrongPossibilityConsequences.SignatureSplit`:
- `positive_cell_consistent` and `negative_cell_consistent`;
- `maximalist_not_atom_cell_at` and `maximalist_not_atom_cell`;
- `maximalist_add_atom_inconsistent`.

Full prose: [signature comparison, §3](../notes/audit-signature-to-pure-sp-20261022.md) and [profile audit, §6.2](../notes/audit-profile-20261022.md). The implementation uses the splitter `c=top`, whose two consistency models directly establish its truth and falsity. This module does not construct the separate pure-profile Max+Atom model, so it alone does not certify the complete pure-SP/signature-SP incompatibility claim. It establishes no consistency result for Strong Possibility.

## Max conservativity: exact delivered result

For any signature and axiom set Ax, **assuming Con(Max)**:

`C+Ax is conservative over C for closed typed identities ↔ Con(Max∪Ax)`.

The consistency-to-conservativity direction needs only Con(Max∪Ax). The converse retains Con(Max) and constructs the finite-support argument from a hypothetical contradiction with Max∪Ax. It does not assume that target consistency. Finite Max conjunctions have the required reflection property; the proof uses that property to obtain the closed identity, preserving the restriction on necessitating optional assumptions.

Principal declarations in `Classicism.Meta.Research.StrongPossibilityConsequences.MaxConservativity`:
- `identity_conservative_of_max_consistent`;
- `max_consistent_of_identity_conservative`;
- `identity_conservative_iff_max_consistent`.

Full prose: [Max degree, §11](../notes/max-degree.md) and [theory-space comparison, §9](../notes/theory-space-comparison.md). The formal result is stated for the fixed signature's closed typed identities; the pure case is obtained by using the empty signature. Con(Max) remains an explicit premise.

## Statement, type and axiom evidence

[StrongPossibilityConsequencesCoreAxioms.lean](StrongPossibilityConsequencesCoreAxioms.lean) prints exact statements and axiom closures for **all 21 public theorem/generated-derivation declarations** in the two modules. The saved [public audit log](logs/runs/20261023T044759304508Z-f503b46f/StrongPossibilityConsequencesCoreAxioms.log) has no `sorryAx` or added proof axioms. The semantic/syntactic metatheorems use only subsets of `propext`, `Classical.choice`, and `Quot.sound`. The shallow C lemma `Conservativity.reflected_neg_box` uses `propext` and the standing `Classicism.em`; it passes the Classicism gate and type checker and is translated into an actual C⁻ derivation. Its `.derivable` proof depends only on `propext` and `Quot.sound` in the metatheory. These are distinct checks; ordinary semantic metatheory is not being presented as a substitute for an object-language derivation.

Exact target source hashes:

| File | SHA-256 |
| --- | --- |
| `StrongPossibilityConsequencesSignatureSplit.lean` | `1c95fc88dffdc5809ea02b43b498ddf4dac4e2b861f17647e242d978702096e9` |
| `StrongPossibilityConsequencesMaxConservativity.lean` | `42f87ab0c6b3fe3e70801fd5761d17f4a9e1ec5a9f55802782f1420067b773fe` |
| `StrongPossibilityConsequencesCoreAxioms.lean` | `de2f752e87be1da1f43e1e794ed610790536b7897ea1b7db5a28975d06c73ff3` |

The manifest contains dependency fingerprints and compiled artifact hashes. [Machine-readable delivery](verification-updates/core_integration.json) includes all 21 named axiom reports, exact scope, target fingerprints, source hashes and remaining boundaries.

## Corrections and contribution

The final SignatureSplit repair makes the singleton individual domain's Unit subsingleton instance explicit. The final MaxConservativity repair exposes list membership in `FiniteChoiceBasis.ofList` before its filter proof. Both preserved the existing theorem statements and mathematical assumptions. Earlier repairs implemented explicit typed transports, theorem-theory arguments and syntactic substitution simplification; no accepted Schemas or Reflection proof was changed in this final run.

Schemas' earlier successful check remains historical evidence in `checks/20261023T040926613001Z.json`; it was not a target of this batch. Reflection was reused as a source dependency and successfully recompiled in this current manifest. UniversalCore and Disjunction remain with their separate owner. Other SP modules retain their author's ledger; this note does not assert aggregate family completion.

The core also repaired the shared pinned-library import overlay and verified it with ten runner regressions and a real Lean import test. See [shared import repair and rollout notice](shared-import-overlay-repair.md), particularly the instruction for invocations that loaded the old runner before waiting on the lock.

## Reproduction

From the bundle root:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py --lock-wait 300 --keep-going --timeout 240 research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSignatureSplit.lean research/2026-10-22/lean-formalization/StrongPossibilityConsequencesMaxConservativity.lean research/2026-10-22/lean-formalization/StrongPossibilityConsequencesCoreAxioms.lean
python3 scripts/pmap.py validate
```

Database validation passes: 132 principles, 447 results, 162 models. No database proof status or generated Statements file was edited. There is no unresolved bridge in the two exact delivered statements. The broader boundaries above remain explicit.
