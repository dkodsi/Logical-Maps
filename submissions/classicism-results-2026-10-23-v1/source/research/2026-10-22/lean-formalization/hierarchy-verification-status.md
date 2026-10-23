# Owned family delivery checkpoint

23 October 2026. This lane is stopped before the hard human cutoff of **01:57 a.m. New York (05:57 UTC)**. Proof repairs ended at the 01:40 checkpoint. All owned compiler sessions have ended and all three child agents are stopped. No active goal or automation was created. Resume only on explicit human instruction.

## Delivered certificates

| Family | Exact delivered scope | Current evidence |
|---|---|---|
| Old/new | A concrete C model with full unboxed ND and BC at the root, failure of IC_et and RC_et, failure of the full TR schema, failure of boxed BC_et, and BC_et failure along every E-to-O arrow. Boxed RP is not included. | [Complete manifest](checks/20261023T045855511121Z-2911dd87.json); [six-declaration axiom audit](logs/runs/20261023T045855511121Z-2911dd87/OldNewCompleteAxioms.log). All 114 captured source hashes still match. |
| Positive Choice hierarchy | For every pure sentence, derivability from C plus full boxed Functional Choice is equivalent to derivability from some single selector stage, and from some single diagonal boxed Choice stage. | [Current complete manifest](checks/20261023T050742277842Z-9dd5be15.json); [hierarchy axiom audit](logs/runs/20261023T050742277842Z-9dd5be15/ChoiceHierarchyAxioms.log). All 72 captured source hashes still match. |
| Retractions | For closed relational type rho, the boxed existential retraction from tower(relEmbeddingBudget rho) follows under exactly C plus plenitudeBase = {boxed Plenitude(t,t)}. The inverse is supplied existentially; no pure inverse term is claimed. | Same current Choice manifest and hierarchy audit. |
| Fresh columns | Explicit fresh-column amalgamation and absence of a finitely supported selector, as external metatheorems. | Same current Choice manifest; [two-declaration helper audit](logs/runs/20261023T050742277842Z-9dd5be15/ChoiceFreshColumnsAxioms.log). |
| Colour-collapse, partial | The actual three-object C model, full boxed BF, and full root TR. Finite extension, root factorization, weak exact-image profiles, and exact-image rigidity are proved. | [Partial manifest](checks/20261023T053543607148Z-fd14d406.json); [seven-declaration audit](logs/runs/20261023T053543607148Z-fd14d406/ColourCollapsePartialAxioms.log). The audit passed; its enclosing batch failed later in Witness. All 86 sources in the passed prefix still match. |
| Colour-collapse witness | The actual coloured unary relation at B is weakly rigid and is not rigid. | [Latest main attempt](checks/20261023T053846469650Z-8a1e058e.json) compiles Witness, then fails in Unary. All 86 sources through Witness still match. Its separate two-declaration axiom audit source is saved, but the check never started because the compiler lock timed out. |

The main OldNew declarations are `Classicism.Meta.Intensional.OldNew.complete_countermodel`, `not_entails_tame`, and `not_entails_box_bc`. TR failure here is schema failure; no particular TR type is asserted to fail.

The main positive Choice declarations are `Classicism.Meta.ChoiceHierarchy.fullChoice_theorem_iff_stage`, `fullChoice_theorem_iff_diagonalStage`, and `realizedRetraction`. The helper declarations are `Classicism.Meta.ChoiceFreshColumns.fresh_amalgam` and `no_finitely_supported_selector`.

The model audits report only `propext`, `Classical.choice`, and `Quot.sound`; the positive Choice audits use only `propext` and `Quot.sound`. None reports `sorryAx`. These are metatheorems about the fixed Classicism object language; these Lean metatheoretic axioms are not added to C.

## Unfinished main certificate and exact resume point

**The colour-collapse RP/WRP separator is not Lean verified.** Its unchanged target is full TR plus full boxed BF plus boxed RP at et, with WRP failure at et. It does not assert full-schema RP.

The latest real main check is [20261023T053846469650Z-8a1e058e](checks/20261023T053846469650Z-8a1e058e.json). Base, Rigidity and Witness pass. The immediate frontier is [the Unary error log](logs/runs/20261023T053846469650Z-8a1e058e/Classicism_Models_ColourCollapseUnary.log):

1. `finite_mem`, lines 49–50: rewrite mismatch between `cat.De.map` and `FunCat.fn`; expose the pointwise equality and use explicit congruence.
2. `extension_finite`, line 70: reduce the identity individual map explicitly.
3. `no_coloured_exception`, lines 183–213: expose the Nat individual domain and concrete colour decisions before arithmetic and numeral elaboration.
4. `rigid_unary_exact`, lines 270 and 279: retain the implicit world binder explicitly when applying `finite_exact` and `top_exact` to `ExactImage`.
5. Then check Subobjects, PowerCore, Formula, Separation, and `ColourCollapseAxioms`. Those downstream modules have no passing certificate from this lane.

No model-proof source edit followed that failed Unary run. The repairs above are the next obligations, not completed work. The current source inventory is in [the delivery manifest](hierarchy-verification-manifest.json), and machine-readable scope/evidence is in [the lane status](verification-updates/hierarchy_oldnew_colourcollapse.json).

The fixed-point entrance remains an unfinished concrete qualitative-link construction with a separately pinned singleton-individual semantics bridge. The negative finite-basis symmetric-forcing/extraction formalization is also unfinished. Neither was reopened during this wrap-up. Positive Choice cofinality does not establish strictness or nonfinite axiomatizability.

## Prose and source repairs

- [Old/new proof](../notes/old-new-boolean-completeness-and-rigidity-separation.md): full BC, corrected future BC failure, ND, IC/RC and schema-level TR separation.
- [Finite Functional Choice](../followup/finite-functional-choice.md): sections 5 and 10 support the positive hierarchy and retractions; section 2 motivates the fresh-column helper. The negative constructions remain separate.
- [Colour-collapse proof](../notes/colour-collapse-entrance.md): sections 1–4 now have the checked concrete category, root rigidity and coloured witness sources. Later classification, lifting and power-separation sources remain pending.

Repairs preserved theorem statements and constructions. OldNewComplete opens the arrow-notation namespace. ColourCollapse explicitly supplies arrow endpoints, uses the actual Barcan-surjectivity API, exposes arithmetic goals, and uses explicit profile-transport equalities. Witness finite prescriptions and individual numerals now have explicit Nat typing. Formula distinguishes algebraic power-body order (`Term.leR`) from boxed inclusion in weak inextensibility. No axioms or `sorry` were added. No owning YAML record or generated `Statements.lean` was changed by this lane.

## Reproduction after explicit human resumption

Run from the bundle root, serially, using the pinned dependency configuration. These commands acquire the shared global compiler lock. Exit 75 means no check started; exit 3 means source drift requires a fresh check. Do not run raw Lean or Lake, and do not automatically execute these after the stop deadline.

```sh
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py research/2026-10-22/lean-formalization/integration-checks/OldNewCompleteAxioms.lean --timeout 240 --lock-wait 60
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/integration-checks/ChoiceHierarchyAxioms.lean research/2026-10-22/lean-formalization/integration-checks/ChoiceFreshColumnsAxioms.lean --timeout 180 --lock-wait 60
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py research/2026-10-22/lean-formalization/integration-checks/ColourCollapsePartialAxioms.lean research/2026-10-22/lean-formalization/integration-checks/ColourCollapseWitnessAxioms.lean --timeout 120 --lock-wait 60
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py research/2026-10-22/lean-formalization/integration-checks/ColourCollapseAxioms.lean --timeout 180 --lock-wait 60
/tmp/classicism-followup-venv/bin/python3 scripts/pmap.py validate
```

Manifests preserve the compiler version/hash, dependency hashes, immutable source snapshots, per-module hashes/fingerprints, exit codes and logs. A hashed uncompiled file is not a verified proof. Repository validation checks records and exports and does not replace Lean elaboration or the main-declaration axiom audit.
