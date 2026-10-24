# Old/new model formalization

Primary assignment: the concrete old/new C countermodel with root all-type ND and BC, et IC/RC failure, and future et BC failure. Ordinary source: `../notes/old-new-boolean-completeness-and-rigidity-separation.md`; the owning construction and published/human originals remain unchanged. The invalid external even-haecceity family is not used.

## First frozen handoff

**READY FOR INTEGRATION:** `Classicism.Models.OldNewBase`. SHA-256: `492004766ed6816fc4ab6bc58208fcf6d8db4d3942d8bd55e1733b321f636a29`.

The file defines E=Nat and O=Nat+Nat, the four actual injection-arrow classes, composition, old/new-preserving symmetries and inverses, finite pinning, the actual symmetric ideally-full model, and `isModel` via `symIdeal_isModel`. It proves finite approximation by target symmetries, factorization of target symmetries through the canonical root arrow, finite partial-injection extension, and finite invertibility for root ND. It has no assumed countermodel, admission or satisfaction hypothesis.


```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.OldNewBase --timeout 240
```

No author-side Lean/Lake command or dependency installation was run. Validation passed after the source batch. The first file is not yet the BC/IC theorem; those concrete semantic proofs are in progress. Root BC will be reconstructed from finite-stabilizer-invariant profile pairs, never from the pointwise union of the current members' full intensions.

## Pair reconstruction, full root BC, and root ND handoff

These are source submissions awaiting verification.

| Module | SHA-256 |
|---|---|
| `Classicism.Models.OldNewPairs` | `7d20108f024d334e765e73f6725e4911257ecf66de9d4126a66420f6b92b9436` |
| `Classicism.Models.OldNewND` | `5386911da6aa8b842f576bd0c178e5c138470115570886f54cac20e7bbd43ea7` |

`OldNewPairs` explicitly constructs an admitted symmetric finitely pinned intension from invariant profiles at E and the canonical old inclusion. `subset_iff_components` proves the order classification at arbitrary RTy; `intersection_invariant` uses the represented family's finite stabilizer and factorization of target symmetries through E; `root_glbs` rebuilds the GLB from component intersections. `root_bc` concludes the official quoted BC instance for every relational type, including t. It does not use pointwise intersections of full member intensions or assume a generic HasLUBs interface.

`OldNewND` uses the actual finite_inverse theorem and a common finite support to prove transport injective at every type out of E; `root_nd` concludes the official unboxed ND instance. Neither result is silently boxed or asserted at O.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.OldNewPairs --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.OldNewND --timeout 240
```

IC_et, RC_et and future BC_et failure proofs are now the remaining concrete target work. No author compiler was run. Repository validation passed after each source batch.

## IC/RC failure and the actual nonentailment handoff

**READY FOR INTEGRATION; frozen.**

| Module | SHA-256 |
|---|---|
| `Classicism.Models.OldNewPredicates` | `1cddee34a5600fe03843787862cd9c2f0b6b48a33444a223f8b6dd13ea412ee2` |
| `Classicism.Models.OldNewFailures` | `6f4f541db744861821772d3f9a300bd25973c657507f35d1bf772b71c61adb0e` |
| `Classicism.Models.OldNewSeparation` | `a6aa48bbc4618d10bf8d195435958f977e4b49fea083d54a8c11993c5afb2d3f` |
| `Classicism.Models.OldNewTame` | `38b3cc608d1a8ac861f9a192d88ce1cd56c3e7ee37f1b68bad8425decd2688ec` |

`OldNewPredicates` proves admission of top, old-only, haecceity, anti-haecceity and represented old anti-haecceity-family witnesses at either object; it supplies the needed transport and pinning lemmas. `OldNewFailures` derives the official IC semantic clause, proves universality propagates along all E→E arrows, and uses old-only plus the return arrow and inequality to refute IC_et. It refutes RC_et by unpacking RC and retaining IC.

`OldNewSeparation` supplies the actual full-schema HoldsAx ND/BC verdicts, `central_countermodel`, consistency of that base, the exact IC_et/RC_et nonderivability, and full-schema nonentailments. None takes a countermodel/verdict as a hypothesis. `OldNewTame` is a separate assembly with the positive rigidity helper's schema certificate: full TR fails in this concrete model, hence ND+BC does not entail TR. It does not invent a fixed-type TR failure.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.OldNewPredicates --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.OldNewFailures --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.OldNewSeparation --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.OldNewTame --timeout 240
```

The delegated future-BC author owns `OldNewFutureBC`. A complete uncompiled GLB-failure proof had already been drafted in OldNewFailures when that delegation arrived; it was removed before this handoff to avoid duplicate declarations and saved solely as `old-new-future-bc-reference.txt` for reuse. It uses precisely the admitted old anti-haecceity family and a new point lower bound, with a source transposition followed by the return arrow. The main files do not duplicate the delegated future result.

All files remain source submissions until the sole compiler records success against exact dependency fingerprints. No author-side Lean/Lake run was made. Validation passed after each source batch. The subsequent explicitly assigned queue is `rigidity.32` (fixed-point entrance-cone model) and `rigidity.33` (colour-collapse model), after this central OldNew implementation; construction, IsModel, verdicts and actual nonderivability must be tracked independently.

## Complete root/future assembly

**READY FOR INTEGRATION; frozen:** `Classicism.Models.OldNewComplete`, SHA-256 `9e53947b96ca26bc6dd9288f10920132a1c9a55ce86df777a7fffcd8a1b49bba`. It imports the independently authored OldNewFutureBC and the root/Tame assembly, combines all actual model verdicts in `complete_countermodel`, and proves ND+BC does not entail boxed BC (already et). Full BC remains local to E; the future failure is asserted for each arrow E→O.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.OldNewComplete --timeout 240
```

This completes source-level coverage of the assigned OldNew result; integration may still find proof/elaboration errors, so no successful kernel certificate is claimed here. The ordinary proof assumptions were not strengthened.
