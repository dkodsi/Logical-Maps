# Colour-collapse entrance formalization

Tracked obligation: rigidity.33. Exact source `../notes/colour-collapse-entrance.md`. Target: concrete C model with full TR at A, boxed BF at every type, boxed RP_et, and failure of WRP_et. RP at higher relation types is not claimed; the full-schema TR+RP conjecture is not refuted by this target.

## First concrete handoff

**READY FOR INTEGRATION; frozen.**

| Module | SHA-256 |
|---|---|
| `Classicism.Models.ColourCollapseBase` | `cfd5c3fc5eacb62b734b8c868e4c10d86124c6fa9728763efe2e9aec65f09d4b` |
| `Classicism.Models.ColourCollapseRigidity` | `c617ebcafeb26d1138356b3b4ce238e94c0cf376b1931990e266e18dcca455a0` |
| `Classicism.Models.ColourCollapseWitness` | `a349b3973e3f91b9bb5432cb5c6443eefaee0b2b3441904000ed61563d77ad5d` |

`ColourCollapseBase` constructs all three Nat-based objects and the actual allowed forward surjections, symmetries, finite-support model and IsModel proof. B has the evens as colours and C has {0,1}. It proves surjective transport and the exact boxed BF instances, builds entrance/collapse/merge arrows, constructs finite colour-compatible extensions explicitly, and derives root finite factorization.

`ColourCollapseRigidity` proves tuple finite pinning, admission of B_N(D), weak rigidity's containment in that admitted relation, root weak rigidity implies exact-image profiles, and exact-image profiles imply full rigidity. `tame_at_root` discharges the official quoted TR instance at arbitrary RTy. These are constructions/proofs in the actual model, not premises of a generic interface.

`ColourCollapseWitness` admits the coloured unary relation at B, proves its weak rigidity by finite prescribed surjections, admits the finite pair-haecceity union at C, and uses the actual collapse and merge arrows to refute the coloured relation's rigidity.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ColourCollapseBase --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ColourCollapseRigidity --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ColourCollapseWitness --timeout 240
```

No author compiler/Lake run or dependency installation occurred. Validation passed after source batches. These remain proof submissions pending the sole compiler. Full target still requires the all-object rigid-unary classification, necessary RP_et, the quoted weak-power failure and the final nonentailment assembly; it is not marked complete. The explicit coloured witness is reusable in those remaining proofs.

## Separate fixed-point entrance obligation

rigidity.32 remains assigned and uncompleted. The local SymmetricIdeal documentation expressly excludes the qualitative-link base; its recorded singleton-individual version also separates the pinning base from the interpreted individual action. Current SymT ties its pinning action to e. Thus implementing that exact cone requires the concrete qualitative-link tail and a separately pinned singleton-individual semantic construction, followed by the root/future verdicts. Substituting a full model or assuming that tail's existence would not meet the tracked target. The colour-collapse construction uses the existing identity-individual semantics and is therefore being completed first while the exact cone obligations remain visible.

## Unary classification and lifting handoff

**READY FOR INTEGRATION; frozen source submissions, not compiler-verified.**

| Module | SHA-256 |
|---|---|
| `Classicism.Models.ColourCollapseUnary` | `9c7cafff3a670dd3b572b921db3fc0dff75260b9a1cef685cde57af548a3fd61` |
| `Classicism.Models.ColourCollapseSubobjects` | `ed623131e01e727b542b04f78684fceaac1e18666dc35e5939f19a2eec3a50a8` |
| `Classicism.Models.ColourCollapsePowerCore` | `cca91b02b33d95104129d9810222c1e6b5767784d16c16d6b1101fd2fa50f992` |

`ColourCollapseUnary` admits finite haecceity unions and the universal unary relation, proves weakly rigid coextensive uniqueness, finite interpolation with one fresh prescribed value, the all-object finite-or-universal classification, and exact-image profiles for rigid unary relations. The exceptional infinite proper B extension is excluded by the actual C collapse and merge. A finite support itself can be used for the exceptional upper bound; it need not equal the finite uncoloured part.

`ColourCollapseSubobjects` selects finite preimages **inside the original extension**, proves full-intension inclusion from current-extension inclusion for weakly rigid relations, and lifts every future rigid subobject. If the future extension is universal, the original rigid relation itself is a lift, by coextensive uniqueness. It then proves exact images for any admitted property with the rigid-power profile. The official term-to-profile bridge is still a separate obligation, not presumed by the final target.

`ColourCollapsePowerCore` proves the concrete weak-power obstruction from the weak-power and rigid-test profiles: root TR makes every current weak-power member necessarily rigid, whereas the actual colour relation at B is a future weak-power member that fails rigidity. The final assembly must discharge both profiles for actual denoted terms.

An independent read-only mathematical audit found the classification and lifting arguments sound, including the need to select preimages inside the original extension. It also identified a static source repair for the integrator in the already-frozen `ColourCollapseWitness`: lines 42 and 57 use `h.2.2` as colour preservation; the conjunction in `Arr` requires `h.2.2.2`. No frozen module was edited by this author.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ColourCollapseUnary --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ColourCollapseSubobjects --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ColourCollapsePowerCore --timeout 240
```

Validation passed after each source batch: 132 principles, 447 results, 162 models. These checks validate the record bundle, not Lean elaboration. No compiler/Lake run or installation was performed by the author. The isolated formula bridge and final quoted RP/WRP assembly remain in progress.

## Final source assembly, 23 October 2026

**The colour-collapse source package is ready for integration and frozen. Lean verification is pending.** This supersedes the earlier source-level outstanding items for rigidity.33; it does not mark the tracked formalization verified or complete.

| Module | SHA-256 |
|---|---|
| `Classicism.Models.ColourCollapseFormula` | `0bbc5022fb923cfe73582443327f95a84df89f34114791d058943733d663785e` |
| `Classicism.Models.ColourCollapseSeparation` | `bc408c23418ae8fc9eb147fb208356262a7430ad10ce72376cf0ae6320814744` |

`ColourCollapseFormula` constructs the rigid-power, weak-power and rigid-test entities as values of actual lambda terms, using `isModel` for admission. It proves their full outgoing profiles, translates the semantic rigidity predicates, handles the quotation procedure's constructor-type unary expansion, and supplies the official quoted RP/WRP equivalences. The exact quotation equalities and all elaboration remain subject to the compiler check.

`ColourCollapseSeparation` discharges the profile premises in the preceding semantic lemmas and assembles:

- `rigid_power_at`: the official RP_et instance at every object reachable from A;
- `boxed_rigid_power_et`: the official boxed RP_et sentence at A;
- `not_weakly_rigid_power_et`: failure of the official WRP_et sentence at A;
- full-schema TR and boxed BF, consistency of their union with the single boxed RP_et instance, and the corresponding WRP_et nonderivability/schema nonentailment;
- `central_countermodel`: the exact concrete semantic conjunction for rigidity.33.

The background contains **only RP_et**, boxed. No higher-type RP claim or counterexample to full-schema TR + RP is made. No owning YAML, generated statement, original research note, or frozen earlier source was modified. The new files contain no `sorry`, `admit`, or new axiom declarations.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ColourCollapseFormula --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ColourCollapseSeparation --timeout 240
```

Run the modules serially after repairing/checking their frozen dependencies, including the two `ColourCollapseWitness` projection issues noted above. The sole compiler owns any repairs to these submitted modules. Record validation passed after the final source batch; there was no author compiler/Lake run or dependency installation. The exact fixed-point entrance construction, rigidity.32, remains unfinished for the separately documented reasons.
