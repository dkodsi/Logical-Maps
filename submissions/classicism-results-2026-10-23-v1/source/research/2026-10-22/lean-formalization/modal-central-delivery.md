# Modal and central-model verification handoff

23 October 2026. Existing research has been prepared for delivery in the
original finitary C. The principal finite-signature countermodel now passes
Lean and its public axiom audit. No database verdict, generated statement,
or database Lean flag has been changed.

Current hashes and matching source evidence are in
[`modal-central-source-manifest.json`](modal-central-source-manifest.json).
The machine-readable lane report is
[`verification-updates/modal_central_negative_models.json`](verification-updates/modal_central_negative_models.json).

## Checked main countermodel

For the permitted signature **Sigma={c:et}**, let Delta contain the complete
Logical Necessity schema, all-type boxed Barcan, and all-type boxed Relational
Choice. The actual constructed model satisfies Delta and fails the library's
exact quoted Actuality sentence. Consequently Delta is consistent and does
not entail the Actuality schema. Here Relational Choice is distinct from
Rigid Comprehension.

The model has singleton individuals and recursively constructed, countably
supported typed intensions on the full product of finite-word monoids indexed
by P(Nat). Countably many pure unary formulas select witnesses; one fresh
coordinate glues their entire future profiles into c. The ordinary proof is
[`followup/central-map.md`](../followup/central-map.md), especially §§1–3 and 6.
The formal proof constructs the domains, interpretation, term closure and
semantic witnesses; it does not assume a model exists.

The main declarations are under
`Classicism.Meta.Intensional.Central.OneConstant`:

| Declaration | Exact role |
| --- | --- |
| `B_isModel` | Closure of the actual typed model |
| `holds_logicalNecessity` | Full existing signature schema, including the empty constant tuple |
| `holds_package` | Logical Necessity plus all-type boxed Barcan and Relational Choice |
| `package_consistent` | Consistency via the actual model and C soundness |
| `package_not_entails_actuality` | Nonentailment of the existing Actuality schema |

The complete 89-module closure and joint model/axiom driver passed in
[`checks/20261023T054410104697Z-48120445.json`](checks/20261023T054410104697Z-48120445.json),
with exit code 0 and captured sources matching the current files at completion.
The exact driver is
[`CentralModelAxioms.lean`](central-checks/CentralModelAxioms.lean).
Its [axiom report](logs/runs/20261023T054410104697Z-48120445/CentralModelAxioms.log)
prints only `propext`, `Classical.choice`, and `Quot.sound` for the model,
schema satisfaction, consistency and nonentailment declarations. This is a
classical metatheoretic model proof, not a choice-free certificate.

The explicit finite signature refutes a signature-uniform implication. The
stronger ordinary construction for every fixed set-sized signature is not
being claimed as formalized. No infinitary language extension is used here.

## Further checked model components

The pure supported product independently satisfies all-type boxed Barcan and
Relational Choice and fails Actuality for any nonempty alphabet. Its joint
certificate and public audit passed in the successful subtargets of
[`checks/20261023T053715003577Z-373ddacd.json`](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1);
see [`CentralProductAxioms.lean`](central-checks/CentralProductAxioms.lean) and
[its axiom report](logs/runs/20261023T053715003577Z-373ddacd/CentralProductAxioms.log).
This run also checked finitary syntax countability. Syntactic countability
places no bound on any semantic domain.

`CentralSupport` checks the general external-support closure construction.
`CentralChoice` proves extensional fullness by arbitrary arrow-independent
extension profiles and derives exact boxed Relational Choice and Transversal
Choice. It never assumes the members of an extension share a common support.
The foundation/choice public audit is
[`CentralFoundationAxioms.log`](logs/runs/20261023T051518714412Z-101d064e/CentralFoundationAxioms.log),
with passing subtargets in
[`checks/20261023T051518714412Z-101d064e.json`](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1).
The closure and choice declarations use the same three metatheoretic axioms;
extension-profile and extensional-fullness lemmas use only `propext` and
`Quot.sound`.

Whole-entity gluing, supported-tuple coordinate factorization, and external
countable joins now pass. The latter two have a public audit in
[`checks/20261023T054120203114Z-4a90260b.json`](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1),
with [the exact report](logs/runs/20261023T054120203114Z-4a90260b/CentralGeometryAxioms.log).
These support the ordinary arguments in central-map §§8 and 10. They do not
by themselves establish the full Tame Rigidity or internal Countable Boolean
Completeness schemata. In particular, an external countable join is not a
substitute for the missing internal countability bridge.

The two initially missing Mathlib imports were removed through owned,
checked supporting implementations: finite lists for words and explicit
constructor codes for syntax. No shared Mathlib or toolchain was modified.
Earlier failed or busy runs remain saved; a mixed manifest certifies only
its successful subtargets, not every requested target.

## Checked positive modal results

**Modal propagation.** Over finitary C, the complete Strong Leibniz and Rigid
Comprehension schemata imply necessary Strong Leibniz, necessary relational
Barcan, necessary Rigid Comprehension and necessary Boolean Completeness.
The Barcan conclusion here is relational; BF_e is not silently added.
The main declaration is
`Classicism.Meta.Research.ModalPropagation.all_four`.
The full ordinary arguments are
[`strong-leibniz-rigid-bottom-cut.md`](../strong-leibniz-rigid-bottom-cut.md)
and [`followup/modal-propagation.md`](../followup/modal-propagation.md).

The core's successful full-schema check is
[`checks/20261023T025257130403Z.json`](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1);
its axiom audit is
[`checks/20261023T030134260568Z.json`](checks/20261023T030134260568Z.json).
The main entailment and final list entailment report only `propext` and
`Quot.sound` as metatheoretic axioms about C derivations.

**Rigid unions and descent.** Rigid indexed unions, direct images, inverse
images under the stated necessary injectivity and image restrictions, and
comprehension descent are proved with their explicit types and hypotheses.
No BF, ND or choice premise is added; function outputs remain relational.
The prose is [`modal-rigidity-descent.md`](modal-rigidity-descent.md).
Principal declarations in `Classicism.Research.ModalRigidityDescent` include
`indexed_union_rigid`, `direct_image_rigid`, `inverse_image_rigid`, and
`rigid_comprehension_descent`.

The core's repaired source and full-module derivation check passed in
[`checks/20261023T040634048786Z.json`](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1).
All fifteen source theorems were derived. The three printed main `.derivable`
declarations use only `propext` and `Quot.sound`. The core's equality-transport
repair is preserved; its source hash still matches the handback snapshot.
Historical READY notes are superseded by these passing checks.

## Checked Vicinity consequence and remaining scope

The same package also fails the exact Vicinity sentence and does not entail
its schema. `Central.Product.not_holds_vicinity` and
`Central.OneConstant.package_not_entails_vicinity` passed with their public
axiom audit in
[`checks/20261023T054809252922Z-5177013d.json`](checks/20261023T054809252922Z-5177013d.json).
The [audit report](logs/runs/20261023T054809252922Z-5177013d/CentralVicinityAxioms.log)
again lists only `propext`, `Classical.choice`, and `Quot.sound`.

All 18 prepared Central source modules and audit drivers now have passing
checks matching their current bytes and local dependency sources. Historical
“uncompiled draft” comments are retained from drafting; the manifests and
current status establish verification.

Further formalization obligations remain exact boxed Tame Rigidity, the
internal finite-cardinality successor-orbit bridge for Countable Boolean
Completeness, the separate symmetric-surjection model and its full
completeness/power package and choice failure, arbitrary set-sized signatures,
and moving-individual infinity variants. Their ordinary sources include
[`central-map-complete-gluing.md`](../followup/central-map-complete-gluing.md)
and [`choice-support-obstruction.md`](../followup/choice-support-obstruction.md).
The different propagation countermodel is retained in
[`propagation-without-barcan-countermodel.md`](../followup/propagation-without-barcan-countermodel.md).
These limitations are not concealed in added hypotheses. No attempt to settle
an open conjecture is included in this delivery pass.

## Reproduction and shutdown

From the bundle root, use the shared locked runner:

```sh
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py research/2026-10-22/lean-formalization/central-checks/CentralModelAxioms.lean --timeout 180 --lock-wait 300
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py research/2026-10-22/lean-formalization/central-checks/CentralGeometryAxioms.lean --timeout 180 --lock-wait 300
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py research/2026-10-22/lean-formalization/central-checks/CentralVicinityAxioms.lean --timeout 180 --lock-wait 300
```

The commands describe reproduction after explicit human resumption; no future
run is scheduled. The human cutoff is 05:57 UTC on 23 October 2026. This lane
finishes by 05:55, and its own bounded wrapper cannot keep a check running past
05:53. The dated wrapper is deliberately expired after that cutoff.

A busy exit 75 starts no Lean check; source-drift exit 3 requires a fresh check.
Preserve source hashes, dependency fingerprints, snapshots, logs and axiom
reports. Repository validation passes, but validation alone is not a Lean
certificate. Current terminal status is in
[`central-verification-status.md`](central-verification-status.md).
