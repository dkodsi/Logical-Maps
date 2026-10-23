# Checked integration checkpoint

All compilation is serial using the pinned Lean 4.33.1 compiler. The `checks/`
directory contains durable source/dependency-fingerprinted runs; `logs/` contains
the exact gate, type, translation, and kernel diagnostics. Failed runs are
retained and superseded only by a successful run of the repaired source.

## Complete C certificates at this checkpoint

- **Uniform half-comprehension:** Actuality is equivalent, at each fixed closed
  relational type (empty tuple included), to uniform persistent, uniform weakly
  persistent, or uniform weakly inextensible comprehension. Full uniform IC
  implies Actuality only. `UniformHalfComprehensionClosed` discharges all tuple
  existence premises; no optional assumption remains. See `uniform-status.md`.
- **Evaluator kernel:** positive evaluator iff Actuality; actual-world uniqueness
  and the current atom-local Barcan lemma. `CanonicalEvaluatorCertificates`
  also passed: canonical replacement, uniqueness among replacements,
  idempotence, and literal universal/existential quantifier commutation for
  each fixed type and current predicate. No boxed universal-predicate claim.
- **ND/IC:** persistent-falsity stability; persistent necessarily separated
  relations equal their inextensible coextensions; weak-rigidity square and
  internal-separation lemmas; the exact `ND_t + IC_tau -> TR_tau` rule, with an
  all-tuples `.listRule`. **The full local ND_t + IC_(tau t) -> WRP_tau
  theorem now passes the gate, type audit, and C translation**, including its
  all-tuples `.listRule`. Descent, rigid power, and the bounded-decision step
  are checked too. See `nd-ic-status.md` and the 20261023T022700791873Z run.
- **Atom coordinates:** requested projections, pins, coordinate recovery,
  collision/injectivity and unary Atomicity/BF results; three schema rules also
  have all-tuples list rules. `AtomCoordinates` exits 0 after explicit audits.
- **Bounded splitter:** guard, atom obstruction, and Atomicity forcing a split
  bound/guard to zero. `BoundedSplitter` exits 0. No Max inconsistency is inferred.
- **Choice completeness:** the submitted evaluation/join, completeness descent,
  represented disjoint-family, and Actuality/meet lemmas. Both source and
  certificate modules exit 0. One ambiguous haecceity term was made explicit.
- **Choice fixed point:** coextension-invariant supremum selector and the stated
  graph/operation fixed-point theorems. Both source and certificate modules exit
  0; translation took about 141 seconds, so avoid unnecessary repeats.
- **Choice Actuality:** the sharp `RC_(t,t) + BC_tt -> Actuality`, its correctly
  boxed version, and the typed Transversal consequence all pass. The exact
  latter premises are `RC_(t,t) + BC_tt + RC_(sigma t,sigma)`. This does not
  settle RC alone. See the 20261023T022130038754Z manifest and `choice-status.md`.
- **Strong Possibility consequences:** the 31 submitted finitary C lemmas in
  `StrongPossibilityConsequencesC.lean` pass their explicit gate, type and
  derivation checks. This does not prove SP consistency or the missing Max-model
  consistency premise for unconditional monism. Eight additional stability
  lemmas pass in `StrongPossibilityConsequencesStability`. Its schema assembly
  currently fails at instantiating the translated D-idempotence theorem.
- **Choice hierarchy:** selector/FC equivalences, retractions, haecceity transfers
  and the stated local descent/diagonal theorems pass their explicit audits and
  translations. Pair/graph coding and `ChoiceHierarchySchemas` also pass.
  The recursive embedding realization, exact single boxed Plenitude base,
  all-type selector-stage cofinality, diagonal-schema equivalence and
  diagonal-stage cofinality now all pass. Every theorem of full boxed FC
  follows from one finite selector stage and one finite diagonal stage, with
  no assumed cofinality or embedding premise. Actual budget retractions and
  closed-type haecceity decoders pass too. Evidence: `checks/20261023T030134260568Z.json`.
  Strictness and nonfinite axiomatizability still need separation models.
- **Full modal propagation:** all-type Strong Leibniz plus Rigid Comprehension
  entails boxed Strong Leibniz, relational Barcan, Rigid Comprehension, and
  Boolean Completeness. `ModalPropagationSchemas.all_four` now compiles from
  actual translated list-rule certificates; empty tuples are included. BF at e
  is not claimed. Evidence: `checks/20261023T025257130403Z.json`.
  The all-record Arity import hit the 180-second bound; the successful run
  instead uses `ModalPropagationRigidPower`, a narrowly scoped, attributed
  copy of the needed existing proofs, plus the elementary type/list lemma.
  The minimal `ModalPropagationAxioms` driver reports only `propext` and
  `Quot.sound` for `all_four` and its completeness list entailment.
  Original Arity/Lists proofs are untouched. Source, gate, type, translated
  rules, and all-schema composition all passed. The original fourteen
  `modal-checks` drivers also remain passed.
- **World/core and arithmetic:** ActualityCore, WorldRepresentation,
  FregeInfinity, CoreNumberIsomorphism and GeneratedAlgebraTransfer certificate
  modules pass. Preserve their exact source hypotheses: number comparison and
  algebra transfer retain their specified maps/commutation conditions. Extra
  world/core helper drivers are still queued; no full probability interpretation
  follows merely from these modules. `FregeArithmeticGraphsCertificates` now
  also passes its fourteen concrete C graph theorems: recurrence, totality,
  inversion, and functionality. Totality uses no Infinity; functionality retains
  quantified Infinity. `ActualityCoreNumbersCertificates` now also passes:
  the actual-world cut constructs the number map and its admitted predicate
  interface, rather than assuming that interface. It proves successor
  commutation, numberhood, surjectivity and Infinity transfer; numerical
  identity/inverse uniqueness retain quantified Infinity. Concrete addition/
  multiplication comparison now passes in `ActualityCoreArithmeticCertificates`,
  including forward/reflected graphs, totality, functionality, order, and
  admission of the target operations as relations. Evidence: `checks/20261023T031752976671Z.json`.
  `ActualityNumericalRelationsCertificates` also passes: number-field support,
  predicate/binary-relation round trips, induction and zero/successor laws.
  No Choice/BF assumption or selected inverse operation is added. Arbitrary
  syntax interpretation, Gallin interpretation and external standardness
  remain separate obligations.
- **Finite sorts:** the k=1,2,3 cover certificates pass: Atomicity/BC at relational
  sorts, Actuality at t, and Relational Choice from a finite input to any
  original output sort including e. The external source generator is not an
  internally proved theorem for every finite k.

## Checked metatheory, with explicit limits

`ChoiceHierarchyTypes` compiles its syntactic tower/order bounds.
`FiniteChoiceBasis` compiles finite optional-axiom support for actual C
derivations, finite support of finite conclusions, and the **conditional**
nonfinite-basis/stage reductions. Its induction was generalized to a variable
source axiom set with a containment map; the logical-only Subst premises are
preserved. No finite-fragment separation model is supplied by these theorems.

MaxAtomicitySyntax, MaxAtomicitySetSyntax, and MaxAtomicityReduction compile.
They certify syntax and a conditional reduction, **not** the proposed full
Maximalism/Atomicity inconsistency.

The AtomicProbabilityAlgebraChecks dependency batch compiles as ordinary
algebraic metatheory. Finite support/residual/envelope identities report no
axioms; the finite class-average/fibre results report `propext`,
`Classical.choice`, and `Quot.sound`. They are not choice-free proofs or
translated C probability theorems. The internal interpretation remains missing.

## Still in the integration queue

Priority order after the modal and positive hierarchy successes: direct local
Transversal and CBC/CCC;
genuine core/number interpretation bridges; essential semantic dependencies for
the substantive negative models. Further Max/selector and probability sources
remain submissions. BooleanValued semantics requires the pinned narrow Mathlib
dependency, now installed narrowly. See `dependency-status.md` and
`mathlib-dependencies.json`: 650 source-hashed cached imports, no Mathlib library
source build. The complete `BooleanValuedChecks` dependency chain now compiles:
renaming/substitution/conversion/holes, top-valued C soundness, designated-truth
soundness with only designated-true optional axioms, and explicit ND/BF/CBF
value calculations. The kernel reports `propext`, `Classical.choice`, and
`Quot.sound` throughout. This is ordinary classical model metatheory, not a
choice-free metatheorem or a certificate for a concrete negative model. No concrete negative central-question model is
claimed certified here. Author `READY FOR INTEGRATION` notes are handoff states,
not successful checks. Exact module results remain in the fingerprinted manifests.

No original research note, database YAML, generated `Statements.lean`, or
verification status was changed. Research certificates do not set `lean: verified`
on an existing database record; that requires its documented `pmap lean-check` route.

## Current resumed-run diagnostics

The first ChoiceChains certificate check exceeded 240 seconds after passing
source/gate/type checks. The subsequent long independent batch was interrupted
to avoid rebuilding the same translated dependencies. ChoiceBoolean and
ChoiceCountable source files compile; their main C certificates remain pending.
The repaired certificate import chain now reuses ChoiceFixedPointCertificates,
then ChoiceChainsCertificates, then ChoiceCountableCertificates. This is a
build-efficiency repair, with no mathematical premises or conclusions changed.

## Negative-proof infrastructure

`Classicism.Models.ChoiceFreshColumns` now compiles after an explicit predicate
binder annotation. It proves fresh-column compatibility with an explicit common
extension and unconditional absence of a finitely transposition-supported
selector on predicates on Nat. This is genuine ordinary metatheory, not a C
countermodel certificate or the full nonfinite-basis theorem. The required
forcing symmetry/hereditary-symmetry/finite-fragment preservation bridge remains
unformalized. The diagnostic now passes: `fresh_amalgam` uses only `propext`;
`no_finitely_supported_selector` uses `propext` and `Quot.sound`, with no
`Classical.choice` or added axiom. The analogous positive-hierarchy diagnostics
also report only `propext` and `Quot.sound`.

## Active next checks

Compiler ownership transition: see `core-handback-status.md`. The core's batch
has finished; no core-owned compiler process remains. No new compiler run
will start pending the coordinator's shared-lock-ready instruction. The final
batch verified the full IC/RC/TR/WRP equivalence over ND+BC, finite and tuple
closure certificates, and SP Reflection. Remaining source and cache failures
have exact handback diagnostics and frozen hashes.

### Old/new separator: central result verified

`OldNewSeparation` and `integration-checks/OldNewSeparationAxioms.lean`
pass in `checks/20261023T041530892093Z.json`. This supplies the actual concrete
C-model with full unboxed ND and full BC, IC_et and RC_et failures, consistency
of that base, and both full-schema nonentailments. The nine exported axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`, appropriate
to the ordinary model-theoretic metatheory; no `sorryAx` or added model axiom.
Admission, finite pinning, symmetry, all-type transport injectivity, invariant
profile-pair reconstruction, represented-family GLBs and the corrected IC
argument are proved dependencies, not assumed countermodel interfaces.

`OldNewFutureBC` separately passes in `checks/20261023T041341460587Z.json`:
the admitted old anti-haecceity family has no GLB at O, and boxed BC_et fails
at E. Its combined final axiom audit and the Tame/Complete assemblies remain
queued behind the positive rigidity certificates.

`ModalRigidityDescent` and its complete derivation audit also pass after a
typed equality transport repair. The rigidity closure source now compiles;
its C translation and list certificates are being repaired and checked.

Work resumed on 23 October following the user's clarification. The old/new
countermodel is the primary integration target. All main verdict modules and
the supplementary FutureBC/Tame/Complete modules are now frozen for repair.
The precise pinned Mathlib dependencies are installed. The main separation is
being checked before the supplementary claims; source submission alone is not
the ND + BC / no RC countermodel certificate.

ChoiceChains, ChoiceCountable and ChoiceTransversal certificates now all pass
(manifest `checks/20261023T032657816117Z.json`). Factoring through an explicit
conforming predicate resolved the translation timeout; the main theorem
discharges maximality. The exact results include RC + CBC + Boolean CCC => BC,
and RC at (sigma t, sigma t) + BC at sigma t => TC at sigma, without Actuality
or BC at tt. The countability predicate uses represented Frege-number labels.
ChoiceJoinTruth also passes, preserving its existing-join hypothesis.

The compact whole-module ActualityCore and WorldRepresentation derivation
audits pass in that manifest, including their helper lemmas. Graph and bridge
extensions remain separate queued checks.

The SP schema repair now passes (ordinary formula-substitution equality at
nested D), with its conditional monism/consistency scope unchanged. See
`sp-core-verification-status.md` for the separately tracked SP integration.
