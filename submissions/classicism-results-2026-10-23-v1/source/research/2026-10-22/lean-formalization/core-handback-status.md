# Core compiler handback

23 October 2026. Per the coordinator's latest instruction, the core will finish
its current serial batch and start no new compiler run until the shared lock
is reported ready. **The batch is finished; there is no core-owned compiler
process running.** Shared infrastructure has not been edited in this resumed
turn. All listed source groups are now frozen for the coordinator's handback.

Current batch: `checks/20261023T041703947503Z.json`, targeting
OldNewCompleteAxioms, SP MaxConservativity, SP SignatureSplit, and
RigidityClosureResearchContinuationSchemas. Completed with independent
successes and failures preserved in that manifest.

## Current core-owned source changes

- OldNewBase/Pairs/ND/Predicates/Failures/Separation/FutureBC: the base, all-type
  ND/BC, admitted witnesses, corrected IC/RC failures, central separator and
  future BC failure all pass. No ND source repair was needed. The central
  axiom audit passes with only propext/Classical.choice/Quot.sound. Exact
  evidence: `checks/20261023T041530892093Z.json` and
  `checks/20261023T041341460587Z.json`. Tame and Complete are pending the current
  batch's positive rigidity dependencies. Preserve these completed results.
- ModalRigidityDescent: equality transport repair; source and full module
  C-derivation audit pass.
- RigidityClosureResearchFinite: added the missing C5 import, made two
  complement transports explicit, and reformulated the meet converse's
  inextensibility test as x != a to avoid an implication/negation quotation
  mismatch. Statements are unchanged. FiniteCertificates now imports the
  existing schema definitions. Both source and certificate pass, including
  requested tuple rules. Joins and JoinsCertificates also pass.
- SP Schemas: nested D substitution expansion repaired; passes. SP Reflection:
  explicit single-axiom set on conjunction elimination and an explicit
  Classical.byContradiction term; recheck is in the current batch.
- SP SignatureSplit: standard-library names, Unit exposure, and generic
  type-cast lemmas repaired; recheck is in the current batch.
- SP UniversalCore/Disjunction are no longer core-owned. UniversalCore had
  received an explicit substitution-identity proof and a tentative conversion
  wrapper before reassignment; that version has NOT passed. The requesting SP
  author owns their continuing repair. MaxDiagram was separately repaired,
  verified and released by the SP author; the core did not edit it.

No owning YAML records or published/human proof sources were changed. All
resumed edit batches passed repository validation (132/447/162).

## Final current-batch results and handback diagnostics

- **PASS** rigidity FiniteCertificates, JoinsCertificates,
  ClassificationCertificates, full Schemas, TupleLaws and TupleLawsCertificates.
  The exact full-schema IC/RC/TR/WRP equivalences over unboxed ND+BC now pass.
- **PASS** SP Reflection and MaxDiagram dependency check. Reflection's full
  finite-support Max reflection and conditional SP diagram are checked.
  Its current source is frozen and available to the separate Disjunction owner.
- **OldNewTame: infrastructure failure before elaboration.** Lean could not
  find `/tmp/classicism-lean-cert-cache/Mathlib/Lean/Linter.olean`. The exact
  pinned precompiled file DOES exist at
  `/tmp/classicism-mathlib/.lake/build/lib/lean/Mathlib/Lean/Linter.olean`.
  A new `/tmp/classicism-lean-cert-cache/Mathlib` directory appeared during
  the batch; this is consistent with the shared-cache prefix shadowing the
  later precompiled library root. The runner currently puts the shared cache
  first in LEAN_PATH. Review that ordering before retrying; no need to fetch
  Linter or alter the model proof. Tame's actual positive dependency now passes.
  OldNewComplete and its audit were skipped because Tame failed to import.
- **SP SignatureSplit:** only remaining error is line 75, synthesis of
  Subsingleton for `Ty.denote (singleton Sig b).D Ty.e`. Suggested minimal
  repair: supply the Unit instance explicitly, e.g.
  `exact @Subsingleton.elim Unit inferInstance x y`. Its type-cast lemmas and
  all other earlier errors are repaired. No passing claim for this source yet.
- **SP MaxConservativity:** only remaining goal is `a ∈ L` at line 75 inside
  the filter-membership proof; `ha` has the definitionally equal type
  `FiniteChoiceBasis.ofList L a`. Explicitly change that hypothesis to `a ∈ L`
  before `simp [K, ha, hm]`. The new shallow helper's C certificate passes.
- **Rigidity Nullary:** lines 96 and 99 use `▸` against named predicates
  RigidRigidity / WeaklyRigidWeakRigidity. Replace with explicit
  `Eq.mp (congrArg Rigid ...)` and `Eq.mp (congrArg WeaklyRigid ...)` after
  exposing the relevant predicate. No theorem-statement change is needed.
- **Rigidity AtomicPower:** line 43 refers to absent `atom_le_or_le_neg_arrow`.
  The existing generic theorem is `atom_le_or_le_neg_rel` in Lattice.lean:387.
  Bounded source passes; its certificate and the remaining continuation chain
  are blocked by the earlier Nullary dependency. Uniform/Retractions have not
  yet been checked in this batch.

Sources and current SHA-256 hashes are recorded in
`core-handback-20261023.json`. No compiler re-launch has been made after the
coordinator's instruction and current-batch completion.
