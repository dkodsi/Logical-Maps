# Central negative countermodels: implementation plan

22 October 2026, America/New_York. Assignment resumed for substantive model
certificates. This is a plan and mathematical audit ledger, not verification.
The sole compiler/dependency owner is task
`01a1664d-7c13-7701-b52c-2070ee16eb06`. Authors write new files, validate the
repository, and freeze/hash ready modules. No Lean/Lake runs, new workers,
cross-chat messages, original-proof edits, YAML edits or rendering here.

## Targets and sources

The coordinator's efficiency refinement makes the first deliverable the exact
countermodel over the permitted finite signature Sigma={c:et}. Countably many
pure unary formulas suffice for witness selection; the index set is P(Nat).
This already separates Logical Necessity from Actuality. The original
every-fixed-set-sized-signature theorem remains a later target. No cardinal
generalization is a prerequisite to integrating the concrete witness.

1. `followup/central-map.md`, §§1–6, 8, 10: the supported product of free-word
   monoids, with singleton individuals. Target the actual model of C,
   Logical Necessity for each prescribed set-sized signature, boxed BF and
   Tame Rigidity, Relational Choice, Countable Boolean Completeness, and
   failure of Actuality/Vicinity. Its failure of WIC and Rigid Power must not
   be conflated with the second model's completeness package.
2. `followup/central-map-complete-gluing.md`, §§1–7: the distinct symmetric
   word-times-surjection model. Target boxed full BC/BF/Tame Rigidity/WRP,
   Logical Necessity, no Actuality/Vicinity, and failure of Relational Choice.
   Arbitrary constant graph profiles are not admitted in this model.
3. Moving-individual and non-right-cancellative-factor variants remain
   separate constructions and separate verdicts. Infinity means the stated
   quantified cardinality axiom, not merely an external infinite set.

Direct sources are these new research notes (`misc` for any later record).
Existing action/pinning background is Bacon–Dorr, Classicism, draft 16 May
2023, §3.5 pp.58–61 and Appendix D pp.73–74, as indexed in the source notes.
No source is being credited with the new central constructions.

## Existing Lean infrastructure and the nontrivial adaptation

Use `Semantics/Intensional.lean` and `IntensionalSoundness.lean` for typed
domains, actual intensions, term semantics and C soundness. The flattened
intensional representation already handles currying and avoids rebuilding
the raw exponential action. `IntensionalFull`, `IdeallyFull`, `Symmetric`
and `IntensionalFacts` provide action products, pinning arguments, symmetry
closure, and satisfaction-to-nonderivability transfer.

The existing ideally-full/symmetric constructor pins to the *typed*
individual action. It cannot directly express either primary model:
singleton individuals would remove all coordinate dependence; in the
symmetric model, pinning only to U would also remove the unrestricted word
coordinate needed for gluing. Do not pretend `symIdeal_isModel` already
constructs these models. Build a fresh external-support subaction and prove
its closure from the actual term interpretation. Preserve those existing
modules unchanged.

## Proof obligations, in dependency order

- Concrete arrow monoids and bounded-coordinate agreement. Prove agreement
  survives appropriate composition; prove the support ideal's finite and
  indexed-union laws and existence of a fresh coordinate. Cardinal bounds
  for arbitrary signatures must be stated explicitly.
- Recursive typed inner domains, tuple actions, injective/natural inclusion
  into actual intensions, and all term-closure cases. In particular lambda
  abstraction and higher quantification must quantify over the unchanged
  full current domains, not union supports of all quantified entities.
- Complete-profile suffix lifts and simultaneous gluing. A gluing result
  for current extensions alone is insufficient. Use one fresh coordinate
  for all signature interpretations and all constants together.
- Satisfaction bridges: entailment is profile inclusion; modal truth
  transports all parameters; BF follows from onto type actions; pure closed
  sentences are invariant in the one-object model. Logical Necessity itself
  remains unboxed and signature-dependent.
- Supported-model negative witnesses q_i and the one-coordinate killing
  action; actual truth has no least member and cannot entail possibility of
  every truth. Directly certify these model formulas before treating them
  as a separation of schemas.
- Supported-model choice: constant graph admission plus external selection;
  countable BC: the internal finite-cardinality extension is the external
  successor orbit, then inject actual A-members into external natural
  indices and form the supported join. External countable closure alone is
  not the stated Countable BC theorem.
- Tame Rigidity: prove the exact-image characterization by the specific
  coordinate factorization. Do not assume arbitrary exact-image profiles
  are admitted or import full-model Rigid Power.
- Symmetric-model stages: actual bounded pinning and permutation covariance;
  partial-map/surjection extension and fresh-permutation lemmas; the hull
  LUB proof; exact-image and power lifting; the actual two-output swap
  contradiction (and later the sharper proposition-input obstruction).

## Audit checkpoints

The supported-profile closure and coordinate-gluing calculations preserve
the distinction between fixed external set members and transported logical
parameters. The full product includes arrows with arbitrarily large support;
restricting the arrows would invalidate the factorization argument.

For symmetric power, separately check the construction of j0 whose only
nonsingleton fibers are inside N, the bound on j0 inverse-image of T, and
the factor v with j0 u = v j0. These are decisive construction lemmas, not
acceptable model-existence assumptions.

A completed ordinary Lean algebra lemma is metatheory. An actual typed
premodel, its proved IsModel, the exact HoldsAx/HoldsSentence statements,
and the soundness/nonderivability transfer are separate milestones. A
conditional structure field asserting the target separator will not count
as a model certificate. Any discovered mathematical gap will be saved with
its exact failed step and scope.
