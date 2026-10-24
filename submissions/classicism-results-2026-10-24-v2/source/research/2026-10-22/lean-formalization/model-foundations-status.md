# Model foundations: author status

**Current status (23 October):** the full single-predicate driver, finite-sort
certificates and Boolean-valued driver have passed current locked checks.
The nominal checked prefix
ends at substitution; the conversion repair and downstream verdicts remain
unverified. See
[the current delivery summary](model-foundations-delivery.md) and
[machine-readable evidence](verification-updates/model_foundations_signature_nominal.json).
The older READY/frozen submissions below are retained as historical handoffs.

## Finite-sort package — READY FOR INTEGRATION

These are proof candidates; compilation, gate/type audits and translated C certificates are required for certification.

| File (bundle-relative) | SHA256 |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FiniteSortStructure.lean` | `fe2613bc8800aa1b74d7e1c9e9b6dbf63cf89ec90ba9104c4670ab75904e7f31` |
| `topics/classicism/lean/Classicism/Results/Research/FiniteSortStructureBounds.lean` | `9a4ab90ea3dc0ca0ba654234bd4c6c41083dc74a87010a74b40eeaed4d248728` |
| `topics/classicism/lean/Classicism/Results/Research/FiniteSortStructureCertificates.lean` | `7650ae11e6f6e04b457a5931a34163ae8a3582049d32da5186a701e9a09e4a61` |
| `research/2026-10-22/lean-formalization/generate_finite_sort_structure.py` | `3d34d91afe2d64da5c35126b97e5feb422d2271b5cfc535d305dc5f6cad4607b` |

Scope: exhaustive k-entry covers imply Atomicity and Boolean Completeness at a
relational sort, Actuality at t, and Relational Choice from a finite input sort
to **any original output sort, including e**. Fixed k=1,2,3 sources and all twelve
requested translation commands are supplied. There is no Fintype premise or
inferred Functional Choice. Repeated cover entries are handled by a priority
mask. Each larger external bound can be generated in a fresh module using the
script; no claim that all its outputs have been checked. This is external Lean
source generation followed by the existing object-syntax translator, not an
internally verified natural-number-indexed proof generator.

Source: `research/2026-10-22/notes/positive-effective.md` §§23.1–23.3, original
research, unpaginated. The AtMost notation is explicitly defined by an exhaustive
finite cover, equivalent to the usual bound over inhabited sorts; no certificate
of an alternate pigeonhole formulation is included.

Serial check commands, from the bundle root:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteSortStructure --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteSortStructureBounds --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteSortStructureCertificates --timeout 600
```

The certificate driver performs the shallow gate, relational type audit and
translation, and prints the object-derivation axiom dependencies. Success in the
first two commands alone would not certify C derivability. Likely integration
attention: recursive helper unfolding in translation and quotation of arbitrary
output sort τ in the relation-valued finite-choice proof.

Repository validation after this source batch: `classicism: 132 principles, 447
results, 162 models — OK`. This checks records, not Lean proofs.

## Boolean-valued semantics — READY FOR INTEGRATION

These two files are uncompiled proof candidates.

| File (bundle-relative) | SHA256 |
|---|---|
| `topics/classicism/lean/Classicism/Semantics/BooleanValued.lean` | `15f15eae8542d88eb4160466592068a5e346d2b341a531807844e10e54f1e5b1` |
| `topics/classicism/lean/Classicism/Semantics/BooleanValuedSoundness.lean` | `89b477e535bcff730e40d8537f2af2c171da8956220c9fc1301391df8a01c0bb` |

The interpretation covers **all constructors of the existing Term type**,
full function domains, crisp equality, arbitrary meets/joins, and recursive
relational operations. Renaming, lifted substitution, beta/eta/delta conversion,
and one-hole contexts under binders have explicit proofs. Delta at box uses the
exact syntactic top value, then separately proves that value equals Boolean top.

`sound` proves `meet(hypotheses) ≤ value(conclusion)` by the actual `Derivable`
constructors. In Subst, the two logical-only derivations give both inequalities
between P and Q at every environment; antisymmetry and hole congruence handle the
conclusion. Quantified elimination uses Boolean residuation, not a top-valued
witness assumption. `C_axioms_valid` discharges existence from `Nonempty I.E`;
`C_sound` has **no assumed C soundness premise**. Additional corollaries cover
C-minus, non-top non-theorems, unequal closed denotations and falsity.

This is ordinary classical Lean metatheory parameterized by a complete Boolean
algebra. It is not a shallow C certificate and must not undergo the shallow gate.
No forcing, rigidity, selector, Atomicity, or FC conclusion is imported.

Serial commands, after the certificate checker makes the pinned narrow Mathlib import
available to the checker:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.BooleanValued --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.BooleanValuedSoundness --timeout 300
```

**Dependency blocker at submission:** `Mathlib.Order.CompleteBooleanAlgebra` is
not in this workspace's current dependency tree. The current `check_module.py`
rejects missing external imports before compiling. Only the designated compiler
owner may resolve dependencies. Do not read these commands as an assertion that
the present checker can already run them. Likely elaboration attention is the
Mathlib lattice lemma API, implicit environments in quantified rule branches, and
recursive proof termination (pattern follows existing Denotation.sound).

Source provenance is explicit in the files: the source write-up attributes its
construction to Bacon's 9 October 2025 draft, appendix B.2, pp. 7–9; these exact
syntax proofs are new formalization, not a proof attributed to that paper.

## Designated truth — READY FOR INTEGRATION

Frozen file:

| File (bundle-relative) | SHA256 |
|---|---|
| `topics/classicism/lean/Classicism/Semantics/BooleanValuedPoint.lean` | `d318512d676cf9e78cc09cd1d2bec8b86e762186aff5080e203048d2ab2d4cf7` |

The file proves ordinary truth clauses at a nonzero Boolean atom, including
complete primeness: the atom lies below a join iff it lies below one summand.
`sound_at` covers every actual Derivable rule with optional axioms **only
designated true**, rather than top-valued. Its Subst side derivations alone use
the existing Boolean-valued soundness theorem, because their axioms lie in
Logical and Existence has value top. This preserves unboxed premises without
silently necessitating them. It is an uncompiled metatheory candidate.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.BooleanValuedPoint --timeout 300
```

The same unresolved Mathlib dependency applies. The atom assumption does not
supply or assert existence of an atomless algebra, a distinguished product atom,
or the rigid algebra needed by the selector construction.

The Python generator separately passed an AST parse, exact reproduction of the
saved bounds 1–3 source, and expansion-count checks for bounds 1,2,3,8. These are
source-generation checks only, not evidence of Lean/C certification.

## Modal values and kernel report — READY FOR INTEGRATION

Source modules:

| File (bundle-relative) | SHA256 |
|---|---|
| `topics/classicism/lean/Classicism/Semantics/BooleanValuedModal.lean` | `6cf664b9e6bcf11adec5e42db71a950464d2a4b24539a5111de468564dea8914` |
| `topics/classicism/lean/Classicism/Semantics/BooleanValuedChecks.lean` | `9b78513f4500b731581a114b53976ac89a6b751ab42e7b3228119574b308dd9a` |

The modal file supplies literal typed sentences for ND, BF and CBF, matching the
directions in `Principles/Coarse.lean`, and candidate proofs that each and its
box has value top in the full semantics. ND uses nontriviality of B; the BF meet
calculation does not. These formulas are explicitly defined finite syntax, not
silently identified with a generated `.schemaIn` identifier. No claim that ND
or BF is derivable in C is made.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.BooleanValuedModal --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.BooleanValuedChecks --timeout 300
```

The checks file prints kernel axiom dependencies for the central interpretation,
soundness, designated-truth and modal-value theorems. It still needs the same
dependency resolution and actual compiler run. All eight submitted Lean files
were statically scanned: no `sorry`, `admit`, or mathematical `axiom` declaration.

## Author handoff complete

All source files listed above are frozen. This author ran no Lean, lake,
dependency installation/download, additional worker or cross-chat message.
Every edit batch was followed by the required record validator. Last recorded
result: **132 principles, 447 results, 162 models — OK**. Source-generation and
record validation are not Lean verification. No YAML status, generated statement,
original proof or frozen research note was changed.

Still outside this handoff: compiler repair/certification; the bridge from the
explicit ND/BF formulas to generated schema identifiers; a concrete complete
atomless/rigid algebra and its forcing proof; typed selector syntax; concrete
product-algebra/choice/atomicity model verdicts. The Max and other model workers
retain their assigned constructions. The saved soundness proof candidates do
not assume those constructions or use them as evidence.

## Resumed central-negative lane — READY FOR INTEGRATION

The following seven files extend the model construction.

| New file under `topics/classicism/lean/Classicism/` | SHA256 |
|---|---|
| `Semantics/FullPureEquivariance.lean` | `5b3f034cd9bf1873299ce9820712b288892289d9ac5c62d4823d17112c347045` |
| `Semantics/FullExtensionalProperties.lean` | `4e73e6a99ac7ecd9609a28cb27a9e1c3e3397980faec0114b1ee945495ac7c56` |
| `Semantics/FullExtensionalInfinity.lean` | `492f0f5c286df8586d313ce1107f5a0f4c70cf9819cde4dda36305ef154369d5` |
| `Semantics/FullExtensionalCounting.lean` | `a067f44ef0db1bca7d2a0d0d5ce1ae34ade97454ae8820d4fc26f9b70f7a12db` |
| `Models/SinglePredicateFull.lean` | `0c621ae741758b3a8218490599b8c491f0dc035e70b55f67aee2fb9852b0d509` |
| `Models/SinglePredicateCountermodels.lean` | `c69ea056df681589817d87adbeaf75b0084c5aa62be464f35ac20620f6e99baf` |
| `Models/SinglePredicateCountermodelChecks.lean` | `6fa0aec4bacb555cbc879c0e457f2434af31a433d3c9af353a4cca554309eef7` |

**Status:** complete written proof bodies, saved Lean drafts; no compilation or
verified model-certificate claim. Static scan found no sorry/admit/axiom
declaration. Record validation passed after edit batches. The source is
`research/2026-10-22/central-questions-audit.md`, the construction, Independence,
other properties, twelve-row table and signature qualification (unpaginated,
original research, direct source misc).

### What the new sources actually connect

- `FullPureEquivariance` uses the existing `Term.denote`, `Ty.denote`, `RTy.denote`
  and `Env`, imported through **Semantics/Relational**. It proves full typed
  permutation transport, inverse laws, quantifier invariance, every recursive
  relational operation, and equivariance for all constructors including lambda.
  Closed pure predicates are then fixed. This is not merely a subset-action
  lemma or an assumed syntax-equivariance interface.
- `SinglePredicateFull` supplies the **actual admitted signature `{c:e→t}`**,
  concrete Bool/Nat interpretations with c={false}/{0}, and explicit swapping
  permutations. The true `AxiomSet.independence` quantification over lists of
  other constants is eliminated using singleton-signature distinctness. Its
  empty-list instances are discharged by the typed equivariance theorem. C
  validation reuses `C.axioms_holds`; consistency reuses real C soundness.
- `FullExtensionalProperties` proves ordinary semantic lattice atomicity via
  complete predicate coordinates, then validates the existing generated
  **`.quoted` and `.schemaIn`** versions of Extensionality, Atomicity, FC,
  boxed FC, boxed ND/C5, Intensional Choice, and Distinctness Preserving Collapse.
  No Contingency and Modal Freedom are the actual signature schemas. Classical
  metatheoretic choice validates existential FC; it does not enter the syntax as
  a logical choice operator.
- `FullExtensionalInfinity` refutes the **actual n=3 schema sentence**, and
  interprets the generated **quantified Frege Infinity** sentences including
  their impredicative finite-cardinality definition. Two successors of zero
  count Bool and Prop; every finite cardinality on Nat counts only bounded
  subsets, so Nat satisfies individual quantified Infinity. No Fintype-to-C
  bridge is assumed.
- `FullExtensionalCounting` adapts the existing Counting block/tuple proof to
  the ordinary full denotation. It proves the actual counting sentence iff an
  injection from Fin n exists, then validates **all individual Infinity schema
  instances in the Nat model**. It adds the narrow import
  `Mathlib.Data.List.OfFn` (including the Fin.cons/List.ofFn API to be checked).
- `SinglePredicateCountermodels` proves consistency/nonentailment against the
  exact axiom-set unions and builds **complete consistent theories of the two
  actual interpretations**. All four finite Infinity failures hold jointly in
  one Bool theory; individual quantified/schema Infinity and propositional
  schema failure hold jointly in the Nat theory.

All twelve table rows have draft targets, under namespace
`Classicism.Meta.SinglePredicateFull`:

| Audit row | Target theorem |
|---|---|
| C5 3 | `c5_independence_boxedChoice_consistent` |
| C5 5 | `c5_independence_choice_consistent` |
| C5+Atomicity 1 | `c5_atomic_independence_collapse_consistent` |
| C5+Atomicity 2 | `c5_atomic_independence_noContingency_not_schemaInfinity_t` |
| C5+Atomicity 3 | `c5_atomic_independence_intensionalChoice_not_schemaInfinity_t` |
| C5+Atomicity 4 | `c5_atomic_independence_modalFreedom_not_schemaInfinity_t` |
| C5+Atomicity 5 | `c5_atomic_independence_noContingency_not_quantifiedInfinity_t` |
| Extensionalism 1 | `extensional_independence_infinity_consistent` |
| Extensionalism 2 | `extensional_independence_schemaInfinity_consistent` |
| Extensionalism 3 | `extensional_independence_choice_consistent` |
| Extensionalism 4 | `extensional_independence_not_infinity` |
| Extensionalism 5 | `extensional_independence_choice_not_infinity` |

`bool_complete_countermodel` and `nat_complete_countermodel` are the joint
complete-theory targets. The separate `signature_admitted` theorem establishes
that this precise signature is among the map's permitted ones. These are
negative answers to **signature-uniform** claims; no all-signature compatibility
claim is made. No result about the separately assigned gluing models is claimed.

### Serial check targets

Run from the bundle root with the pinned dependencies:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.FullPureEquivariance --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.SinglePredicateFull --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.FullExtensionalProperties --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.FullExtensionalInfinity --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Semantics.FullExtensionalCounting --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.SinglePredicateCountermodels --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.SinglePredicateCountermodelChecks --timeout 300
```

Integration attention: mutual-recursion termination and dependent reductions in
the transport lemmas; the exact generated quotation simplifications, especially
Atomicity and impredicative Infinity; Fin.cons/List.ofFn imports and reduction;
schemaIn membership pattern elaboration. These are explicit proof candidates,
not assumed interfaces. The check driver prints axiom dependencies for the
decisive proofs and all twelve targets. Reject any unexpected mathematical
axiom or sorryAx dependency. These proofs are metatheory, so the shallow gate
and `#classicism_derive` are **not** the appropriate checks.


## Nominal typed foundations — READY FOR INTEGRATION

**Ownership retained:** `model_interpretation.02` (finite-support nominal
classification) and `model_interpretation.03` (larger support/world geometry).
**Both exact main classifications remain incomplete.** This is a supporting
source batch, not a completed coverage item or an addition to a proved tally.
The earlier frozen one-world and finite-sort submissions remain frozen.

These thirteen new files are now frozen and pass to the sole compiler/integrator.
The author ran no Lean/lake process, installed no dependencies, opened no
preview, and sent no cross-thread message. They are **uncompiled proof
candidates**. The record validator passed after each edit batch; the latest
result was `classicism: 132 principles, 447 results, 162 models — OK`.
A separate static scan found balanced delimiters/comments, available local
imports, and no `sorry`, `admit`, mathematical `axiom`, or `opaque` declaration.
Neither check verifies elaboration, termination, or mathematical correctness.

| File (bundle-relative) | SHA256 at freeze |
|---|---|
| `topics/classicism/lean/Classicism/Models/NominalSupportCore.lean` | `2b733fea0d56664a5a88f4369e11656817671538d9ab35b00ac23e287d22186b` |
| `topics/classicism/lean/Classicism/Models/NominalLogicalOperations.lean` | `716333e719b8c278398bc4cc9ea7980b05476063aa5cbfbad9ca066e1037e98d` |
| `topics/classicism/lean/Classicism/Models/NominalTypedHierarchy.lean` | `b92de64764f9ae0c9de4117ebc9f9b97cf8a8d23c1bfc042d01317cd5d68166b` |
| `topics/classicism/lean/Classicism/Models/NominalSubstitution.lean` | `e74372eb934b904d612f375cf53db4db6420cd8e1c1d0534c844c3d9e28c6ac9` |
| `topics/classicism/lean/Classicism/Models/NominalConversion.lean` | `97208d68f99f7597a8d0d764144c806cac8c7d7d5b58ad0687a35110a143b3a0` |
| `topics/classicism/lean/Classicism/Models/NominalSoundness.lean` | `6ead7534470524d6761a551659032d80dab5912b308efbf902804bb136a964e6` |
| `topics/classicism/lean/Classicism/Models/NominalChoiceInfrastructure.lean` | `4afea38b1b16515edd8b757bcc889a445185ebee74b991e5782bce472cd0ca97` |
| `topics/classicism/lean/Classicism/Models/NominalStabilizerCriterion.lean` | `c9abec836c0115519dc1d30ab6ef4d4e23cbfea0e9c3f76913edfcec9f76799d` |
| `topics/classicism/lean/Classicism/Models/NominalOrbitShift.lean` | `a7d73d4fe07582fe8814d840317be0ab0ad6f4c31dbae690de10aae7edb9c17c` |
| `topics/classicism/lean/Classicism/Models/NominalFiniteStrata.lean` | `59bbec34485dc4a144a66ddd9b1c006f2487afa69c301dab57d8d5b02d2564ca` |
| `topics/classicism/lean/Classicism/Models/NominalWorldExamples.lean` | `80bfc867bb153244310892ab8ffbf243bc54e45e33ac6ab0589435f66f9cad6a` |
| `topics/classicism/lean/Classicism/Models/NominalC5.lean` | `b5a19e43388cf16b3c426964116d4c4869a2445e5108ae5e10c928f7f0825766` |
| `topics/classicism/lean/Classicism/Models/NominalFoundationChecks.lean` | `b2fa8921d4cb4683f2dc122325f06d055ca1943cde4dc85b4eeb2b9e6d945491` |

### Concrete implemented obligations in this draft

- `NominalSupportCore`: generic group actions, support ideals with only empty,
  subset, binary-union and translated-image closure; concrete finite and
  countable ideals; **all** supported elements/functions, product and lambda
  closure, evaluation, equivariant maps and their admitted representations.
  No regularity or countable-union closure is a premise of typed closure.
- `NominalLogicalOperations` and `NominalTypedHierarchy`: actual original
  `Ty`/`RTy` hierarchy, trivial-action E=Nat, supported world propositions,
  every admitted relational arrow, all constructors of the actual `Term`,
  all seven recursive relational operations, and genuine world-membership
  satisfaction. Quantifiers range over the exact supported domains. Box is
  rigid equality with the everywhere-true proposition.
- `NominalSubstitution`, `NominalConversion`, `NominalSoundness`: actual
  renaming, lifted substitution, beta/eta/delta conversion, typed holes and
  rule-by-rule `Derivable` soundness. The Subst side derivations are evaluated
  at every world using their logical-only axioms. Proper axioms need hold only
  at the selected world. `NominalC5` names the actual C interface and provides
  a draft certificate for the generated boxed ND instance at every type.
- `NominalChoiceInfrastructure`: admitted relational graph of an external
  world-to-witness function (no forbidden individual-output object type);
  unique witnesses fixed by the joint support/world stabilizer; a least-natural
  selector for arbitrary worlds/support ideals; all-type IC for trivial world
  action. The IC reading connects to the existing generated
  `P.IntensionalChoice.quoted`; individual boxed IC and trivial-world all-type
  IC have actual sentence targets.
- `NominalStabilizerCriterion`: a full proof candidate of the exact per-family
  selector iff common-small-support/stabilizer-fixed-witness criterion. The
  reverse direction chooses support-orbit representatives and witness values,
  constructs transports, proves their independence, proves support, and returns
  an admitted graph. It does not postulate a selector or a reservoir theorem.
- `NominalOrbitShift`: explicit admitted full-domain injective nonsurjective
  operation from a sequence of distinct world orbits; off-sequence inputs are
  fixed. `Hierarchy.dedInfT` is the actual pure existential t→t sentence for
  operational Dedekind infinity, with semantic equivalence and boxed target.
  It is separate from quantified Frege Infinity.
- `NominalFiniteStrata`: the iterate obstruction for a supported injection
  omitting a value. **Finiteness of every fixed-support stratum is an explicit
  conditional premise here, not an established orbit-finiteness theorem.**
- `NominalWorldExamples`: exact Sym(A) atom, trivial-Nat, and tagged-A×Nat
  world actions for the finite/countable ideals; finite Nat atom worlds and
  countably supported (Nat→Bool) atom worlds. Distinct orbit sequences give
  boxed operational DedInf in the trivial and tagged constructions. This does
  not supply the unordered-pair model or its verdicts.
- `NominalFoundationChecks`: axiom-dependency targets for soundness, C/C5,
  exact quoted IC, the stabilizer iff, orbit shifts, finite-strata obstruction,
  and concrete examples. These are classical metatheory, so the shallow-C gate
  and `#classicism_derive` are not appropriate for these proofs.

Signature scope is explicit: the evaluator covers the pure signature and
specified globally fixed constants. Arbitrary non-fixed constant assignments
are not handled by this evaluator. The universal original-type schema targets
in this batch are pure. No stronger all-signature interpretation claim is made.

Sources: `research/2026-10-22/notes/nominal-choice-classification-20261022.md`
§§1–8; `countable-support-choice-countermodel-20261022.md` §§8–9; and
`support-bounds-world-geometry-20261022.md` §§1–5. These are unpaginated original
research notes, direct source category **misc**. Their asserted classification
is not newly accepted merely because the supporting draft exists.

### Serial check commands

Run from the bundle root with the pinned dependencies.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalSupportCore --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalLogicalOperations --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalTypedHierarchy --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalSubstitution --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalConversion --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalSoundness --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalChoiceInfrastructure --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalStabilizerCriterion --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalOrbitShift --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalFiniteStrata --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalWorldExamples --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalC5 --timeout 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.NominalFoundationChecks --timeout 300
```

Integration attention: custom action/coercion elaboration; mutual recursion on
Ty/RTy and Term; implicit context parameters in the substitution/soundness
induction; exact generated quote simplification; the finite/countable Set API,
Nat.find API, and `not_finite` invocation. The full proof bodies are present,
but only the compiler can establish that they elaborate without placeholders.
Reject any unexpected mathematical axiom or `sorryAx` dependency.

### Sequential remaining author queue — exact main obligations

1. Finite Sym(A) support intersection and least supports; their transport;
   orbit representation by injective finite tuples modulo the local finite
   stabilizer; finitely many Fix(S)-orbits for an orbit-finite world set.
2. Derive the nontrivial-world IC positive direction from finite strong orbits
   by the reservoir argument. Derive IC_t failures from local symmetries and
   from infinitely many orbits plus a moving orbit, with explicit admitted
   support-star/finite-set coding families. Use the proved-candidate stabilizer
   criterion rather than assuming equivariant selectors.
3. Establish finite fixed-support proposition strata from the actual finite
   orbit decomposition, discharge `NominalFiniteStrata`'s premise, and extract
   a countable distinct-orbit sequence from an infinite orbit quotient. Then
   certify the exact two-sided DedInf orbit classification.
4. Construct the actual fresh-pair t,t FC and RC counterexamples for every
   nontrivial world action. The RC argument must fix the designated world as
   well as the selector support. Prove the trivial-action positive cases.
5. Complete all-relational-type Atomicity, the standard number fields/full
   ordinary core and both boxed quantified Frege Infinity verdicts when W is
   infinite; construct the unordered-pair example and all four table rows.
6. For `.03`, instantiate the <kappa support ideals with finite-union closure
   without assuming regularity; formalize common reservoirs and strong-world
   stabilizers; successor/regular-limit/singular classifications; the marked
   cofinal-support obstruction; ordered tuple length lambda=mu failure and
   lambda<mu positive case; countable-input selection and the uncountable-bound
   full-domain DedInf operation. None of these cardinal-geometry theorems is
   claimed completed by this foundation batch.

No YAML, generated Statements.lean, source research note, ownership inventory,
or other author's file was edited. Next author work must use new files; these
thirteen frozen sources belong to the integrator for repairs.

## Ownership return and active verification — 23 October 2026

The shared runner has been activated, and repair ownership of this family has
returned to its author. The historical frozen handoffs above are superseded
for ownership, not rewritten as successful checks. The current contribution
summary is [model-foundations-delivery.md](model-foundations-delivery.md),
with current hashes, check manifests and queue state in
[the lane update](verification-updates/model_foundations_signature_nominal.json).

SinglePredicateCountermodelChecks is first; NominalFoundationChecks follows.
Two initial five-minute lock waits ended busy without starting a check.
The author is retrying through the shared runner. No raw Lean/Lake or dependency
installation has been used. Three source import/API repairs are described in
the delivery summary and require compiler confirmation.

The existing finite-orbit proof now also has a source implementation in
NominalFiniteOrbitStrata.lean and four added axiom-audit targets. It proves
finite fixed-support proposition strata from finite stabilizer-orbit
representatives and explicitly supplies those representatives for atom worlds.
The resulting actual boxed negation of operational DedInf_t has no remaining
finite-strata premise for that concrete model. These are uncompiled candidates;
the general orbit decomposition and other classification obligations remain.

### Single-predicate main target passed

The complete SinglePredicateCountermodelChecks driver passed in
`checks/20261023T051126488606Z-b00090cd.json`, with current source bytes matching
the captured sources. All twelve central-question targets and the two complete
consistent theory witnesses were audited directly. The 27 printed dependencies
contain only propext, Classical.choice and Quot.sound, or fewer; no sorryAx.
Exact evidence and owned source hashes are in
[singlepredicate-verified-20261023.json](singlepredicate-verified-20261023.json).
The signature remains exactly {c:e→t}; no richer-signature compatibility claim
or database verification promotion has been added.

### Certificate scope

The finite-sort certificate driver and BooleanValuedChecks also passed fresh
locked checks in `checks/20261023T051245030376Z-c1fd79a4.json`; their exact
independent evidence is in
[model-foundations-existing-certificates-20261023.json](model-foundations-existing-certificates-20261023.json).
The final live source closures match all three successful packages.

NominalSupportCore, NominalLogicalOperations, NominalTypedHierarchy and
NominalSubstitution pass in `checks/20261023T053031030293Z-15212e27.json`.
The later conversion source repair and full nominal driver require a successful check. The broader classification remains
incomplete in Lean; no new mathematical obstruction is asserted.
