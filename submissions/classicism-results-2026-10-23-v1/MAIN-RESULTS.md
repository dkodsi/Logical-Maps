# Results and their significance

This submission studies the relationships among Choice, completeness, rigidity, Actuality, arithmetic, world structure and possibility principles. The guide begins with central implications and separations, then develops the structural and model-theoretic results by subject. Mathematical claims and Lean coverage are assessed separately.

There are **26 result entries** in this selective guide and **160 tracked keys** in the [complete catalog](CATALOG.md). Entries overlap and vary in breadth; their number and length do not rank importance or count independent new theorems. The [evidence index](evidence/RESULT-INDEX.md) gives exact declarations, sources, saved checks and remaining obligations.

All claims use the original finitary relational Classicism **C** unless explicitly stated otherwise. **ND** means local Necessity of Distinctness, **BC** Boolean Completeness, **B** C + necessary Plenitude, and **F** C + necessary Functional Choice. Quantified Infinity, an infinity schema and external standardness are distinct. “Ordinary proof” means a written mathematical argument; “checked” means the exact stated scope has saved Lean evidence. Neither implies a human check or literature novelty.

| Area | Main question |
|---|---|
| [Central implications and separations](#central-results) | Which central principles imply one another, and which combinations have countermodels? |
| [Choice, completeness and rigidity](#choice-and-rigidity) | How do inverse maps, Boolean retractions, completeness and propagation conditions characterize the principles? |
| [Arithmetic and evaluation](#arithmetic-and-evaluation) | Which mathematical structures and operations can these theories interpret or represent? |
| [World structure and probability](#worlds-and-probability) | How do world richness, internal cardinality and probability relate to Choice? |
| [Strong Possibility and language extensions](#possibility-and-language) | How does the Max-consistency side condition constrain SP and its behavior under changes of language? |

The main unresolved mathematical boundaries include Relational Choice alone implying Transversal Choice, full Tame Rigidity + Rigid Power implying Weakly Rigid Power, and consistency of pure and signature SP. Incomplete formalizations of supplied ordinary proofs are listed separately in each entry.

<a id="central-results"></a>
## Central implications and separations

Which central principles imply one another, and which combinations have countermodels?

| Result | Lean scope |
|---|---|
| [Pure Maximalism excludes propositional Atomicity](#max-atomicity) | Exact main statement checked |
| [Choice and completeness produce Actuality and transversals](#choice-completeness) | Exact displayed main implications checked |
| [Strong Leibniz and Rigid Comprehension force modal stability](#modal-propagation) | Exact full schema checked; legacy-format evidence retained |
| [Four rigidity principles coincide over local ND and Boolean Completeness](#rigidity-nd-bc) | Exact full-schema equivalences checked |
| [Local ND and Boolean Completeness do not give Rigid Comprehension](#oldnew-separation) | Complete displayed countermodel checked |
| [Logical Necessity and strong selection laws do not force Actuality](#logical-necessity-separation) | Displayed one-signature countermodel and nonentailments checked |
| [Independence coexists with extensionality and strong Choice](#signature-independence) | Concrete models and displayed twelve-row applications checked |

<a id="max-atomicity"></a>
### Pure Maximalism excludes propositional Atomicity

C + pure Maximalism + unboxed Atomicity at t is inconsistent.

**Why it matters.** An exact incompatibility between two major principles: propositional Atomicity cannot be added to pure Maximalism, even without boxing Atomicity.

**Scope.** Original finitary relational language; pure signature; Atomicity is unboxed. The final theorem has no additional selector, coding, rigidity, model-existence or non-theoremhood premise.

**Lean.** Exact main statement checked.

The saved axiom report lists propext, Classical.choice and Quot.sound, with no sorryAx or custom axioms. The proof uses an explicitly attributed Jech–Shelah construction; the new result and implementation retain the notes’ misc attribution. The consistency of Strong Possibility remains a separate question.

**Proof:** [max-atomicity-canonical-code-proof.md](source/research/2026-10-22/lean-formalization/max-atomicity-canonical-code-proof.md) · [max-atomicity-inconsistency-proof.md](source/research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md). [Certificate details](evidence/RESULT-INDEX.md#max-atomicity).

<a id="choice-completeness"></a>
### Choice and completeness produce Actuality and transversals

Relational Choice from t to t plus Boolean Completeness at tt implies Actuality. All-type Relational Choice plus Boolean Completeness also implies Transversal Choice, with sharper local chain-completeness and countable-completeness/ccc versions in the cited certificates.

**Why it matters.** Selection and Boolean completeness together recover an actual-world truth selector and quotient representatives. This identifies what completeness contributes beyond Relational Choice alone.

**Scope.** C; actual, unboxed premises. No ND or BF is added to the sharp Actuality theorem. The transversal refinements retain their exact point-selection, type and counting-base conditions.

**Lean.** Exact displayed main implications checked.

Relational Choice alone implying Transversal Choice is not settled by this result.

**Proof:** [choice-completeness-actuality.md](source/research/2026-10-22/followup/choice-completeness-actuality.md) · [relational-choice-boolean-completeness-transversal-proof.md](source/research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md). [Certificate details](evidence/RESULT-INDEX.md#choice-completeness).

<a id="modal-propagation"></a>
### Strong Leibniz and Rigid Comprehension force modal stability

Strong Leibniz plus Rigid Comprehension entails necessary Strong Leibniz, necessary relational BF, necessary Rigid Comprehension and necessary Boolean Completeness.

**Why it matters.** Two local hypotheses force several necessary principles. The result explains a substantial cluster of arrows in the map instead of treating each arrow separately.

**Scope.** Pure C; both initial premises unboxed; comprehension covers every admitted finite argument tuple, including individual and mixed tuples. BF is concluded only for relational types, not e.

**Lean.** Exact full schema checked; legacy-format evidence retained.

The coordinating technical review reported matching historical recursive fingerprints. This legacy manifest lacks the later per-file source map; the release does not pretend to have recomputed its entire historical fingerprint or rerun Lean.

**Proof:** [strong-leibniz-rigid-bottom-cut.md](source/research/2026-10-22/strong-leibniz-rigid-bottom-cut.md) · [modal-propagation.md](source/research/2026-10-22/followup/modal-propagation.md). [Certificate details](evidence/RESULT-INDEX.md#modal-propagation).

<a id="rigidity-nd-bc"></a>
### Four rigidity principles coincide over local ND and Boolean Completeness

Over C + unboxed ND + Boolean Completeness, Inextensible Comprehension, Rigid Comprehension, Tame Rigidity and Weakly Rigid Power are equivalent as full all-type schemas.

**Why it matters.** Several seemingly different additions to this base express one strength. Combined with the old/new model, this identifies a real extra requirement rather than something already implied by ND + BC.

**Scope.** The equivalence uses the full relational type hierarchy; the route to Weakly Rigid Power uses a higher property type. The premises are local, not boxed.

**Lean.** Exact full-schema equivalences checked.

This does not settle whether full Tame Rigidity + Rigid Power implies Weakly Rigid Power without the stated additional assumptions.

**Proof:** [nd-inextensible-comprehension-implies-weak-power.md](source/research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md) · [old-new-boolean-completeness-and-rigidity-separation.md](source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md). [Certificate details](evidence/RESULT-INDEX.md#rigidity-nd-bc).
Locations: “Exact classification over ND + BC”; corrected old/new separation.

<a id="oldnew-separation"></a>
### Local ND and Boolean Completeness do not give Rigid Comprehension

A concrete model satisfies full local ND and full relational Boolean Completeness, but fails Inextensible Comprehension and Rigid Comprehension at et, Tame Rigidity, and boxed Boolean Completeness at et. BC at et also fails at each specified accessible E-to-O evaluation.

**Why it matters.** Completeness and local stability of identity still leave a rigidity gap. The corrected model supplies the lower side of the four-way equivalence over ND + BC.

**Scope.** Pure C; ND and BC are unboxed. The complete declaration uses the original old/new construction. No boxed-Rigid-Power or signature-extension verdict is inferred from it.

**Lean.** Complete displayed countermodel checked.

The external even-haecceity family is not admitted in the model and cannot establish failure of BC at E. The corrected local BC proof must accompany any database integration.

**Proof:** [old-new-boolean-completeness-and-rigidity-separation.md](source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md) · [old-new-boolean-completeness-source-caveat.md](source/research/2026-10-22/notes/old-new-boolean-completeness-source-caveat.md). [Certificate details](evidence/RESULT-INDEX.md#oldnew-separation).

<a id="logical-necessity-separation"></a>
### Logical Necessity and strong selection laws do not force Actuality

For the concrete one-predicate signature, Logical Necessity + boxed all-type BF + boxed Relational Choice is consistent and does not entail Actuality or Vicinity.

**Why it matters.** Strong selection and modal laws can coexist with failure of Actuality. Logical Necessity therefore does not supply the actual-world structure by itself.

**Scope.** C with the explicitly interpreted one-constant signature. The concrete supported-product model supplies the semantics. The ordinary prose also treats arbitrary set-sized signatures and additional verdicts, which are not all covered by this certificate.

**Lean.** Displayed one-signature countermodel and nonentailments checked.

Exact boxed Tame Rigidity, internal Countable BC, the separate full-BC symmetric-surjection construction, arbitrary-signature extension and moving-individual Infinity variants retain separate obligations.

**Proof:** [central-map.md](source/research/2026-10-22/followup/central-map.md). [Certificate details](evidence/RESULT-INDEX.md#logical-necessity-separation).

<a id="signature-independence"></a>
### Independence coexists with extensionality and strong Choice

For Σ={c:et}, full one-world models satisfy Independence together with the stated Extensionality/C5/Atomicity/Choice packages and refute the indicated Infinity implications. Two concrete models answer twelve displayed signature-uniform rows.

**Why it matters.** Concrete interpretations answer several central signature questions while showing why a result for one specified language must not be promoted to every signature.

**Scope.** Exactly the one-predicate signature; either two individuals or natural-number individuals, with a proper nonempty interpretation of c. It is not an existence theorem for every richer fixed signature.

**Lean.** Concrete models and displayed twelve-row applications checked.

Twelve applications reuse two models; they are not twelve unrelated constructions. Completion of these certificates does not certify the separate nominal-world classifications.

**Proof:** [central-questions-audit.md](source/research/2026-10-22/central-questions-audit.md). [Certificate details](evidence/RESULT-INDEX.md#signature-independence).

<a id="choice-and-rigidity"></a>
## Choice, completeness and rigidity

How do inverse maps, Boolean retractions, completeness and propagation conditions characterize the principles?

| Result | Lean scope |
|---|---|
| [Choice and Plenitude decompose into Actuality and inverse maps](#sections-retractions) | Ordinary and necessitated ordinary-splitting equivalences checked; one stronger formulation remains |
| [Rigidity has exact power, uniformization and algebraic descriptions](#rigidity-classifications) | Exact full schemas and stated fragment/retraction certificates checked |
| [Complete Boolean retractions characterize necessary Functional Choice](#boolean-retractions-choice) | Ordinary proof supplied; complete theorem not Lean-certified |
| [Internal countability plus countable completeness forces finiteness](#countable-boolean-finiteness) | Ordinary proof supplied; complete theorem not Lean-certified |
| [Full necessary Functional Choice has no finite fixed-type basis](#choice-no-finite-basis) | Positive hierarchy and support lemmas checked; negative main theorem not fully formalized |

<a id="sections-retractions"></a>
### Choice and Plenitude decompose into Actuality and inverse maps

Functional Choice iff Actuality plus pointwise sections of actual surjections; Plenitude iff Actuality plus pointwise retractions of actual injections. Their necessitated ordinary-splitting formulations, and specified persistence and involution-representation laws, are also checked.

**Why it matters.** Choice and Plenitude each separate into Actuality and a familiar inverse-map principle. This makes their different strengths easier to compare.

**Scope.** C; splitting source and target types are relational. Functional Choice retains its original admitted input/output scope. Actual inverse equations and necessary inverse equations are distinguished.

**Lean.** Ordinary and necessitated ordinary-splitting equivalences checked; one stronger formulation remains.

Necessary FC iff necessary Actuality plus unboxed strong sections is mathematically proved in the notes but remains a separate Lean obligation. This must not be confused with the checked necessitated ordinary-section equivalence.

**Proof:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md) · [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md). [Certificate details](evidence/RESULT-INDEX.md#sections-retractions).

<a id="rigidity-classifications"></a>
### Rigidity has exact power, uniformization and algebraic descriptions

Atomicity + Rigid Comprehension implies Weakly Rigid Power. Full Weakly Rigid Power is equivalent to Tame Rigidity + Rigid Power + bounded future-tameness. Uniform weak/rigid comprehension is equivalent to local ND plus the corresponding weak/rigid comprehension schema.

**Why it matters.** The decomposition identifies bounded future-tameness as the additional condition relating Weakly Rigid Power to Tame Rigidity plus Rigid Power.

**Scope.** Pure C, full schemas with nullary and finite-tuple cases. Bounded future-tameness says every future weakly rigid subrelation of an actual rigid bound is rigid. The WRP-to-RP route uses the next property type.

**Lean.** Exact full schemas and stated fragment/retraction certificates checked.

The final four schema reports list propext/Quot.sound. Current normalizer laws are not automatically boxed laws about all future inputs. Full TR + RP alone implying WRP remains distinct.

**Proof:** [maximalism-modal.md](source/research/2026-10-22/notes/maximalism-modal.md) · [rigidity-by-joins-and-boolean-closure.md](source/research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md). [Certificate details](evidence/RESULT-INDEX.md#rigidity-classifications).

<a id="boolean-retractions-choice"></a>
### Complete Boolean retractions characterize necessary Functional Choice

Over C + necessary Plenitude, necessary Functional Choice is equivalent to the schema saying every admitted rigid internally complete Boolean subalgebra of every relational-type Boolean algebra has a complete Boolean retraction.

**Why it matters.** This supplies an algebraic characterization of the step from the Plenitude baseline to full Choice. Retractions select representatives of the corresponding equivalence classes of atoms.

**Scope.** Internal completeness ranges over admitted families. The all-type requirement is essential; a single canonical membership inclusion per output type suffices for the converse.

**Lean.** Ordinary proof supplied; complete theorem not Lean-certified.

Propositional retractions alone do not imply full Choice: the notes give a nominal model with all such retractions but failure of Relational Choice. These are different from ordinary surjection-section decompositions.

**Proof:** [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md). [Certificate details](evidence/RESULT-INDEX.md#boolean-retractions-choice).
Locations: §§16,18–19,38.

<a id="countable-boolean-finiteness"></a>
### Internal countability plus countable completeness forces finiteness

In bare C, an internally countable relational Boolean type is countably complete iff it is internally Frege-finite. Consequently internal countability plus the matching Countable Boolean Completeness implies Actuality.

**Why it matters.** This gives a route to Actuality from internal countability and countable completeness, without selection assumptions. It also specifies when countable completeness reduces to internal finiteness.

**Scope.** Countability is relative to a specified admitted counting base. No Choice, Infinity, BF, ND or Plenitude premise is required. Internal finiteness does not imply external finiteness.

**Lean.** Ordinary proof supplied; complete theorem not Lean-certified.

Countability must remain a premise: without arithmetic noncollapse at the counting base, a finite Boolean type can have too many elements for the available numerical labels. The unrestricted converse from finiteness to countability is false.

**Proof:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md). [Certificate details](evidence/RESULT-INDEX.md#countable-boolean-finiteness).
Locations: §§21–21.3.

<a id="choice-no-finite-basis"></a>
### Full necessary Functional Choice has no finite fixed-type basis

The ordinary proof reports that full boxed Functional Choice cannot be axiomatized over C by finitely many fixed-type closed formulas; it gives strict cofinal and bounded-type-order refinements.

**Why it matters.** No finite list of fixed-type demands captures full boxed Functional Choice. The distinction between finitely many formulas and an unbounded type schema is essential.

**Scope.** Original relational grammar and ordinary ZFC metatheory, using symmetric forcing and ground Henkin extraction. This does not rule out a finite number of unbounded type schemata.

**Lean.** Positive hierarchy and support lemmas checked; negative main theorem not fully formalized.

The surviving ordinary proof has an author audit, not a complete independent Lean certificate. Do not replace the missing forcing/extraction construction by an assumed finite-fragment-gap premise.

**Proof:** [finite-functional-choice.md](source/research/2026-10-22/followup/finite-functional-choice.md) · [finite-choice-negative-audit.md](source/research/2026-10-22/lean-formalization/finite-choice-negative-audit.md). [Certificate details](evidence/RESULT-INDEX.md#choice-no-finite-basis).

<a id="arithmetic-and-evaluation"></a>
## Arithmetic and evaluation

Which mathematical structures and operations can these theories interpret or represent?

| Result | Lean scope |
|---|---|
| [Frege number structure and transfer can be separated from stronger model claims](#arithmetic-foundations) | Named foundations checked; complete interpretation/conservativity only partly formalized |
| [Actual-truth evaluators and current extensional cores](#evaluators-cores) | Substantial exact components checked; entire hierarchy and core interpretation incomplete |
| [Maximalism forbids a numerical predecessor operation](#max-predecessor) | Ordinary proof supplied; complete theorem not Lean-certified |
| [Arithmetic and effective strength of the competing theories](#arithmetic-comparison) | Selected foundations and metatheorems checked; full broad comparisons not certified |

<a id="arithmetic-foundations"></a>
### Frege number structure and transfer can be separated from stronger model claims

The cited certificates establish the exact successor-noncollapse/bottom-number equivalences, finite-versus-Dedekind-infinite number-field results, and specified number-map/Hume-class and C5-Actuality transfer results.

**Why it matters.** Arithmetic noncollapse, quantified domain Infinity, and an infinity schema are different resources. The transfer theorems specify what survives changes of counting base or passage to a core.

**Scope.** Internal Frege finite cardinalities at the source's admitted counting types. Domain Infinity, arithmetic noncollapse, the finite-numeral schema and external standardness are different conditions.

**Lean.** Named foundations checked; complete interpretation/conservativity only partly formalized.

External syntax induction/reflection is not an object-C derivation builder or arbitrary-intensional-model truth lemma. The broad first-order arithmetic conservativity and effective-degree classifications are not marked fully formalized here.

**Proof:** [frege-infinity-20261022-1726.md](source/research/2026-10-22/notes/frege-infinity-20261022-1726.md) · [infinity-core-number-isomorphism.md](source/research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md). [Certificate details](evidence/RESULT-INDEX.md#arithmetic-foundations).

<a id="evaluators-cores"></a>
### Actual-truth evaluators and current extensional cores

The prose distinguishes six evaluator strengths and constructs Actuality/Gallin extensional cores. Checked certificates include canonical current evaluators, graph normalization/realization, extension-invariant predicate transfer and the canonical current truth bridge.

**Why it matters.** An evaluator correct now, one correct at a selected world, and one fixed evaluator necessarily correct are different demands. The hierarchy explains why apparently similar definitions of evaluation have different strength.

**Scope.** Current predicates and actual-world codes; a single necessarily correct evaluator is stronger than necessary local existence. No future-domain identification or uniformly boxed quantifier law is silently added.

**Lean.** Substantial exact components checked; entire hierarchy and core interpretation incomplete.

The full arbitrary-Henkin truth induction, Gallin comparison and every strictness countermodel are separate from the checked kernels.

**Proof:** [actual-truth-evaluator-ladder.md](source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md) · [canonical-actual-evaluator.md](source/research/2026-10-22/proof-refinements/canonical-actual-evaluator.md) · [actuality-world-slice-core.md](source/research/2026-10-22/notes/actuality-world-slice-core.md). [Certificate details](evidence/RESULT-INDEX.md#evaluators-cores).

<a id="max-predecessor"></a>
### Maximalism forbids a numerical predecessor operation

At every admitted counting type σ, pure Max refutes an operation f satisfying f(S_σ n)=n on all Frege numbers, although Max entails arithmetic noncollapse I_σ and has the definable predecessor graph. C + Plenitude + I_σ supplies such an operation.

**Why it matters.** A total functional arithmetic graph need not have an intensional operation representing it. This pinpoints how Max can support relational arithmetic while opposing individual Plenitude instances.

**Scope.** Only a left inverse to successor is demanded; specifying f(0)=0 is unnecessary for the negative result. Number types are relational, so the operation type is admitted.

**Lean.** Ordinary proof supplied; complete theorem not Lean-certified.

The obstruction uses two fixed numeral values, ordinary pure Max and necessity of identity. It does not require SP or a Barcan premise.

**Proof:** [relational-coding-recursion-20261022.md](source/research/2026-10-22/notes/relational-coding-recursion-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#max-predecessor).
Locations: §38; related cross-base graph/operation results in §§34–35.

<a id="arithmetic-comparison"></a>
### Arithmetic and effective strength of the competing theories

The ordinary reports give the stated common first-order arithmetic theory of positive packages, Max's true-Pi1 strengthening, concrete graph-versus-operation obstructions, and conditional effective/model-degree comparisons.

**Why it matters.** The comparison distinguishes agreement in first-order arithmetic from agreement about represented operations, modal structure, or the information needed to specify a model.

**Scope.** First-order arithmetic conservativity only; counting-base, finite-proof, adequate-code, external-source and consistency assumptions remain. SP's complexity classification is conditional on consistency. Standard-number models are distinct from arbitrary Henkin models.

**Lean.** Selected foundations and metatheorems checked; full broad comparisons not certified.

Existing source claims are collected, not newly independently adjudicated. Literature novelty and the exact external-theorem locators remain separate review items.

**Proof:** [infinity-world-richness-consolidation-20261022.md](source/research/2026-10-22/notes/infinity-world-richness-consolidation-20261022.md) · [relational-coding-recursion-20261022.md](source/research/2026-10-22/notes/relational-coding-recursion-20261022.md) · [comparison-handoff-20261022.md](source/research/2026-10-22/notes/comparison-handoff-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#arithmetic-comparison).

<a id="worlds-and-probability"></a>
## World structure and probability

How do world richness, internal cardinality and probability relate to Choice?

| Result | Lean scope |
|---|---|
| [Profile Realization and the Boolean structure of worlds](#profile-world-algebra) | Supporting sources and finite/arithmetic kernels; full classifications and models not certified |
| [Faithful probability has an exact finite-fibre condition and type ceiling](#probability) | Arithmetic/real/finite-family components checked; main probability equivalences incomplete |

<a id="profile-world-algebra"></a>
### Profile Realization and the Boolean structure of worlds

The ordinary notes give world-indexed representations over necessary Plenitude, consistent individual profile-realization strengthenings, relational-input diagonal obstructions, and nominal examples with all finite supported richness ranks but without Functional Choice.

**Why it matters.** World richness and Choice are separate dimensions of strength. Individual-profile realization can coexist with failure of Functional Choice, while unrestricted relational-input realization hits a diagonal obstruction.

**Scope.** Admitted internal fields; original rigid/possible PR and raw world representation are identified only under the stated background. Supported finite-rank richness is not unrestricted realization at relational input types, nor a quantified Infinity axiom.

**Lean.** Supporting sources and finite/arithmetic kernels; full classifications and models not certified.

PR is a research proposal, distinct from the original Actual Profile principle. B + individual quantified Infinity + PR yields the remaining Infinity instances in the ordinary arguments; PR does not itself supply Functional Choice.

**Proof:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md). [Certificate details](evidence/RESULT-INDEX.md#profile-world-algebra).

<a id="probability"></a>
### Faithful probability has an exact finite-fibre condition and type ceiling

Over C + necessary Plenitude + quantified Infinity_e, the ordinary proofs equate faithful probability with admitted finite-fibre numerical labelling of world atoms. Countable Choice for finite fields upgrades this to internal countability. Higher-type probability has a finiteness obstruction.

**Why it matters.** Faithful probability is controlled by internal world size, with an exact weaker labelling condition before Choice is added. The obstruction becomes stronger as the event type rises.

**Scope.** Internal Dedekind reals and represented families. The weaker local version uses Actuality + Atomicity_t + BC_t + Infinity_e and graph-valued probabilities in the current core; it need not supply an ambient operation or future-stable real codes.

**Lean.** Arithmetic/real/finite-family components checked; main probability equivalences incomplete.

Real multiplication/positive normalization and the full threshold/finite-fibre/interpretation bridges remain. A countably additive replacement exists in the ordinary proof; the original finite-additive state is not thereby shown countably additive.

**Proof:** [choice-free-faithful-probability.md](source/research/2026-10-22/proof-refinements/choice-free-faithful-probability.md) · [choice-free-probability-type-ceiling.md](source/research/2026-10-22/proof-refinements/choice-free-probability-type-ceiling.md) · [local-propositional-probability.md](source/research/2026-10-22/proof-refinements/local-propositional-probability.md). [Certificate details](evidence/RESULT-INDEX.md#probability).

<a id="possibility-and-language"></a>
## Strong Possibility and language extensions

How does the Max-consistency side condition constrain SP and its behavior under changes of language?

| Result | Lean scope |
|---|---|
| [Strong Possibility is an exact universal-identity theory](#sp-criteria) | Universal-core equivalence and the stated conditional disjunction criterion checked; further model constructions remain partial |
| [Signature SP entails pure SP exactly when signature SP is inconsistent](#sp-signature-conflict) | Signature splitting checked; pure-profile consistency construction and full incompatibility equivalence not Lean-certified |
| [An exact boundary for finite signature extensions](#signature-finite-boundary) | Ordinary proof supplied; complete theorem not Lean-certified |
| [An infinite reserve of names restores conservativity](#signature-infinite-reservoir) | Ordinary proof supplied; complete theorem not Lean-certified |
| [SP fixes the actual domain from the number of individual names](#sp-individual-cardinality) | Conditional monism/reflection component checked; the required profile models and full finite-name theorem not Lean-certified |
| [Pointed theories determine the finite Boolean intervals forced by SP](#sp-finite-profile-rank) | Ordinary proof supplied; complete theorem not Lean-certified |
| [Finite-signature SP refutes Barcan and Functionality at every input type](#sp-barcan-functionality) | Ordinary proof supplied; complete theorem not Lean-certified |
| [Pure SP proves true Π₂ arithmetic, with a sharp conditional boundary](#sp-arithmetic-reflection) | Ordinary proof supplied; complete theorem not Lean-certified |

<a id="sp-criteria"></a>
### Strong Possibility is an exact universal-identity theory

Over C, pure Strong Possibility is equivalent to the schema of all closed pure universal finite-Boolean-identity sentences individually consistent with Max. With Con(Max) retained, SP is consistent iff Max has the restricted finite-disjunction property for existential finite-Boolean-identity sentences.

**Why it matters.** SP can be analyzed through jointly realizable universal identity constraints. Its consistency question becomes a precise restricted disjunction question about Max, rather than an unspecified search for richer worlds.

**Scope.** Universal prefixes and finite Boolean matrices of typed identities; the terms inside those identities may contain quantifiers. Max-consistency is the original metalinguistic side condition. The disjunction property is a criterion, not a proved property of Max.

**Lean.** Universal-core equivalence and the stated conditional disjunction criterion checked; further model constructions remain partial.

No consistency or inconsistency proof for SP is supplied. The separate elementary-extension embedding criterion has an ordinary proof; the full genuine-Henkin construction is not certified by the twelve checked modules.

**Proof:** [proof-summary.md](source/research/2026-10-22/lean-formalization/sp-verification/proof-summary.md) · [reflection-universal-core-20261022.md](source/research/2026-10-22/notes/reflection-universal-core-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#sp-criteria).

<a id="sp-signature-conflict"></a>
### Signature SP entails pure SP exactly when signature SP is inconsistent

For every map-admitted signature Σ, SP(Σ) entails pure SP iff SP(Σ) is inconsistent. More strongly, pure SP is incompatible with signature Max. The reverse implication from pure SP to SP(Σ) holds iff pure SP is inconsistent.

**Why it matters.** Adding names changes which sentences are Max-consistent. Signature SP therefore need not extend pure SP: their demands conflict, and a proof of the proposed arrow would establish inconsistency of its antecedent.

**Scope.** Σ contains at least one relational nonlogical constant; it may be finite or infinite and may also contain individual names. Original finitary syntax and the distinct reference Max theories are retained.

**Lean.** Signature splitting checked; pure-profile consistency construction and full incompatibility equivalence not Lean-certified.

Witness: A is Fregean ∧ ExactlyOneIndividual and U is Atom_t(A). The pure-profile model gives Con(Max(pure)+U); pure SP entails U; two signature-Max instances split A and give ¬U. This proves neither SP theory consistent or inconsistent separately.

**Proof:** [audit-signature-to-pure-sp-20261022.md](source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md) · [audit-signature-conservativity-obstruction-20261022.md](source/research/2026-10-22/notes/audit-signature-conservativity-obstruction-20261022.md) · [profile-root-construction-20261022.md](source/research/2026-10-22/notes/profile-root-construction-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#sp-signature-conflict).
Locations: audit-signature-to-pure-sp-20261022.md §§1–5; audit-signature-conservativity-obstruction-20261022.md §§3–6; profile-root-construction-20261022.md §§1–4.

<a id="signature-finite-boundary"></a>
### An exact boundary for finite signature extensions

For a proper extension of finite signatures Σ ⊊ Σ′, Max(Σ′) preserves all Max(Σ)-consistent old-language conditions iff the extension adds exactly one individual name, adds no relational constants, and Σ has no individual names.

**Why it matters.** This is a classification, not just a failed generic-expansion argument. It isolates the one harmless finite extension and explains the otherwise conflicting SP schemes.

**Scope.** Signatures contain only constants of the admitted types. This comparative result also discusses signatures outside the map convention. Equal signatures are the trivial preservation case.

**Lean.** Ordinary proof supplied; complete theorem not Lean-certified.

In the negative cases the two SP theories are incompatible, and each direction of entailment is equivalent to inconsistency of its antecedent. In the positive case the larger-language SP entails the smaller-language SP; no reverse SP implication is asserted.

**Proof:** [audit-signature-to-pure-sp-20261022.md](source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#signature-finite-boundary).
Locations: §§6,9.

<a id="signature-infinite-reservoir"></a>
### An infinite reserve of names restores conservativity

If Σ ⊆ Σ′ and Σ already has infinitely many constants of every type at which Σ′ adds constants, Max(Σ′) and SP(Σ′) are conservative over the corresponding old-language theories, preserving old-language consistency conditions.

**Why it matters.** Finite-signature nonconservativity and infinite-language conservativity have different mechanisms. The supply of unused names is the exact hypothesis used by this positive result.

**Scope.** Every proof is finite, so fresh old constants of matching types can replace the finitely many new names it uses. No generic expansion of each individual model is asserted.

**Lean.** Ordinary proof supplied; complete theorem not Lean-certified.

**Proof:** [audit-signature-to-pure-sp-20261022.md](source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#signature-infinite-reservoir).
Locations: §8.

<a id="sp-individual-cardinality"></a>
### SP fixes the actual domain from the number of individual names

If Σ has exactly u < ∞ individual constant symbols, SP(Σ) entails exactly max(1,u) actual individuals. For u ≥ 1 the individual names enumerate the domain bijectively. Pure SP therefore entails exactly one actual individual.

**Why it matters.** SP has a much sharper cardinal consequence than an informal plenitude reading suggests. Adding individual names can change the forced actual cardinality and make theories incompatible.

**Scope.** The relational part of Σ may be infinite. This is an actual-domain assertion, not a boxed cardinality claim. No exhaustion claim is made for infinitely many individual names.

**Lean.** Conditional monism/reflection component checked; the required profile models and full finite-name theorem not Lean-certified.

The Max-consistent profile-root cardinality sentence transfers by universal-identity reflection; signature Max makes distinct individual name symbols denote distinct actual individuals. This remains a consequence of SP, not an SP consistency proof.

**Proof:** [audit-signature-to-pure-sp-20261022.md](source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#sp-individual-cardinality).
Locations: §10.

<a id="sp-finite-profile-rank"></a>
### Pointed theories determine the finite Boolean intervals forced by SP

For closed pure A, let S_A be the space of complete consistent theories extending C(a)+A for one fresh individual name a. Max + Width_k(A) is consistent iff S_A has at most k members. If S_A has exactly finite k members, pure SP forces exactly k atoms and 2^k elements below A.

**Why it matters.** The atom obstruction is one case of a general classification. It computes entire finite intervals of the propositional algebra from pointed logical possibilities.

**Scope.** k is an external fixed finite number; Width_k excludes k+1 disjoint nonzero subpropositions. When S_A is infinite, Max already refutes each finite width bound.

**Lean.** Ordinary proof supplied; complete theorem not Lean-certified.

The finite-signature notes refine the cell counts using pointed isomorphism orbits. None of the profile models is asserted to satisfy full SP.

**Proof:** [sp-finite-profile-rank-20261022.md](source/research/2026-10-22/notes/sp-finite-profile-rank-20261022.md) · [finite-c5-profile-cells-20261022.md](source/research/2026-10-22/notes/finite-c5-profile-cells-20261022.md) · [finite-c5-signature-cells-20261022.md](source/research/2026-10-22/notes/finite-c5-signature-cells-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#sp-finite-profile-rank).
Locations: sp-finite-profile-rank-20261022.md §§1–5; finite-c5-profile-cells-20261022.md §§1–8; finite-c5-signature-cells-20261022.md.

<a id="sp-barcan-functionality"></a>
### Finite-signature SP refutes Barcan and Functionality at every input type

For every finite signature Σ, including the empty signature, SP(Σ) refutes Barcan at every admitted input type α and every Functionality type instance with input α and relational output β. Explicit counterpredicates and pairs of operations witness the failures.

**Why it matters.** The failure is type-by-type, including individual inputs, rather than merely failure of an all-type conjunction. Future domains contain values not transported from the actual domain.

**Scope.** For an infinite relational signature with finitely many individual names, only the individual-input result is extended by this proof. Relational-input failures use a finite complete signature diagram.

**Lean.** Ordinary proof supplied; complete theorem not Lean-certified.

A failed schema has a counterinstance; not every formula or every pair of operations is a counterexample. Consistency of the SP antecedent remains unresolved.

**Proof:** [signature-sp-barcan-20261022.md](source/research/2026-10-22/notes/signature-sp-barcan-20261022.md) · [finite-c5-profile-cells-20261022.md](source/research/2026-10-22/notes/finite-c5-profile-cells-20261022.md). [Certificate details](evidence/RESULT-INDEX.md#sp-barcan-functionality).
Locations: signature-sp-barcan-20261022.md §§1–7; finite-c5-profile-cells-20261022.md §9.

<a id="sp-arithmetic-reflection"></a>
### Pure SP proves true Π₂ arithmetic, with a sharp conditional boundary

Pure SP proves every true Π⁰₂ arithmetic sentence under the specified pure Frege-arithmetic translation. More generally, if C + I_e proves every standard numeral instance of a fixed pure P(n), SP proves its universal numerical closure. If SP is consistent, some true Π⁰₃ sentence is not an SP theorem.

**Why it matters.** This exhibits a concrete arithmetic gain over Max and a limit to that gain. The reflection principle is stronger than merely recognizing a list of familiar arithmetic axioms.

**Scope.** The one-step ω-rule has C + I_e as its reference theory. It uses external separate finite proofs, not an infinitary object-language formula. It is not an iterated ω-rule for SP.

**Lean.** Ordinary proof supplied; complete theorem not Lean-certified.

The ordinary argument uses the standard-arithmetic Max model and the stated arithmetic interpretation. The upper-bound conclusion retains Con(SP); no standard-arithmetic SP model is supplied.

**Proof:** [strong-possibility.md](source/research/2026-10-22/followup/strong-possibility.md). [Certificate details](evidence/RESULT-INDEX.md#sp-arithmetic-reflection).
Locations: “A one-step omega-rule consequence of pure SP”; “Pure SP contains true Pi^0_2 arithmetic”; “The arithmetic correctness bound is sharp if SP is consistent”.
