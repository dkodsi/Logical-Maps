# Classicism: delivery synthesis

**Draft for the coordinating root's technical review — 23 October 2026.**

This is an assembly of the existing research, its reported proofs, and its verification evidence. It does not independently settle disputes between sources, accept unfinished proofs, assess novelty in the literature, or replace the result registry. The organizing order follows the saved [significance assessment](../lean-formalization/significant-results.json) and [thematic catalog](../RESULT-CATALOG.md). Final technical assessment and acceptance remain with the coordinating root.

The [complete tracked index](RESULTS.md) and [structured index](results.json) retain 160 keys in the inspected collection snapshot, including conditional and unfinished entries. That is an inventory count, not a count of established independent theorems. Supporting Lean modules, multiple equivalent formulations, and the same countermodel applied to several displayed questions are not additional headline results. This document gives a connected reading route; the index remains the place to find every tracked family.

## 1. Framework and reading conventions

The fixed theory **C** is Bacon–Dorr Classicism in the original relational type grammar: base types e and t, with an arrow σ→τ only when τ is not e. Individual-valued functions are consequently represented by relational graphs. Type schemata are indexed outside the object language. Unless explicitly identified as an infinitary extension, the results below concern the original finitary language.

| Notation | Exact meaning here |
|---|---|
| C5 | C + **□ND**, not merely current ND |
| B | C + **□Plenitude**, equivalently C5 + Atomicity by the recorded results |
| F | C + **□Functional Choice** |
| Quantified Infinity at σ | No internally finite Frege cardinality counts the entire σ-domain; this is stronger than the external schema of arbitrarily large finite lower bounds |
| Represented/internal | Quantification over objects, relations, families and graphs admitted by the model; external powersets and external countability are not silently substituted |
| Local/unboxed | Asserted at the current point; an optional premise is not automatically necessitated |

“Relational Choice,” “Rigid Comprehension,” “Intensional Choice” and “Inextensible Comprehension” are written out because the research notes reuse RC and IC for different principles. Propositional atoms serve as world codes only in the precisely stated representation results. A signature countermodel must interpret the specified constants, not just the pure reduct.

The user's working package is **F plus quantified Infinity at every admitted type**. It is reported here as the selected working hypothesis, not as a uniquely best theory. Profile Realization remains an optional principle to understand and compare. Its consequences should not be discounted merely because some also follow from other assumptions.

Controlling definitions: [topic guide](../../../topics/classicism/AGENTS.md), [framework and notation](../../../topics/classicism/background.md), [quantified individual Infinity](../../../topics/classicism/principles/axiom-of-infinity-e.yaml), [quantified propositional Infinity](../../../topics/classicism/principles/axiom-of-infinity-t.yaml), and [necessary Functional Choice](../../../topics/classicism/principles/necessary-functional-choice-r.yaml).

## 2. Selection, completeness and actual truth

The later follow-up gives an exact connection between two familiar structural principles and Actuality:

> **C + Relational Choice from t to t + Boolean Completeness at tt entails Actuality.** Both premises are unboxed.

Here tt is the type of properties of propositions. The theorem uses neither ND nor BF nor Plenitude. The source's shorter proof first shows that a true represented disjoint join must have a true member. Relational Choice supplies a disjoint refinement of the family of current falsehoods. If Actuality failed, that family would have join top, contradicting the reflection property of disjoint joins. The construction uses a represented functional graph and a guarded Bourbaki–Witt argument; it does not assume that every graph is an operation.

This strengthens the earlier theorem that **all-type Relational Choice + Boolean Completeness entails Transversal Choice**. The transversal proof can further weaken the completeness premise to the relevant represented well-ordered chain joins and isolate the point-selection instance needed. Relational Choice alone implying Transversal Choice remains a separate unresolved claim in this collection.

The proof notes also record two completeness upgrades: the matching Relational Choice instance turns well-ordered-chain completeness into full Boolean Completeness; and matching Relational Choice, Countable Boolean Completeness and the internal countable chain condition imply Boolean Completeness. The counting base and represented-family qualifications must stay attached to the second statement.

**Sources and evidence.** [Sharp Actuality theorem, §§1–8](../followup/choice-completeness-actuality.md), [ordinary proof audit](../followup/choice-completeness-actuality-audit.md), [transversal proof](../notes/relational-choice-boolean-completeness-transversal-proof.md), [guarded refinement](../notes/rc-guarded-progressive-operation.md), and [countable-completeness refinement](../notes/relational-choice-countable-completeness-ccc.md). These new arguments are attributed in their notes to OpenAI Codex / `misc`, not to the published background paper. Tracked families: F01 and rigidity.15–20.

The declaration `Classicism.Research.Choice.choice_completeness_actuality_sharp.derivable` is requested by [ChoiceActualityCertificates](../../../topics/classicism/lean/Classicism/Results/Research/ChoiceActualityCertificates.lean). Its successful module check is recorded in [the 03:13 manifest](../lean-formalization/checks/20261023T031329148765Z.json); the coverage registry labels F01 `certified_exact_family`. This does not certify every later refinement associated with the Choice lane.

## 3. Simpler presentations of familiar principles

### Actual-truth evaluation

An actual-truth evaluator is an operation on propositions that sends every currently true proposition to top and every currently false proposition to bottom. The notes distinguish six levels by whether an evaluator exists, is globally two-valued, is unique, exists anew at each world, or is one fixed evaluator correct everywhere.

| Evaluator requirement | Reported equivalent over C |
|---|---|
| Some operation's top fibre represents current truth | Actuality |
| An ordinary two-valued actual-truth evaluator exists | ND + Actuality |
| Such an evaluator has two-valued outputs necessarily | Gallin Comprehension |
| Exactly one ordinary actual-truth evaluator exists | C5 + Actuality |
| Necessarily, an actual-truth evaluator exists | B |
| One evaluator is necessarily correct | Extensionality |

The [evaluator note](../notes/actual-truth-evaluator-ladder.md) reports strictness between adjacent levels using the specified chain, retract and group constructions. Its opening five-level table is historical: §“The extra modal-scope distinction” inserts B to obtain the six-level version above. In particular, “necessarily there is an evaluator” and “there is an evaluator that necessarily works” have different strengths.

The [canonical-evaluator refinement](../proof-refinements/canonical-actual-evaluator.md) lowers the assumptions needed for current quantifier preservation. An ordinary evaluator already supplies a canonical replacement commuting with each current typed quantifier. Global bivalence is needed to identify an arbitrary supplied evaluator with that replacement. This does **not** establish the stronger universally boxed law for future predicates.

Tracked families: choice.08–11, choice.23 and R08. [CanonicalEvaluatorCertificates](../../../topics/classicism/lean/Classicism/Results/Research/CanonicalEvaluatorCertificates.lean) names `canonicalEvaluator_all.derivable` and `canonicalEvaluator_exists.derivable`; [its successful check](../lean-formalization/checks/20261023T021637568182Z.json) is evidence for those declarations. The registry still treats the aggregate evaluator hierarchy as only partly certified; the countermodel strictness claims have their own obligations.

### Sections, retractions and representation

The [sections proof](../notes/functional-choice-by-sections.md) reports:

- Functional Choice iff Actuality plus pointwise right inverses for actual surjections.
- Necessary Functional Choice iff necessary Actuality plus strong right inverses for actual surjections.
- Plenitude iff Actuality plus pointwise left inverses for actual injections.

Both source and target of these splitting maps are **relational types**. A strong inverse obeys the inverse equation necessarily. The antecedent remains actual surjectivity or injectivity; replacing it with categorical epimorphism changes the statement. The accompanying classification identifies epimorphism with necessary surjectivity.

The [uniformization note](../notes/choice-uniformization.md) and [reversible-comprehension note](../notes/reversible-comprehension-and-algebraic-laws.md) give the related retraction and involution formulations. [Uniform half-comprehension](../notes/uniform-half-comprehension-definitions.md) characterizes Actuality using operation-valued uniform Persistent, Weak Persistent, or Weak Inextensible Comprehension at one relational type. It does not claim the analogous equivalence for full uniform Inextensible Comprehension.

Tracked families: choice.01–07 and catalog.06. The [04:30 sections/retractions manifest](../lean-formalization/checks/20261023T043052042065Z-a1faec80.json) passes [SectionsRetractionsCertificates](../../../topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsCertificates.lean), including `functional_choice_sections.rule`, `plenitude_retractions.rule` and `epi_iff_necessary_surjective.derivable`. These first two declarations are forward implications. The later [strong-retraction certificate](../../../topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsStrongCertificates.lean) also passes in [the 04:48 manifest](../lean-formalization/checks/20261023T044838756253Z-50e18a7f.json): it includes `necessary_injection_iff_retraction.derivable`, its t-source case and the C5 strong-retraction rule. Its finite-tuple/type scope is stated in the source. The [lane report](../lean-formalization/verification-updates/choice_sections_retractions.json) records implemented but unchecked reverse constructions and retains boxed classifications as separate work; these successful certificates must not be presented as verification of all three equivalences.

## 4. Rigidity, modal propagation and the corrected separator

The rigidity papers give algebraic reformulations before adding new axioms. Weak rigidity is reconstruction from current tuple haecceities; rigidity is its necessary counterpart. Existing represented joins preserve weak rigidity already in C. Tame Rigidity is exactly closure of rigid relations under such joins. Intersection, difference, sections and complement yield further characterizations with the precise ND/BF and type qualifications in the [Boolean-closure note](../notes/rigid-boolean-closure.md). The [join and retraction note](../notes/rigidity-by-joins-and-boolean-closure.md) records uniformization and complete Boolean fragment results.

The completed [local-rigidity schema assembly](../../../topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchContinuationSchemas.lean) now certifies four exact statements in the **pure finitary C language**:

| Statement | Principal declaration in `Classicism.Meta.Research.RigidityClosure` |
|---|---|
| Full relational Atomicity + Rigid Comprehension entails full Weakly Rigid Power | `atomicity_rc_weak_power` |
| Full Weakly Rigid Power iff full Tame Rigidity + Rigid Power + bounded future-tameness | `weak_power_decomposition_equivalent` |
| Full uniform weakly rigid comprehension iff full local ND + weakly rigid comprehension | `uniform_weak_equivalent` |
| Full uniform rigid comprehension iff full local ND + rigid comprehension | `uniform_rigid_equivalent` |

Bounded future-tameness says that every future weakly rigid subrelation of an actual rigid bound is rigid; [its exact definition](../../../topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchBounded.lean) fixes the order and placement of the quantifiers and box. The decomposition is an all-schema result: the route from Weakly Rigid Power to Rigid Power uses the next property type. The uniform-comprehension equivalences use **local**, not boxed, ND; nullary and finite-tuple obligations are discharged in the assembly. [The 04:42 manifest](../lean-formalization/checks/20261023T044252100669Z-9b8e2beb.json) records completion and matching source fingerprints, and the coordinating root has reviewed these exact statements. The four final schema axiom reports list `propext` and `Quot.sound`, with no holes reported.

The [same lane report](../lean-formalization/verification-updates/local_rigidity_closure_replacement.json) maps the checked Boolean-fragment and complete-retraction tuple certificates. Their normalizers preserve represented joins under the displayed comprehension instances and ND_t where required. The universal laws are current; no boxed law on all future arguments is inferred. Section closure and separate semantic countermodels are outside this certificate.

One positive implication is particularly useful for connecting the established principles:

> **ND at t + Inextensible Comprehension at τt entails Weakly Rigid Power at τ.**

At schema level this gives ND + Inextensible Comprehension ⇒ Weakly Rigid Power. Over **unboxed ND + Boolean Completeness**, Inextensible Comprehension, Rigid Comprehension, Tame Rigidity and Weakly Rigid Power become equivalent additional assumptions. [Full ordinary proof and typed scope](../notes/nd-inextensible-comprehension-implies-weak-power.md).

### Local structure can force necessary structure

The completed propagation statement in the later source is:

> **Strong Leibniz + Rigid Comprehension entails necessary Strong Leibniz, necessary relational BF, necessary Rigid Comprehension at every admitted tuple, and necessary Boolean Completeness.**

The two starting premises are unboxed. The BF conclusion concerns **relational types**, not e. The [bottom-inclusive rigid-cover proof](../strong-leibniz-rigid-bottom-cut.md) supplies the first modal step; the [follow-up](../followup/modal-propagation.md) uses haecceity codes to handle individual and mixed tuples without assuming individual BF. Including bottom in the world cover and handling those tuples are explicit proof repairs, not optional details.

`Classicism.Meta.Research.ModalPropagation.all_four` in [ModalPropagationSchemas](../../../topics/classicism/lean/Classicism/Results/Research/ModalPropagationSchemas.lean) assembles these exact schema conclusions. [The 03:01 manifest](../lean-formalization/checks/20261023T030134260568Z.json) records successful checks of that module and [its axiom-report driver](../lean-formalization/integration-checks/ModalPropagationAxioms.lean). The registry labels F05 `certified_exact_family`. The weaker-premise countermodel in [the separate propagation note](../followup/propagation-without-barcan-countermodel.md) must not be mistaken for a counterexample to this full theorem.

### Certified central OldNew countermodel

The existing old/new construction, evaluated at E, has:

> **In the pure signature: C + full local (unboxed) ND + full relational Boolean Completeness is consistent and does not entail Inextensible Comprehension or Rigid Comprehension at et, hence does not entail either full schema.**

Thus local ND and full completeness do not supply the rigidity needed by the preceding implications. This is a concrete model result, not an inference from a missing database arrow.

The [corrected ordinary proof](../notes/old-new-boolean-completeness-and-rigidity-separation.md) represents an E-intension by its E-profile and its profile along the canonical old inclusion E→O. Stabilizer invariance of a represented family makes its componentwise unions admitted, giving all-type Boolean Completeness at E. The existing old/new obstruction supplies failure of Inextensible Comprehension at et. At O, completeness fails at et, so the source also distinguishes current BC from boxed BC.

The correction matters: the earlier root BC-failure argument used an external even-haecceity family that is **not admitted**. The [source caveat](../notes/old-new-boolean-completeness-source-caveat.md) must travel with this result. The construction and its earlier verdicts retain their original attribution; the new completeness verification is identified as `misc` in the research note.

The principal Lean statement is `Classicism.Meta.Intensional.OldNew.central_countermodel` in [OldNewSeparation](../../../topics/classicism/lean/Classicism/Models/OldNewSeparation.lean). The same source gives `background_consistent`, `not_theorem_rc_et` and `not_entails_rc`. In that namespace, `model`/`isModel` are supplied by [OldNewBase](../../../topics/classicism/lean/Classicism/Models/OldNewBase.lean), and `root_glbs`/`root_bc` by [OldNewPairs](../../../topics/classicism/lean/Classicism/Models/OldNewPairs.lean), rather than a model-existence assumption. [The successful central run](../lean-formalization/checks/20261023T041530892093Z.json) and [its axiom report](../lean-formalization/logs/runs/20261023T041530892093Z/OldNewSeparationAxioms.log) cover the concrete model and these statements. The coordinating root's technical review confirms this precise scope and a matching historical fingerprint audit. The report lists `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`; ambient Lean Choice is not an extra object-theory Choice premise. No boxed ND/BC or signature-extension result is inferred from this certificate.

The broader rigidity.31 inventory entry also includes Tame Rigidity and combined-assembly work. Its [later check](../lean-formalization/checks/20261023T043027133420Z-0b8af199.json) failed, and the [owner report](../lean-formalization/verification-updates/hierarchy_oldnew_colourcollapse.json) keeps that work separate. A failure in the larger assembly does not itself erase the named central certificate; conversely the central certificate does not certify that entire assembly. Root should reconcile the final source fingerprints before release.

Other model boundaries remain distinct: the [colour-collapse construction](../notes/colour-collapse-entrance.md) reports full Tame Rigidity + boxed BF + boxed Rigid Power at et with failure of Weakly Rigid Power at et. This refutes a **single-type** strengthening; it does not settle full all-type Tame Rigidity + Rigid Power ⇒ Weakly Rigid Power. The [fixed-point entrance construction](../notes/fixed-point-entrance-cone.md) provides a further local/necessary separation, with its own unfinished Lean model obligations.

## 5. Actuality, extensional cores and quantified Infinity

The [Actuality slice](../notes/actuality-world-slice-core.md) interprets current extensional relational Henkin higher-order logic over **all current individuals**, using relations supported below the actual atom. Relational Choice transfers to that core, as does quantified Infinity for the stated original counting sort. Represented local Boolean intervals are complete and atomic; this does not imply ambient Boolean Completeness. The actual atom can disappear later, so the interpretation is current rather than automatically necessary.

The [Gallin core](../notes/gallin-extensional-core.md) uses globally two-valued representatives. Under Gallin Comprehension it is canonically isomorphic to the Actuality slice as a current structure. This does not identify their future domains. A separate [bounded rigid core](../notes/bounded-extensional-core.md) works over a nonempty rigid individual domain under its ND and Rigid Power assumptions.

The later [number-isomorphism refinement](../proof-refinements/infinity-core-number-isomorphism.md) states that **Actuality + quantified Infinity_e** makes the slice's original-to-core number map a bijection preserving literal numerical identity, zero, successor, arithmetic graphs and represented numerical relations. Neither Choice nor BF is assumed. The earlier merely surjective formulation is not the final statement.

The [Infinity report](../notes/infinity-world-richness-consolidation-20261022.md) separately distinguishes domain Infinity from the arithmetic successor-noncollapse condition Iσ. Domain Infinity implies Iσ in C; the converse is reported under C5, with a separating construction for bare C. The [generated-algebra transfer](../notes/c5-generated-algebra-transfer-20261022.md) concerns admitted commuting maps and its stated inverse conditions; it is not unrestricted transfer between arbitrary external structures.

Tracked families: choice.12–17, principles.01–05, model_interpretation.01 and R04. The [world lane report](../lean-formalization/verification-updates/world_actuality_gallin.json) records checked graph normalization, relational-output graph realization, extension-invariant predicate transfer and the current truth-sort bridge in [the 04:30 manifest](../lean-formalization/checks/20261023T043023549683Z-0cf20b33.json). Principal declarations are `graph_normalization_law`, `graph_realization_law`, `predicate_transfer_law` and `canonical_truth_bridge` in the `Classicism.Research.ActualityCore` namespace. Its later report also records membership/substitution progress, while retaining application preservation, conversion, full truth induction and Gallin comparison as separate obligations.

The [arithmetic lane report](../lean-formalization/verification-updates/infinity_arithmetic_profiles.json) now records a passing [FregeNoncollapse certificate](../../../topics/classicism/lean/Classicism/Results/Research/FregeNoncollapseCertificates.lean) in [the 04:42 manifest](../lean-formalization/checks/20261023T044223622850Z-528e6bf0.json). It names `noncollapse_iff_bottom_not_number.derivable`, `arithmeticI_iff_istar.derivable`, `finite_numbers_iff_bottom_number.derivable` and `infinite_numbers_iff_dedekind.derivable`. These exact arithmetic-foundation statements are distinct from a complete arbitrary-syntax interpretation or the reported first-order conservativity theorem.

## 6. Worlds, profiles and Boolean structure

Over B, the [world-representation note](../notes/structural-world-representation.md) codes relational intensions by admitted rigid relations on worlds and tuples. It gives an internal truth lemma and world-times-tuple atomic normal forms. This is an internal representation theorem, not external fullness of every powerset. The [atom refinement](../proof-refinements/atom-normal-form.md) reduces some assumptions and states the exact coordinate-collision condition; uniqueness needs its ND qualification.

### What Profile Realization says

The original individual principle called UCP_e in [the profile note](../notes/world-cardinality-ucp-20261022.md) says that **one property V can possibly have the extension of each rigid individual property**. “PR” is the explanatory shorthand used in this chat. It is a research proposal, not the original database's separate Actual Profile principle.

Over B, §12 gives an equivalent world formulation: every current individual-property extension is represented by an atom w, with an individual's V-proposition containing w exactly when the individual belongs to that extension. The unique version demands exactly one representing atom. Outside B, the original rigid/possible formulation and this raw world formulation must not be interchanged without proof.

The reported consequences and limits include:

- Full S5 models with individual domain D and worlds P(D) realize every individual profile exactly once. Finite D is allowed, so PR alone does not force Infinity.
- Over B with quantified individual Infinity, realization yields quantified propositional Infinity; the higher-type transfer then gives all relational Infinity instances. This connects PR to part of the user's baseline without claiming that PR supplies Functional Choice.
- Unrestricted raw realization at a relational **input** type is diagonally impossible already in C. The finite-rank hierarchy instead uses specified supported rigid cores; it is not unrestricted realization at every type.
- Ordinary-ZFC nominal models in §§35–36 satisfy B, both base quantified infinities and even every finite supported realization rank while Functional Choice fails.
- Unique realization at one supported rank cannot simply be combined with realization at the next. The all-finite-rank schema itself must not be substituted for a quantified Infinity axiom.

The [profile source](../notes/world-cardinality-ucp-20261022.md) contains the precise rank definitions, Cantor arguments and model proofs. This draft does not add a new claim about the strength or desirability of PR. The world and model-foundation lane reports still retain substantial representation and nominal-model formalization obligations.

### Further structural classifications

The [algebraic report](../notes/structural-algebraic-core.md) records, over its explicitly stated B background, complete subalgebras as world partitions, complete Boolean homomorphisms as contravariant world maps, and normal modal operators as represented world relations. Complete Boolean retractions onto all admitted complete subalgebras characterize necessary Functional Choice, with the stated all-type scope. Finite Boolean retractions instead lead to ultrafilter-valued Choice and the separate filter-extension/BPI factorization.

These classifications are indexed as world_algebra.01–19. They include canonical configuration algebras, uniform complete evaluators and world well-orderability. Their primary proofs and exact side conditions remain in the [representation](../notes/structural-world-representation.md), [algebraic](../notes/structural-algebraic-core.md) and [mixing](../notes/structural-mixing-models.md) sources. The registry reports no complete principal Lean implementation for several of these classifications; associated generic algebra modules do not certify them.

The opposite BPI-factor separation uses a literature-dependent Howard–Tachtsis ZFA input, unlike the direct pair-flip construction for the other direction. The source explicitly lacks the exact printed page for the cited Remark 4. That bibliographic gap remains a delivery issue, not an independently settled attribution.

## 7. Model separations and the size of Choice

### Logical Necessity without Actuality

The later [supported-product proof](../followup/central-map.md) reports, for every permitted fixed set-sized signature Σ, a model with Logical Necessity, all-type boxed BF and Tame Rigidity, Relational Choice, Countable Boolean Completeness and atomlessness, but without Actuality, Vicinity, Weakly Inextensible Comprehension or Rigid Power. The [separate symmetric-surjection proof](../followup/central-map-complete-gluing.md) obtains Logical Necessity with boxed full BC, BF, Tame Rigidity and Weakly Rigid Power, and still no Actuality or Vicinity; **Relational Choice fails there**.

These are two different constructions. Combining the first one's Choice verdict with the second one's full completeness would contradict the theorem in §2. Moving-individual variants and their quantified Infinity verdicts are separately proved in the sources. The notes report independent agent audits of the ordinary constructions; they do not claim human verification. The [central-model lane](../lean-formalization/verification-updates/modal_central_negative_models.json) is formalizing a concrete one-constant signature first and retains the arbitrary-signature and moving-individual extensions as additional obligations.

### A small signature can answer several displayed questions

The [central-question audit](../central-questions-audit.md) uses Σ = {c:et}, with c interpreted as a proper nonempty subset in a full one-world model. Pure-term permutation equivariance proves the required Independence instances. Two individuals give the finite separator; natural-number individuals give the individual-Infinity variant. These models satisfy Extensionality and necessary Functional Choice while failing the indicated Infinity conclusions.

The argument refutes **signature-uniform** entailments because one permitted signature suffices. It does not establish Independence for every richer prescribed signature; a proposition constant, for example, obstructs this particular one-world construction. Twelve displayed rows reuse these two models and should not be counted as twelve unrelated constructions. The [model-foundations report](../lean-formalization/verification-updates/model_foundations_signature_nominal.json) still retains the main concrete certificates as pending in its inspected report.

### Finite approximations to Functional Choice

The [finite-basis follow-up](../followup/finite-functional-choice.md) reports that full boxed Functional Choice has no finite axiomatization over C by **fixed-type closed formulas**, and gives strict cofinal selector hierarchies and bounded-type-order refinements. This does not exclude a finite number of unbounded type schemata. The proof uses symmetric forcing, preservation of low-type domains and ground Henkin extraction.

The [negative audit](../lean-formalization/finite-choice-negative-audit.md) is an author rereading that reports no gap in that ordinary argument; it is not independent certification. Checked positive cofinality, diagonal reductions, finite-proof support and fresh-column lemmas do not supply the forcing and extraction bridge. The full negative theorem remains unproved in Lean according to the coverage registry. The conditional real-uniformization separator and proposed later alternative in [type-t uniformization](../followup/type-t-uniformization.md) need separate root assessment; this draft does not declare the earlier middle inclusion strict unconditionally.

Other nominal distinctions are collected in [the finite-support classification](../notes/nominal-choice-classification-20261022.md), [larger support bounds](../notes/support-bounds-world-geometry-20261022.md), and [the paired-individual fragment](../followup/choice-paired-atoms-type-fragment.md). Their group actions differ: trivial-action individuals in one construction are not interchangeable with independently flipped individual pairs in another. Tracked families model_interpretation.02–03, world_algebra.20–26 and F04 retain those construction parameters.

## 8. Faithful probability and the exact Choice boundary

The original [probability theorem](../notes/faithful-probability-countable-worlds.md), over F plus quantified Infinity_e and its internal Dedekind reals, equates existence of a faithful finitely additive probability with internal countability of world atoms and the internal countable chain condition. A countably additive faithful replacement exists. It does not assert that every initially supplied finitely additive probability was already countably additive.

The [choice-free refinement](../proof-refinements/choice-free-faithful-probability.md) replaces F by B and identifies the exact weaker condition: an admitted numerical labelling of worlds with **internally finite fibres**. Under B + quantified Infinity_e, existence of a faithful finite-, countable-, or represented-completely-additive probability is equivalent to such a labelling. Countable Choice for finite fields upgrades finite fibres to the injection/countability formulation. The distinction cannot be erased by treating “countable union of finite fields” as automatically countable.

The [canonical atomic-part proof](../proof-refinements/canonical-atomic-probability.md) constructs the completely additive atomic part by finite subsums. [Finite-class averaging](../proof-refinements/canonical-finite-class-symmetrization.md) gives the invariant-state refinement without choosing an enumeration of each class. The [type-ceiling refinement](../proof-refinements/choice-free-probability-type-ceiling.md) proves that an admitted powerset has finite-fibre numerical labelling exactly when its underlying field is internally finite; this yields the higher-type obstructions under the stated B + Infinity background.

The weakest displayed propositional version in [the local-core refinement](../proof-refinements/local-propositional-probability.md) assumes only **Actuality + Atomicity_t + BC_t + quantified Infinity_e** over C. Its probabilities are functional **graphs** valued in the current slice's Dedekind-real codes. It does not claim an ambient operation, globally rigid real codes, or future stability without further premises.

Tracked families: choice.18–22 and R02–03, R05–07, R09. [The probability lane](../lean-formalization/verification-updates/probability_internal_constructions.json) reports checked finite-enumeration and other algebraic helpers, including `ProbabilityFinite.remove_one`, `perm_length`, `enumeration_perm` and `enumeration_subset_length` in [the finite-constructive manifest](../lean-formalization/checks/20261023T043010164526Z-9af95bd5.json). Ordered real multiplication/normalization and the complete internal interpretation remain obligations. No full original-C probability classification is claimed Lean certified here.

## 9. Arithmetic, Maximalism and Strong Possibility

The [Infinity consolidation](../notes/infinity-world-richness-consolidation-20261022.md), §2, reports equality of the ordinary **first-order arithmetic** consequences of the specified positive packages, from C plus the arithmetic-infinity condition through necessary Functional Choice with all-type quantified Infinity. Its extension to the Choice package uses an explicitly cited number-preserving constructibility interpretation. This is not higher-order, modal or profile-cardinality conservativity. The original counting-base and finite-proof qualifications are part of the claim.

The same research reports Max's arithmetic theory as the deductive closure of the common positive arithmetic theory T plus true Π₁ sentences. The [relational-coding report](../notes/relational-coding-recursion-20261022.md), §§34–38, exhibits a concrete representation obstruction: Max permits the current predecessor graph but forbids an admitted operation satisfying the stated predecessor equation on all internal numbers. The collision argument uses possible finite numerical identifications and necessity of identity. Related cross-base graph/operation distinctions and an explicit missing guarded numerical join are reported in the linked sources. This does not show that arithmetic itself is unavailable in Max.

The [effective comparison](../notes/comparison-handoff-20261022.md), [Max degree report](../notes/max-degree.md), [positive effective report](../notes/positive-effective.md) and [SP degree report](../notes/strong-possibility-degree.md) distinguish theoremhood complexity from model-code capacity. The reported Σ₁/Σ₂/Σ₃ and PA-degree classifications retain adequate-code, arithmetic and consistency assumptions. In particular, the SP classification is conditional on consistency; externally standard-number models impose additional requirements and are not silently supplied by an ordinary Henkin model.

The [SP signature audit](../notes/audit-signature-to-pure-sp-20261022.md) keeps pure and signature principles separate. The [SP follow-up](../followup/strong-possibility.md) and [universal-core work](../notes/reflection-universal-core-20261022.md) report reflection, finite Boolean-fragment and algebraic consistency criteria. None is a completed SP consistency construction. The UniversalCore matrix allows arbitrary typed terms, including quantifiers inside identity arguments; it is not a quantifier-free first-order or arithmetic-hierarchy theorem. The corrected [formalization proof summary](../lean-formalization/sp-verification/proof-summary.md) retains that distinction. The disjunction/conservativity equivalences retain Con(Max). Some Lean declarations with names such as `max_consistent` or `sp_consistent_iff_universal_core` have exact metatheoretic hypotheses; their names alone do not settle the original open claims.

The SP verification package has since completed its **twelve original modules**, with the separate 21-declaration CoreAxioms audit. This is a module-completion milestone, not twelve new mathematical results or completion of the 32 broader assigned families. [The final core manifest](../lean-formalization/checks/20261023T044759304508Z-f503b46f.json), [Disjunction manifest](../lean-formalization/sp-universal-verification/checks/20261023T044336274999Z-6b5c1cb4.json), [acceptance ledger](../lean-formalization/sp-verification/verification-status.md) and [reproduction instructions](../lean-formalization/sp-verification/reproduction.md) identify the accepted statements and source fingerprints. The coordinating root confirms the final manifest is complete and current. No `sorryAx` is reported. The shallow `reflected_neg_box` intentionally uses the existing `Classicism.em` rule; its translated C derivation is separately audited with only `propext`/`Quot.sound`. These are different levels of formalization and must not be conflated.

**Infinitary boundary.** The notes separately permit countable conjunction/comprehension resources and derive standardness or incompatibility results under those enlarged languages. The [comparison guide](../notes/comparison-handoff-20261022.md) and [structural guide](../notes/structural-lane-handoff.md) give the scopes. A contradiction after adding genuine infinitary comprehension is not a contradiction in original finitary Max. The [SP verification report](../lean-formalization/verification-updates/strong_possibility.json) expressly classifies `InfinitaryNumerals` as enlarged-syntax metatheory and retains the typed arithmetic bridge as separate work.

**Max + Atomicity is not accepted as settled in this draft.** The [proposed proof](../lean-formalization/max-atomicity-inconsistency-proof.md), [selector audit](../followup/max-atomicity-selector-audit.md) and [verification status](../lean-formalization/max-lean-verification-status.md) must be read together. The checked `split_zero_under_atomicity` and `inconsistent_of_split_not_zero_theorem` in [MaxAtomicitySplitCertificate](../../../topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySplitCertificate.lean) establish a zero identity and a **conditional** reduction. [The successful manifest](../lean-formalization/checks/20261023T043512624964Z-73db32d1.json) does not provide the required bare-C non-theorem certificate. Earlier reports identify finite coding/selector adequacy and a nonzero interpretation as gaps. The later [04:50 owner report](../lean-formalization/verification-updates/maximalism_atomicity.json) reports no newly identified mathematical gap after source audits and points to an authored [final inconsistency module](../../../topics/classicism/lean/Classicism/Results/Research/MaxAtomicityInconsistency.lean), but still sets `full_inconsistency_verified` to false and requires the final dependency closure and axiom audit. This changed report is preserved for root's assessment; the synthesis does not decide whether the earlier obligations have all been discharged.

## 10. Evidence, corrections and review handoff

### How to use the evidence

The [coverage registry](../lean-formalization/coverage-and-ownership.json), [verification protocol](../lean-formalization/VERIFICATION-PROTOCOL.md) and individual [lane reports](RESULTS.md#current-lane-evidence) distinguish ordinary proofs, actual C derivations, semantic models, external metatheorems and supporting infrastructure. Aggregate evidence categories are being reconciled as checks finish; their stale totals are not copied here. The tracked keys include unfinished claims, and no aggregate completion percentage is inferred.

This draft inspected the named sources and saved reports without running Lean, building dependencies, refreshing the generated index, or editing any proof/record. A passing historical manifest applies to its recorded source and dependencies. A live author report can postdate the generated index; conversely a report saying “checked target” can point to a failed attempt. Root should freeze and reconcile the exact accepted source/dependency fingerprints for release.

### Specific corrections to carry into delivery

| Earlier presentation or tempting inference | Required delivery correction |
|---|---|
| Old/new fails BC at E | The corrected proof gives full BC at E; the old even-haecceity family was inadmissible. Failure at O is distinct. |
| Strong Leibniz + Rigid Comprehension only gives boxed Strong Leibniz/BF | The later all-schema certificate also gives boxed Rigid Comprehension and BC; BF remains relational, not individual. |
| Relational Choice + BC ⇒ Actuality is still an open recorded gap | The later F01 proof and certificate must supersede that historical research status in the delivery narrative. YAML absence alone is not contrary evidence. |
| Five evaluator levels | §3 of this draft includes the sixth, necessary-local-evaluation level from the later section of the original note. |
| Probability requires full Functional Choice | The refined criterion uses finite-fibre labels under B, and the local graph-coded version has weaker premises; retain their changed witness conventions. |
| Arbitrarily large finite lower bounds are quantified Infinity | They are different principles; compactness-based schema models do not automatically satisfy the quantified axiom. |
| A checked helper proves its lane's main theorem | Preserve the exact declaration and remaining bridge, especially for finite Choice, probability, model interpretation and Max + Atomicity. |
| A signature-uniform refutation works for every fixed signature | The elementary Independence separator uses Σ={c:et}; the stronger arbitrary-signature gluing claims require their own construction. |
| Pure SP, signature SP and an infinitary enlargement are interchangeable | Each has its own language and reference-theory side conditions. |

### Matters reserved for root's technical review

1. **Proposed Max + Atomicity contradiction (F11):** the headline inventory wording exceeds the accepted certificate. Reconcile the earlier non-theorem/adequacy gap report with the later author report that source audits find no new mathematical gap and the newly authored final module. The synthesis has not adjudicated that change; retain the conditional certificate's scope until root accepts the full argument and final evidence.
2. **Type-t middle strictness (F10):** distinguish the conditional determinacy-based result, the explicitly refuted one-block construction and the later proposed full-automorphism construction in [type-t uniformization](../followup/type-t-uniformization.md). No unconditional resolution is inferred here.
3. **Finite Choice negative theorem (F09):** the source and author audit report a complete ordinary argument, while the Lean forcing/extraction bridge is absent. Root's review should assess that reported argument separately from the certified positive hierarchy.
4. **OldNew aggregate status:** preserve the successful central separator, but do not close Tame Rigidity, the combined assembly or stronger boxed-Rigid-Power statements on that evidence alone. The current source/dependency snapshot needs final reconciliation.
5. **Arithmetic conservativity and effective classifications:** confirm the exact external theorem locators, finite-language translations, counting-base bridges and code assumptions. The draft preserves their source-reported statements without a new independent audit.
6. **Canonical source selection:** the collection contains duplicates, historical temporary-path links and source headers saying “no Lean verification” before later certificates existed. Choose the corrected durable proof for each family, and attach later evidence without rewriting the historical original.
7. **Bibliographic completeness:** retain explicit missing locators, including the Howard–Tachtsis input above. Project discovery, proof simplification and literature novelty are different assessments; no literature-novelty conclusion is made here.

The unresolved boundaries retained for delivery include pure/signature SP consistency; the unaccepted full Max + Atomicity argument; Relational Choice alone ⇒ Transversal Choice; and the full all-type Tame Rigidity + Rigid Power ⇒ Weakly Rigid Power question. These are documentation boundaries for this phase, not instructions to start new conjecture research.

For remaining tracked contributions not expanded here—finite profile cells, signature cardinal bounds, completion spaces, exact degree spectra, Boolean categorical classifications and construction-specific obstruction lemmas—use the preserved IDs and proof links in [RESULTS.md](RESULTS.md). The source collection and current ownership reports, rather than the length of this synthesis, determine delivery coverage.

### Assembly handoff

**The assigned assembly and drafting are complete; this remains a draft for root's technical acceptance.** Only `consolidation/DELIVERY-SYNTHESIS.md` was edited. All local file links were checked, and repository validation passed: 132 principles, 447 results and 162 models. No Lean compiler, dependency installation, index rebuild, preview or new conjecture work was run.

The draft incorporates the root-reviewed OldNew central separator, the completed local-rigidity schema statements and the completed SP module package, alongside the exact limits of their certificates. The main factual reconciliation items are the changed Max–Atomicity gap reports, F10's proposed unconditional separator, the unformalized negative finite-Choice bridge, the remaining whole-interpretation/model certificates and the missing literature locator. These items are documented above with their sources; none was independently adjudicated by this synthesis task. Later author checks can be integrated by the coordinator without reopening those conjectures or treating this draft as a frozen release bundle.
