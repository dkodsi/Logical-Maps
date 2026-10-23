# Proof and certificate index

[Read the results guide](../MAIN-RESULTS.md). This index gives technical evidence for exactly the stated scopes; a checked supporting lemma does not certify a larger theorem. No new Lean compilation was performed for this editorial pass.

## Central implications and separations

<a id="max-atomicity"></a>
### Pure Maximalism excludes propositional Atomicity

C + pure Maximalism + unboxed Atomicity at t is inconsistent.

**Scope:** Original finitary relational language; pure signature; Atomicity is unboxed. The final theorem has no additional selector, coding, rigidity, model-existence or non-theoremhood premise.

**Lean:** Exact main statement checked.

The saved axiom report lists propext, Classical.choice and Quot.sound, with no sorryAx or custom axioms. The proof uses an explicitly attributed Jech–Shelah construction; the new result and implementation retain the notes’ misc attribution. The consistency of Strong Possibility remains a separate question.

Tracked keys: `F11`.

**Proofs:** [max-atomicity-canonical-code-proof.md](../source/research/2026-10-22/lean-formalization/max-atomicity-canonical-code-proof.md) · [max-atomicity-inconsistency-proof.md](../source/research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md)

**Lean sources:** [MaxAtomicityInconsistency.lean](../source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityInconsistency.lean)

**Compiler manifests:** [20261023T054730505817Z-9a834f08.json](../source/research/2026-10-22/lean-formalization/checks/20261023T054730505817Z-9a834f08.json)

**Scope and axiom evidence:** [max-certificate-audit.json](../source/research/2026-10-22/lean-formalization/max-certificate-audit.json) · [Classicism_Results_Research_MaxAtomicityInconsistency.log](../source/research/2026-10-22/lean-formalization/logs/runs/20261023T054730505817Z-9a834f08/Classicism_Results_Research_MaxAtomicityInconsistency.log)

**Principal declarations:**

- `Classicism.Meta.Research.MaxAtomicityInconsistency.maximalism_atomicity_inconsistent`

<a id="choice-completeness"></a>
### Choice and completeness produce Actuality and transversals

Relational Choice from t to t plus Boolean Completeness at tt implies Actuality. All-type Relational Choice plus Boolean Completeness also implies Transversal Choice, with sharper local chain-completeness and countable-completeness/ccc versions in the cited certificates.

**Scope:** C; actual, unboxed premises. No ND or BF is added to the sharp Actuality theorem. The transversal refinements retain their exact point-selection, type and counting-base conditions.

**Lean:** Exact displayed main implications checked.

Relational Choice alone implying Transversal Choice is not settled by this result.

Tracked keys: `F01`, `rigidity.16`, `rigidity.19`.

**Proofs:** [choice-completeness-actuality.md](../source/research/2026-10-22/followup/choice-completeness-actuality.md) · [relational-choice-boolean-completeness-transversal-proof.md](../source/research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md)

**Lean sources:** [ChoiceActualityCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/ChoiceActualityCertificates.lean) · [ChoiceSectionsRetractionsChecks.lean](../source/topics/classicism/lean/Classicism/Results/Research/ChoiceSectionsRetractionsChecks.lean)

**Compiler manifests:** [20261023T053945495916Z-2d579847.json](../source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json)

**Scope and axiom evidence:** [choice_sections_retractions.json](../source/research/2026-10-22/lean-formalization/verification-updates/choice_sections_retractions.json)

**Principal declarations:**

- `Classicism.Research.Choice.choice_completeness_actuality_sharp.derivable`
- `Classicism.Research.Choice.choice_completeness_transversal_sharp.derivable`
- `Classicism.Research.Choice.local_choice_completeness_transversal.derivable`
- `Classicism.Research.Choice.local_choice_countable_ccc_transversal.derivable`

<a id="modal-propagation"></a>
### Strong Leibniz and Rigid Comprehension force modal stability

Strong Leibniz plus Rigid Comprehension entails necessary Strong Leibniz, necessary relational BF, necessary Rigid Comprehension and necessary Boolean Completeness.

**Scope:** Pure C; both initial premises unboxed; comprehension covers every admitted finite argument tuple, including individual and mixed tuples. BF is concluded only for relational types, not e.

**Lean:** Exact full schema checked; legacy-format evidence retained.

The coordinating technical review reported matching historical recursive fingerprints. This legacy manifest lacks the later per-file source map; the release does not pretend to have recomputed its entire historical fingerprint or rerun Lean.

Tracked keys: `F05`, `rigidity.13`.

**Proofs:** [strong-leibniz-rigid-bottom-cut.md](../source/research/2026-10-22/strong-leibniz-rigid-bottom-cut.md) · [modal-propagation.md](../source/research/2026-10-22/followup/modal-propagation.md)

**Lean sources:** [ModalPropagationSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/ModalPropagationSchemas.lean)

**Compiler manifests:** [20261023T030134260568Z.json](../source/research/2026-10-22/lean-formalization/checks/20261023T030134260568Z.json)

**Scope and axiom evidence:** [ModalPropagationAxioms.log](../source/research/2026-10-22/lean-formalization/logs/runs/20261023T030134260568Z/ModalPropagationAxioms.log) · [significant-results.json](../source/research/2026-10-22/lean-formalization/significant-results.json)

**Principal declarations:**

- `Classicism.Meta.Research.ModalPropagation.all_four`

<a id="rigidity-nd-bc"></a>
### Four rigidity principles coincide over local ND and Boolean Completeness

Over C + unboxed ND + Boolean Completeness, Inextensible Comprehension, Rigid Comprehension, Tame Rigidity and Weakly Rigid Power are equivalent as full all-type schemas.

**Scope:** The equivalence uses the full relational type hierarchy; the route to Weakly Rigid Power uses a higher property type. The premises are local, not boxed.

**Lean:** Exact full-schema equivalences checked.

This does not settle whether full Tame Rigidity + Rigid Power implies Weakly Rigid Power without the stated additional assumptions.

Tracked keys: `rigidity.10`.

**Proofs:** [nd-inextensible-comprehension-implies-weak-power.md](../source/research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md) · [old-new-boolean-completeness-and-rigidity-separation.md](../source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md)

**Lean sources:** [RigidityClosureResearchSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchSchemas.lean) · [RigidityClosureResearchClassification.lean](../source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchClassification.lean)

**Compiler manifests:** [20261023T044252100669Z-9b8e2beb.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044252100669Z-9b8e2beb.json)

**Scope and axiom evidence:** [local_rigidity_closure_replacement.json](../source/research/2026-10-22/lean-formalization/verification-updates/local_rigidity_closure_replacement.json)

**Locations:** “Exact classification over ND + BC”; corrected old/new separation

**Principal declarations:**

- `Classicism.Meta.Research.RigidityClosure.ic_rc_equivalent`
- `Classicism.Meta.Research.RigidityClosure.tame_rc_equivalent`
- `Classicism.Meta.Research.RigidityClosure.weak_power_rc_equivalent`

<a id="oldnew-separation"></a>
### Local ND and Boolean Completeness do not give Rigid Comprehension

A concrete model satisfies full local ND and full relational Boolean Completeness, but fails Inextensible Comprehension and Rigid Comprehension at et, Tame Rigidity, and boxed Boolean Completeness at et. BC at et also fails at each specified accessible E-to-O evaluation.

**Scope:** Pure C; ND and BC are unboxed. The complete declaration uses the original old/new construction. No boxed-Rigid-Power or signature-extension verdict is inferred from it.

**Lean:** Complete displayed countermodel checked.

The external even-haecceity family is not admitted in the model and cannot establish failure of BC at E. The corrected local BC proof must accompany any database integration.

Tracked keys: `rigidity.31`.

**Proofs:** [old-new-boolean-completeness-and-rigidity-separation.md](../source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md) · [old-new-boolean-completeness-source-caveat.md](../source/research/2026-10-22/notes/old-new-boolean-completeness-source-caveat.md)

**Lean sources:** [OldNewComplete.lean](../source/topics/classicism/lean/Classicism/Models/OldNewComplete.lean) · [OldNewSeparation.lean](../source/topics/classicism/lean/Classicism/Models/OldNewSeparation.lean)

**Compiler manifests:** [20261023T045855511121Z-2911dd87.json](../source/research/2026-10-22/lean-formalization/checks/20261023T045855511121Z-2911dd87.json)

**Scope and axiom evidence:** [hierarchy_oldnew_colourcollapse.json](../source/research/2026-10-22/lean-formalization/verification-updates/hierarchy_oldnew_colourcollapse.json)

**Principal declarations:**

- `Classicism.Meta.Intensional.OldNew.complete_countermodel`
- `Classicism.Meta.Intensional.OldNew.background_consistent`
- `Classicism.Meta.Intensional.OldNew.not_entails_rc`
- `Classicism.Meta.Intensional.OldNew.not_entails_tame`
- `Classicism.Meta.Intensional.OldNew.not_entails_box_bc`

<a id="logical-necessity-separation"></a>
### Logical Necessity and strong selection laws do not force Actuality

For the concrete one-predicate signature, Logical Necessity + boxed all-type BF + boxed Relational Choice is consistent and does not entail Actuality or Vicinity.

**Scope:** C with the explicitly interpreted one-constant signature. The concrete supported-product model supplies the semantics. The ordinary prose also treats arbitrary set-sized signatures and additional verdicts, which are not all covered by this certificate.

**Lean:** Displayed one-signature countermodel and nonentailments checked.

Exact boxed Tame Rigidity, internal Countable BC, the separate full-BC symmetric-surjection construction, arbitrary-signature extension and moving-individual Infinity variants retain separate obligations.

Tracked keys: `F07`.

**Proofs:** [central-map.md](../source/research/2026-10-22/followup/central-map.md)

**Lean sources:** [CentralSupportedProductChoice.lean](../source/topics/classicism/lean/Classicism/Semantics/Research/CentralSupportedProductChoice.lean) · [CentralSupportedProductVicinity.lean](../source/topics/classicism/lean/Classicism/Semantics/Research/CentralSupportedProductVicinity.lean)

**Compiler manifests:** [20261023T054410104697Z-48120445.json](../source/research/2026-10-22/lean-formalization/checks/20261023T054410104697Z-48120445.json) · [20261023T054809252922Z-5177013d.json](../source/research/2026-10-22/lean-formalization/checks/20261023T054809252922Z-5177013d.json)

**Scope and axiom evidence:** [modal_central_negative_models.json](../source/research/2026-10-22/lean-formalization/verification-updates/modal_central_negative_models.json)

**Principal declarations:**

- `Classicism.Meta.Intensional.Central.OneConstant.package_consistent`
- `Classicism.Meta.Intensional.Central.OneConstant.package_not_entails_actuality`
- `Classicism.Meta.Intensional.Central.OneConstant.package_not_entails_vicinity`

<a id="signature-independence"></a>
### Independence coexists with extensionality and strong Choice

For Σ={c:et}, full one-world models satisfy Independence together with the stated Extensionality/C5/Atomicity/Choice packages and refute the indicated Infinity implications. Two concrete models answer twelve displayed signature-uniform rows.

**Scope:** Exactly the one-predicate signature; either two individuals or natural-number individuals, with a proper nonempty interpretation of c. It is not an existence theorem for every richer fixed signature.

**Lean:** Concrete models and displayed twelve-row applications checked.

Twelve applications reuse two models; they are not twelve unrelated constructions. Completion of these certificates does not certify the separate nominal-world classifications.

Tracked keys: `central.signature_countermodels`.

**Proofs:** [central-questions-audit.md](../source/research/2026-10-22/central-questions-audit.md)

**Lean sources:** [SinglePredicateCountermodelChecks.lean](../source/topics/classicism/lean/Classicism/Models/SinglePredicateCountermodelChecks.lean)

**Compiler manifests:** [20261023T051126488606Z-b00090cd.json](../source/research/2026-10-22/lean-formalization/checks/20261023T051126488606Z-b00090cd.json)

**Scope and axiom evidence:** [model_foundations_signature_nominal.json](../source/research/2026-10-22/lean-formalization/verification-updates/model_foundations_signature_nominal.json)

**Principal declarations:**

- `Classicism.Meta.SinglePredicateFull.bool_complete_countermodel`
- `Classicism.Meta.SinglePredicateFull.nat_complete_countermodel`
- `Classicism.Meta.SinglePredicateFull.extensional_independence_choice_not_infinity`

## Choice, completeness and rigidity

<a id="sections-retractions"></a>
### Choice and Plenitude decompose into Actuality and inverse maps

Functional Choice iff Actuality plus pointwise sections of actual surjections; Plenitude iff Actuality plus pointwise retractions of actual injections. Their necessitated ordinary-splitting formulations, and specified persistence and involution-representation laws, are also checked.

**Scope:** C; splitting source and target types are relational. Functional Choice retains its original admitted input/output scope. Actual inverse equations and necessary inverse equations are distinguished.

**Lean:** Ordinary and necessitated ordinary-splitting equivalences checked; one stronger formulation remains.

Necessary FC iff necessary Actuality plus unboxed strong sections is mathematically proved in the notes but remains a separate Lean obligation. This must not be confused with the checked necessitated ordinary-section equivalence.

Tracked keys: `choice.01`, `choice.02`, `choice.03`, `choice.05`, `choice.06`, `choice.07`.

**Proofs:** [functional-choice-by-sections.md](../source/research/2026-10-22/notes/functional-choice-by-sections.md) · [choice-uniformization.md](../source/research/2026-10-22/notes/choice-uniformization.md)

**Lean sources:** [SectionsRetractionsSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsSchemas.lean) · [SectionsRetractionsBoxedSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsBoxedSchemas.lean)

**Compiler manifests:** [20261023T053945495916Z-2d579847.json](../source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json)

**Scope and axiom evidence:** [choice_sections_retractions.json](../source/research/2026-10-22/lean-formalization/verification-updates/choice_sections_retractions.json)

**Principal declarations:**

- `Classicism.Meta.Research.Splitting.functional_choice_equivalence`
- `Classicism.Meta.Research.Splitting.plenitude_equivalence`
- `Classicism.Meta.Research.Splitting.necessary_choice_equivalence`
- `Classicism.Meta.Research.Splitting.necessary_plenitude_equivalence`

<a id="rigidity-classifications"></a>
### Rigidity has exact power, uniformization and algebraic descriptions

Atomicity + Rigid Comprehension implies Weakly Rigid Power. Full Weakly Rigid Power is equivalent to Tame Rigidity + Rigid Power + bounded future-tameness. Uniform weak/rigid comprehension is equivalent to local ND plus the corresponding weak/rigid comprehension schema.

**Scope:** Pure C, full schemas with nullary and finite-tuple cases. Bounded future-tameness says every future weakly rigid subrelation of an actual rigid bound is rigid. The WRP-to-RP route uses the next property type.

**Lean:** Exact full schemas and stated fragment/retraction certificates checked.

The final four schema reports list propext/Quot.sound. Current normalizer laws are not automatically boxed laws about all future inputs. Full TR + RP alone implying WRP remains distinct.

Tracked keys: `rigidity.02`, `rigidity.08`, `rigidity.11`, `rigidity.12`.

**Proofs:** [maximalism-modal.md](../source/research/2026-10-22/notes/maximalism-modal.md) · [rigidity-by-joins-and-boolean-closure.md](../source/research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md)

**Lean sources:** [RigidityClosureResearchContinuationSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchContinuationSchemas.lean) · [RigidityClosureResearchBounded.lean](../source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchBounded.lean)

**Compiler manifests:** [20261023T044252100669Z-9b8e2beb.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044252100669Z-9b8e2beb.json)

**Scope and axiom evidence:** [local_rigidity_closure_replacement.json](../source/research/2026-10-22/lean-formalization/verification-updates/local_rigidity_closure_replacement.json)

**Principal declarations:**

- `Classicism.Meta.Research.RigidityClosure.atomicity_rc_weak_power`
- `Classicism.Meta.Research.RigidityClosure.weak_power_decomposition_equivalent`
- `Classicism.Meta.Research.RigidityClosure.uniform_weak_equivalent`
- `Classicism.Meta.Research.RigidityClosure.uniform_rigid_equivalent`

<a id="boolean-retractions-choice"></a>
### Complete Boolean retractions characterize necessary Functional Choice

Over C + necessary Plenitude, necessary Functional Choice is equivalent to the schema saying every admitted rigid internally complete Boolean subalgebra of every relational-type Boolean algebra has a complete Boolean retraction.

**Scope:** Internal completeness ranges over admitted families. The all-type requirement is essential; a single canonical membership inclusion per output type suffices for the converse.

**Lean:** Ordinary proof supplied; complete theorem not Lean-certified.

Propositional retractions alone do not imply full Choice: the notes give a nominal model with all such retractions but failure of Relational Choice. These are different from ordinary surjection-section decompositions.

Tracked keys: `world_algebra.12`.

**Proofs:** [structural-algebraic-core.md](../source/research/2026-10-22/notes/structural-algebraic-core.md)

**Locations:** §§16,18–19,38

<a id="countable-boolean-finiteness"></a>
### Internal countability plus countable completeness forces finiteness

In bare C, an internally countable relational Boolean type is countably complete iff it is internally Frege-finite. Consequently internal countability plus the matching Countable Boolean Completeness implies Actuality.

**Scope:** Countability is relative to a specified admitted counting base. No Choice, Infinity, BF, ND or Plenitude premise is required. Internal finiteness does not imply external finiteness.

**Lean:** Ordinary proof supplied; complete theorem not Lean-certified.

Countability must remain a premise: without arithmetic noncollapse at the counting base, a finite Boolean type can have too many elements for the available numerical labels. The unrestricted converse from finiteness to countability is false.

Tracked keys: `rigidity.20`.

**Proofs:** [quotient-abstraction-lane.md](../source/research/2026-10-22/notes/quotient-abstraction-lane.md)

**Locations:** §§21–21.3

<a id="choice-no-finite-basis"></a>
### Full necessary Functional Choice has no finite fixed-type basis

The ordinary proof reports that full boxed Functional Choice cannot be axiomatized over C by finitely many fixed-type closed formulas; it gives strict cofinal and bounded-type-order refinements.

**Scope:** Original relational grammar and ordinary ZFC metatheory, using symmetric forcing and ground Henkin extraction. This does not rule out a finite number of unbounded type schemata.

**Lean:** Positive hierarchy and support lemmas checked; negative main theorem not fully formalized.

The surviving ordinary proof has an author audit, not a complete independent Lean certificate. Do not replace the missing forcing/extraction construction by an assumed finite-fragment-gap premise.

Tracked keys: `F09`.

**Proofs:** [finite-functional-choice.md](../source/research/2026-10-22/followup/finite-functional-choice.md) · [finite-choice-negative-audit.md](../source/research/2026-10-22/lean-formalization/finite-choice-negative-audit.md)

**Lean sources:** [ChoiceFreshColumns.lean](../source/topics/classicism/lean/Classicism/Models/ChoiceFreshColumns.lean)

**Scope and axiom evidence:** [hierarchy_oldnew_colourcollapse.json](../source/research/2026-10-22/lean-formalization/verification-updates/hierarchy_oldnew_colourcollapse.json)

## Arithmetic and evaluation

<a id="arithmetic-foundations"></a>
### Frege number structure and transfer can be separated from stronger model claims

The cited certificates establish the exact successor-noncollapse/bottom-number equivalences, finite-versus-Dedekind-infinite number-field results, and specified number-map/Hume-class and C5-Actuality transfer results.

**Scope:** Internal Frege finite cardinalities at the source's admitted counting types. Domain Infinity, arithmetic noncollapse, the finite-numeral schema and external standardness are different conditions.

**Lean:** Named foundations checked; complete interpretation/conservativity only partly formalized.

External syntax induction/reflection is not an object-C derivation builder or arbitrary-intensional-model truth lemma. The broad first-order arithmetic conservativity and effective-degree classifications are not marked fully formalized here.

Tracked keys: `principles.01`, `principles.02`, `R04`, `model_interpretation.01`.

**Proofs:** [frege-infinity-20261022-1726.md](../source/research/2026-10-22/notes/frege-infinity-20261022-1726.md) · [infinity-core-number-isomorphism.md](../source/research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md)

**Lean sources:** [FregeNoncollapseCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/FregeNoncollapseCertificates.lean) · [C5ActualityNumbersCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/C5ActualityNumbersCertificates.lean) · [FregeHumeClassesCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/FregeHumeClassesCertificates.lean)

**Compiler manifests:** [20261023T052411006203Z-90a4d7dd.json](../source/research/2026-10-22/lean-formalization/checks/20261023T052411006203Z-90a4d7dd.json)

**Scope and axiom evidence:** [infinity_arithmetic_profiles.json](../source/research/2026-10-22/lean-formalization/verification-updates/infinity_arithmetic_profiles.json)

**Principal declarations:**

- `Classicism.Research.FregeNoncollapse.noncollapse_iff_bottom_not_number.derivable`
- `Classicism.Research.FregeNoncollapse.arithmeticI_iff_istar.derivable`
- `Classicism.Research.FregeNoncollapse.finite_numbers_iff_bottom_number.derivable`
- `Classicism.Research.FregeNoncollapse.infinite_numbers_iff_dedekind.derivable`

<a id="evaluators-cores"></a>
### Actual-truth evaluators and current extensional cores

The prose distinguishes six evaluator strengths and constructs Actuality/Gallin extensional cores. Checked certificates include canonical current evaluators, graph normalization/realization, extension-invariant predicate transfer and the canonical current truth bridge.

**Scope:** Current predicates and actual-world codes; a single necessarily correct evaluator is stronger than necessary local existence. No future-domain identification or uniformly boxed quantifier law is silently added.

**Lean:** Substantial exact components checked; entire hierarchy and core interpretation incomplete.

The full arbitrary-Henkin truth induction, Gallin comparison and every strictness countermodel are separate from the checked kernels.

Tracked keys: `choice.08`, `choice.09`, `choice.10`, `choice.12`, `choice.16`, `choice.23`, `R08`.

**Proofs:** [actual-truth-evaluator-ladder.md](../source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md) · [canonical-actual-evaluator.md](../source/research/2026-10-22/proof-refinements/canonical-actual-evaluator.md) · [actuality-world-slice-core.md](../source/research/2026-10-22/notes/actuality-world-slice-core.md)

**Lean sources:** [CanonicalEvaluatorCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/CanonicalEvaluatorCertificates.lean) · [ActualityCoreGraphsCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/ActualityCoreGraphsCertificates.lean) · [ActualityCoreBridgeCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/ActualityCoreBridgeCertificates.lean)

**Compiler manifests:** [20261023T053945495916Z-2d579847.json](../source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json) · [20261023T043023549683Z-0cf20b33.json](../source/research/2026-10-22/lean-formalization/checks/20261023T043023549683Z-0cf20b33.json)

**Scope and axiom evidence:** [world_actuality_gallin.json](../source/research/2026-10-22/lean-formalization/verification-updates/world_actuality_gallin.json)

**Principal declarations:**

- `Classicism.Research.canonicalEvaluator_all.derivable`
- `Classicism.Research.canonicalEvaluator_exists.derivable`
- `Classicism.Research.ActualityCore.graph_normalization_law`
- `Classicism.Research.ActualityCore.canonical_truth_bridge`

<a id="max-predecessor"></a>
### Maximalism forbids a numerical predecessor operation

At every admitted counting type σ, pure Max refutes an operation f satisfying f(S_σ n)=n on all Frege numbers, although Max entails arithmetic noncollapse I_σ and has the definable predecessor graph. C + Plenitude + I_σ supplies such an operation.

**Scope:** Only a left inverse to successor is demanded; specifying f(0)=0 is unnecessary for the negative result. Number types are relational, so the operation type is admitted.

**Lean:** Ordinary proof supplied; complete theorem not Lean-certified.

The obstruction uses two fixed numeral values, ordinary pure Max and necessity of identity. It does not require SP or a Barcan premise.

Tracked keys: `principles.05`, `principles.06`.

**Proofs:** [relational-coding-recursion-20261022.md](../source/research/2026-10-22/notes/relational-coding-recursion-20261022.md)

**Locations:** §38; related cross-base graph/operation results in §§34–35

<a id="arithmetic-comparison"></a>
### Arithmetic and effective strength of the competing theories

The ordinary reports give the stated common first-order arithmetic theory of positive packages, Max's true-Pi1 strengthening, concrete graph-versus-operation obstructions, and conditional effective/model-degree comparisons.

**Scope:** First-order arithmetic conservativity only; counting-base, finite-proof, adequate-code, external-source and consistency assumptions remain. SP's complexity classification is conditional on consistency. Standard-number models are distinct from arbitrary Henkin models.

**Lean:** Selected foundations and metatheorems checked; full broad comparisons not certified.

Existing source claims are collected, not newly independently adjudicated. Literature novelty and the exact external-theorem locators remain separate review items.

Tracked keys: `principles.03`, `principles.04`, `principles.06`, `principles.16`, `principles.18`, `principles.25`.

**Proofs:** [infinity-world-richness-consolidation-20261022.md](../source/research/2026-10-22/notes/infinity-world-richness-consolidation-20261022.md) · [relational-coding-recursion-20261022.md](../source/research/2026-10-22/notes/relational-coding-recursion-20261022.md) · [comparison-handoff-20261022.md](../source/research/2026-10-22/notes/comparison-handoff-20261022.md)

**Scope and axiom evidence:** [infinity_arithmetic_profiles.json](../source/research/2026-10-22/lean-formalization/verification-updates/infinity_arithmetic_profiles.json) · [strong_possibility.json](../source/research/2026-10-22/lean-formalization/verification-updates/strong_possibility.json)

## World structure and probability

<a id="profile-world-algebra"></a>
### Profile Realization and the Boolean structure of worlds

The ordinary notes give world-indexed representations over necessary Plenitude, consistent individual profile-realization strengthenings, relational-input diagonal obstructions, and nominal examples with all finite supported richness ranks but without Functional Choice.

**Scope:** Admitted internal fields; original rigid/possible PR and raw world representation are identified only under the stated background. Supported finite-rank richness is not unrestricted realization at relational input types, nor a quantified Infinity axiom.

**Lean:** Supporting sources and finite/arithmetic kernels; full classifications and models not certified.

PR is a research proposal, distinct from the original Actual Profile principle. B + individual quantified Infinity + PR yields the remaining Infinity instances in the ordinary arguments; PR does not itself supply Functional Choice.

Tracked keys: `world_algebra.01`, `world_algebra.05`, `world_algebra.12`, `world_algebra.25`.

**Proofs:** [world-cardinality-ucp-20261022.md](../source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) · [structural-world-representation.md](../source/research/2026-10-22/notes/structural-world-representation.md) · [structural-algebraic-core.md](../source/research/2026-10-22/notes/structural-algebraic-core.md)

**Scope and axiom evidence:** [world_actuality_gallin.json](../source/research/2026-10-22/lean-formalization/verification-updates/world_actuality_gallin.json)

<a id="probability"></a>
### Faithful probability has an exact finite-fibre condition and type ceiling

Over C + necessary Plenitude + quantified Infinity_e, the ordinary proofs equate faithful probability with admitted finite-fibre numerical labelling of world atoms. Countable Choice for finite fields upgrades this to internal countability. Higher-type probability has a finiteness obstruction.

**Scope:** Internal Dedekind reals and represented families. The weaker local version uses Actuality + Atomicity_t + BC_t + Infinity_e and graph-valued probabilities in the current core; it need not supply an ambient operation or future-stable real codes.

**Lean:** Arithmetic/real/finite-family components checked; main probability equivalences incomplete.

Real multiplication/positive normalization and the full threshold/finite-fibre/interpretation bridges remain. A countably additive replacement exists in the ordinary proof; the original finite-additive state is not thereby shown countably additive.

Tracked keys: `choice.18`, `choice.19`, `R02`, `R05`, `R06`, `R07`, `R09`.

**Proofs:** [choice-free-faithful-probability.md](../source/research/2026-10-22/proof-refinements/choice-free-faithful-probability.md) · [choice-free-probability-type-ceiling.md](../source/research/2026-10-22/proof-refinements/choice-free-probability-type-ceiling.md) · [local-propositional-probability.md](../source/research/2026-10-22/proof-refinements/local-propositional-probability.md)

**Scope and axiom evidence:** [probability_internal_constructions.json](../source/research/2026-10-22/lean-formalization/verification-updates/probability_internal_constructions.json)

## Strong Possibility and language extensions

<a id="sp-criteria"></a>
### Strong Possibility is an exact universal-identity theory

Over C, pure Strong Possibility is equivalent to the schema of all closed pure universal finite-Boolean-identity sentences individually consistent with Max. With Con(Max) retained, SP is consistent iff Max has the restricted finite-disjunction property for existential finite-Boolean-identity sentences.

**Scope:** Universal prefixes and finite Boolean matrices of typed identities; the terms inside those identities may contain quantifiers. Max-consistency is the original metalinguistic side condition. The disjunction property is a criterion, not a proved property of Max.

**Lean:** Universal-core equivalence and the stated conditional disjunction criterion checked; further model constructions remain partial.

No consistency or inconsistency proof for SP is supplied. The separate elementary-extension embedding criterion has an ordinary proof; the full genuine-Henkin construction is not certified by the twelve checked modules.

Tracked keys: `sp_supplement.01`, `sp_supplement.02`, `F13`, `F14`, `F15`.

**Proofs:** [proof-summary.md](../source/research/2026-10-22/lean-formalization/sp-verification/proof-summary.md) · [reflection-universal-core-20261022.md](../source/research/2026-10-22/notes/reflection-universal-core-20261022.md)

**Lean sources:** [StrongPossibilityConsequencesUniversalCore.lean](../source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesUniversalCore.lean) · [StrongPossibilityConsequencesMaxConservativity.lean](../source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesMaxConservativity.lean)

**Compiler manifests:** [20261023T044759304508Z-f503b46f.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044759304508Z-f503b46f.json) · [20261023T044336274999Z-6b5c1cb4.json](../source/research/2026-10-22/lean-formalization/sp-universal-verification/checks/20261023T044336274999Z-6b5c1cb4.json)

**Scope and axiom evidence:** [verification-status.json](../source/research/2026-10-22/lean-formalization/sp-verification/verification-status.json) · [verification-status.md](../source/research/2026-10-22/lean-formalization/sp-verification/verification-status.md)

**Principal declarations:**

- `Classicism.Meta.Research.StrongPossibilityConsequences.UniversalCore.sp_consistent_iff_universal_core`
- `Classicism.Meta.Research.StrongPossibilityConsequences.MaxConservativity.identity_conservative_iff_max_consistent`

<a id="sp-signature-conflict"></a>
### Signature SP entails pure SP exactly when signature SP is inconsistent

For every map-admitted signature Σ, SP(Σ) entails pure SP iff SP(Σ) is inconsistent. More strongly, pure SP is incompatible with signature Max. The reverse implication from pure SP to SP(Σ) holds iff pure SP is inconsistent.

**Scope:** Σ contains at least one relational nonlogical constant; it may be finite or infinite and may also contain individual names. Original finitary syntax and the distinct reference Max theories are retained.

**Lean:** Signature splitting checked; pure-profile consistency construction and full incompatibility equivalence not Lean-certified.

Witness: A is Fregean ∧ ExactlyOneIndividual and U is Atom_t(A). The pure-profile model gives Con(Max(pure)+U); pure SP entails U; two signature-Max instances split A and give ¬U. This proves neither SP theory consistent or inconsistent separately.

Tracked keys: `principles.27`.

**Proofs:** [audit-signature-to-pure-sp-20261022.md](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md) · [audit-signature-conservativity-obstruction-20261022.md](../source/research/2026-10-22/notes/audit-signature-conservativity-obstruction-20261022.md) · [profile-root-construction-20261022.md](../source/research/2026-10-22/notes/profile-root-construction-20261022.md)

**Lean sources:** [StrongPossibilityConsequencesSignatureSplit.lean](../source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSignatureSplit.lean)

**Compiler manifests:** [20261023T044759304508Z-f503b46f.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044759304508Z-f503b46f.json) · [20261023T044336274999Z-6b5c1cb4.json](../source/research/2026-10-22/lean-formalization/sp-universal-verification/checks/20261023T044336274999Z-6b5c1cb4.json)

**Scope and axiom evidence:** [proof-summary.md](../source/research/2026-10-22/lean-formalization/sp-verification/proof-summary.md)

**Locations:** audit-signature-to-pure-sp-20261022.md §§1–5; audit-signature-conservativity-obstruction-20261022.md §§3–6; profile-root-construction-20261022.md §§1–4

**Principal declarations:**

- `Classicism.Meta.Research.StrongPossibilityConsequences.SignatureSplit.maximalist_not_atom_cell`
- `Classicism.Meta.Research.StrongPossibilityConsequences.SignatureSplit.maximalist_add_atom_inconsistent`

<a id="signature-finite-boundary"></a>
### An exact boundary for finite signature extensions

For a proper extension of finite signatures Σ ⊊ Σ′, Max(Σ′) preserves all Max(Σ)-consistent old-language conditions iff the extension adds exactly one individual name, adds no relational constants, and Σ has no individual names.

**Scope:** Signatures contain only constants of the admitted types. This comparative result also discusses signatures outside the map convention. Equal signatures are the trivial preservation case.

**Lean:** Ordinary proof supplied; complete theorem not Lean-certified.

In the negative cases the two SP theories are incompatible, and each direction of entailment is equivalent to inconsistency of its antecedent. In the positive case the larger-language SP entails the smaller-language SP; no reverse SP implication is asserted.

Tracked keys: `principles.12`.

**Proofs:** [audit-signature-to-pure-sp-20261022.md](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

**Locations:** §§6,9

<a id="signature-infinite-reservoir"></a>
### An infinite reserve of names restores conservativity

If Σ ⊆ Σ′ and Σ already has infinitely many constants of every type at which Σ′ adds constants, Max(Σ′) and SP(Σ′) are conservative over the corresponding old-language theories, preserving old-language consistency conditions.

**Scope:** Every proof is finite, so fresh old constants of matching types can replace the finitely many new names it uses. No generic expansion of each individual model is asserted.

**Lean:** Ordinary proof supplied; complete theorem not Lean-certified.



Tracked keys: `principles.13`.

**Proofs:** [audit-signature-to-pure-sp-20261022.md](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

**Locations:** §8

<a id="sp-individual-cardinality"></a>
### SP fixes the actual domain from the number of individual names

If Σ has exactly u < ∞ individual constant symbols, SP(Σ) entails exactly max(1,u) actual individuals. For u ≥ 1 the individual names enumerate the domain bijectively. Pure SP therefore entails exactly one actual individual.

**Scope:** The relational part of Σ may be infinite. This is an actual-domain assertion, not a boxed cardinality claim. No exhaustion claim is made for infinitely many individual names.

**Lean:** Conditional monism/reflection component checked; the required profile models and full finite-name theorem not Lean-certified.

The Max-consistent profile-root cardinality sentence transfers by universal-identity reflection; signature Max makes distinct individual name symbols denote distinct actual individuals. This remains a consequence of SP, not an SP consistency proof.

Tracked keys: `principles.27`.

**Proofs:** [audit-signature-to-pure-sp-20261022.md](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

**Lean sources:** [StrongPossibilityConsequencesSchemas.lean](../source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSchemas.lean)

**Compiler manifests:** [20261023T044759304508Z-f503b46f.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044759304508Z-f503b46f.json) · [20261023T044336274999Z-6b5c1cb4.json](../source/research/2026-10-22/lean-formalization/sp-universal-verification/checks/20261023T044336274999Z-6b5c1cb4.json)

**Scope and axiom evidence:** [proof-summary.md](../source/research/2026-10-22/lean-formalization/sp-verification/proof-summary.md)

**Locations:** §10

<a id="sp-finite-profile-rank"></a>
### Pointed theories determine the finite Boolean intervals forced by SP

For closed pure A, let S_A be the space of complete consistent theories extending C(a)+A for one fresh individual name a. Max + Width_k(A) is consistent iff S_A has at most k members. If S_A has exactly finite k members, pure SP forces exactly k atoms and 2^k elements below A.

**Scope:** k is an external fixed finite number; Width_k excludes k+1 disjoint nonzero subpropositions. When S_A is infinite, Max already refutes each finite width bound.

**Lean:** Ordinary proof supplied; complete theorem not Lean-certified.

The finite-signature notes refine the cell counts using pointed isomorphism orbits. None of the profile models is asserted to satisfy full SP.

Tracked keys: `principles.10`, `principles.11`, `principles.26`, `principles.28`.

**Proofs:** [sp-finite-profile-rank-20261022.md](../source/research/2026-10-22/notes/sp-finite-profile-rank-20261022.md) · [finite-c5-profile-cells-20261022.md](../source/research/2026-10-22/notes/finite-c5-profile-cells-20261022.md) · [finite-c5-signature-cells-20261022.md](../source/research/2026-10-22/notes/finite-c5-signature-cells-20261022.md)

**Locations:** sp-finite-profile-rank-20261022.md §§1–5; finite-c5-profile-cells-20261022.md §§1–8; finite-c5-signature-cells-20261022.md

<a id="sp-barcan-functionality"></a>
### Finite-signature SP refutes Barcan and Functionality at every input type

For every finite signature Σ, including the empty signature, SP(Σ) refutes Barcan at every admitted input type α and every Functionality type instance with input α and relational output β. Explicit counterpredicates and pairs of operations witness the failures.

**Scope:** For an infinite relational signature with finitely many individual names, only the individual-input result is extended by this proof. Relational-input failures use a finite complete signature diagram.

**Lean:** Ordinary proof supplied; complete theorem not Lean-certified.

A failed schema has a counterinstance; not every formula or every pair of operations is a counterexample. Consistency of the SP antecedent remains unresolved.

Tracked keys: `principles.29`.

**Proofs:** [signature-sp-barcan-20261022.md](../source/research/2026-10-22/notes/signature-sp-barcan-20261022.md) · [finite-c5-profile-cells-20261022.md](../source/research/2026-10-22/notes/finite-c5-profile-cells-20261022.md)

**Locations:** signature-sp-barcan-20261022.md §§1–7; finite-c5-profile-cells-20261022.md §9

<a id="sp-arithmetic-reflection"></a>
### Pure SP proves true Π₂ arithmetic, with a sharp conditional boundary

Pure SP proves every true Π⁰₂ arithmetic sentence under the specified pure Frege-arithmetic translation. More generally, if C + I_e proves every standard numeral instance of a fixed pure P(n), SP proves its universal numerical closure. If SP is consistent, some true Π⁰₃ sentence is not an SP theorem.

**Scope:** The one-step ω-rule has C + I_e as its reference theory. It uses external separate finite proofs, not an infinitary object-language formula. It is not an iterated ω-rule for SP.

**Lean:** Ordinary proof supplied; complete theorem not Lean-certified.

The ordinary argument uses the standard-arithmetic Max model and the stated arithmetic interpretation. The upper-bound conclusion retains Con(SP); no standard-arithmetic SP model is supplied.

Tracked keys: `F14`.

**Proofs:** [strong-possibility.md](../source/research/2026-10-22/followup/strong-possibility.md)

**Locations:** “A one-step omega-rule consequence of pure SP”; “Pure SP contains true Pi^0_2 arithmetic”; “The arithmetic correctness bound is sharp if SP is consistent”
