# Main results and Lean status

Release: `classicism-results-2026-10-23-v1`. Evidence captured 2026-10-23T12:40:20.509353+00:00.

All results use the original finitary relational Classicism unless a scope explicitly says otherwise. C5 means C + boxed ND; B means C + boxed Plenitude; F means C + boxed Functional Choice. `Checked` below means a saved successful Lean certificate for the stated scope, not a new compilation during packaging. `Partial` means the whole headline theorem or construction has not been certified. A proposed or conditional claim is not counted as an unconditional theorem.

The strongest change since the early synthesis is the final Max–Atomicity inconsistency certificate. Older source notes are preserved byte for byte; later evidence below supersedes their earlier verification-status prose.

| Result | Lean status |
|---|---|
| [Pure Maximalism excludes propositional Atomicity](#max-atomicity) | Exact main statement checked |
| [Choice and completeness produce Actuality and transversals](#choice-completeness) | Exact displayed main implications checked |
| [Strong Leibniz and Rigid Comprehension force modal stability](#modal-propagation) | Exact full schema checked; legacy-format evidence retained |
| [Local ND and Boolean Completeness do not give Rigid Comprehension](#oldnew-separation) | Complete displayed countermodel checked |
| [Rigidity has exact power, uniformization and algebraic descriptions](#rigidity-classifications) | Exact full schemas and stated fragment/retraction certificates checked |
| [Choice and Plenitude decompose into Actuality and inverse maps](#sections-retractions) | Ordinary and necessitated ordinary-splitting equivalences checked; one stronger formulation remains |
| [Logical Necessity and strong selection laws do not force Actuality](#logical-necessity-separation) | Displayed one-signature countermodel and nonentailments checked |
| [Independence coexists with extensionality and strong Choice](#signature-independence) | Concrete models and displayed twelve-row applications checked |
| [Frege number structure and transfer can be separated from stronger model claims](#arithmetic-foundations) | Named foundations checked; complete interpretation/conservativity only partly formalized |
| [Actual-truth evaluators and current extensional cores](#evaluators-cores) | Substantial exact components checked; entire hierarchy and core interpretation incomplete |
| [Strong Possibility reflection and algebraic criteria](#sp-criteria) | Twelve-module verification package complete; wider SP research remains partial |
| [Full necessary Functional Choice has no finite fixed-type basis](#choice-no-finite-basis) | Positive hierarchy and support lemmas checked; negative main theorem not fully formalized |
| [Faithful probability has an exact finite-fibre condition and type ceiling](#probability) | Arithmetic/real/finite-family components checked; main probability equivalences incomplete |
| [Profile Realization and the Boolean structure of worlds](#profile-world-algebra) | Supporting sources and finite/arithmetic kernels; full classifications and models not certified |
| [Arithmetic and effective strength of the competing theories](#arithmetic-comparison) | Selected foundations and metatheorems checked; full broad comparisons not certified |

<a id="max-atomicity"></a>
## Pure Maximalism excludes propositional Atomicity

**C + pure Maximalism + unboxed Atomicity at t is inconsistent.**

**Scope:** Original finitary relational language; pure signature; Atomicity is unboxed. The final theorem has no additional selector, coding, rigidity, model-existence or non-theoremhood premise.

**Lean:** Exact main statement checked.

This supersedes the earlier conditional-only reports. The final axiom report lists propext, Classical.choice and Quot.sound, with no sorryAx or custom axioms. The proof uses an explicitly attributed Jech–Shelah construction; the new result and implementation retain the notes' misc attribution. This does not prove Strong Possibility consistent or inconsistent.

Trace IDs: `F11`.

Principal declarations:

- `Classicism.Meta.Research.MaxAtomicityInconsistency.maximalism_atomicity_inconsistent`

Prose proofs: [max-atomicity-canonical-code-proof.md](source/research/2026-10-22/lean-formalization/max-atomicity-canonical-code-proof.md) · [max-atomicity-inconsistency-proof.md](source/research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md)

Lean sources: [MaxAtomicityInconsistency.lean](source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityInconsistency.lean)

Compiler manifests: [20261023T054730505817Z-9a834f08.json](source/research/2026-10-22/lean-formalization/checks/20261023T054730505817Z-9a834f08.json)

Audits and status: [max-certificate-audit.json](source/research/2026-10-22/lean-formalization/max-certificate-audit.json) · [Classicism_Results_Research_MaxAtomicityInconsistency.log](source/research/2026-10-22/lean-formalization/logs/runs/20261023T054730505817Z-9a834f08/Classicism_Results_Research_MaxAtomicityInconsistency.log)


<a id="choice-completeness"></a>
## Choice and completeness produce Actuality and transversals

**Relational Choice from t to t plus Boolean Completeness at tt implies Actuality. All-type Relational Choice plus Boolean Completeness also implies Transversal Choice, with sharper local chain-completeness and countable-completeness/ccc versions in the cited certificates.**

**Scope:** C; actual, unboxed premises. No ND or BF is added to the sharp Actuality theorem. The transversal refinements retain their exact point-selection, type and counting-base conditions.

**Lean:** Exact displayed main implications checked.

Relational Choice alone implying Transversal Choice is not settled by this result.

Trace IDs: `F01`, `rigidity.16`, `rigidity.19`.

Principal declarations:

- `Classicism.Research.Choice.choice_completeness_actuality_sharp.derivable`
- `Classicism.Research.Choice.choice_completeness_transversal_sharp.derivable`
- `Classicism.Research.Choice.local_choice_completeness_transversal.derivable`
- `Classicism.Research.Choice.local_choice_countable_ccc_transversal.derivable`

Prose proofs: [choice-completeness-actuality.md](source/research/2026-10-22/followup/choice-completeness-actuality.md) · [relational-choice-boolean-completeness-transversal-proof.md](source/research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md)

Lean sources: [ChoiceActualityCertificates.lean](source/topics/classicism/lean/Classicism/Results/Research/ChoiceActualityCertificates.lean) · [ChoiceSectionsRetractionsChecks.lean](source/topics/classicism/lean/Classicism/Results/Research/ChoiceSectionsRetractionsChecks.lean)

Compiler manifests: [20261023T053945495916Z-2d579847.json](source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json)

Audits and status: [choice_sections_retractions.json](source/research/2026-10-22/lean-formalization/verification-updates/choice_sections_retractions.json)


<a id="modal-propagation"></a>
## Strong Leibniz and Rigid Comprehension force modal stability

**Strong Leibniz plus Rigid Comprehension entails necessary Strong Leibniz, necessary relational BF, necessary Rigid Comprehension and necessary Boolean Completeness.**

**Scope:** Pure C; both initial premises unboxed; comprehension covers every admitted finite argument tuple, including individual and mixed tuples. BF is concluded only for relational types, not e.

**Lean:** Exact full schema checked; legacy-format evidence retained.

The coordinating technical review reported matching historical recursive fingerprints. This legacy manifest lacks the later per-file source map; the release does not pretend to have recomputed its entire historical fingerprint or rerun Lean.

Trace IDs: `F05`, `rigidity.13`.

Principal declarations:

- `Classicism.Meta.Research.ModalPropagation.all_four`

Prose proofs: [strong-leibniz-rigid-bottom-cut.md](source/research/2026-10-22/strong-leibniz-rigid-bottom-cut.md) · [modal-propagation.md](source/research/2026-10-22/followup/modal-propagation.md)

Lean sources: [ModalPropagationSchemas.lean](source/topics/classicism/lean/Classicism/Results/Research/ModalPropagationSchemas.lean)

Compiler manifests: [20261023T030134260568Z.json](source/research/2026-10-22/lean-formalization/checks/20261023T030134260568Z.json)

Audits and status: [ModalPropagationAxioms.log](source/research/2026-10-22/lean-formalization/logs/runs/20261023T030134260568Z/ModalPropagationAxioms.log) · [significant-results.json](source/research/2026-10-22/lean-formalization/significant-results.json)


<a id="oldnew-separation"></a>
## Local ND and Boolean Completeness do not give Rigid Comprehension

**A concrete model satisfies full local ND and full relational Boolean Completeness, but fails Inextensible Comprehension and Rigid Comprehension at et, Tame Rigidity, and boxed Boolean Completeness at et. BC at et also fails at each specified accessible E-to-O evaluation.**

**Scope:** Pure C; ND and BC are unboxed. The complete declaration uses the original old/new construction. No boxed-Rigid-Power or signature-extension verdict is inferred from it.

**Lean:** Complete displayed countermodel checked.

The earlier claim that BC failed at E used an inadmissible external even-haecceity family. Its correction must accompany any database integration. The broader assembly is now checked, superseding its earlier failed attempt.

Trace IDs: `rigidity.31`.

Principal declarations:

- `Classicism.Meta.Intensional.OldNew.complete_countermodel`
- `Classicism.Meta.Intensional.OldNew.background_consistent`
- `Classicism.Meta.Intensional.OldNew.not_entails_rc`
- `Classicism.Meta.Intensional.OldNew.not_entails_tame`
- `Classicism.Meta.Intensional.OldNew.not_entails_box_bc`

Prose proofs: [old-new-boolean-completeness-and-rigidity-separation.md](source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md) · [old-new-boolean-completeness-source-caveat.md](source/research/2026-10-22/notes/old-new-boolean-completeness-source-caveat.md)

Lean sources: [OldNewComplete.lean](source/topics/classicism/lean/Classicism/Models/OldNewComplete.lean) · [OldNewSeparation.lean](source/topics/classicism/lean/Classicism/Models/OldNewSeparation.lean)

Compiler manifests: [20261023T045855511121Z-2911dd87.json](source/research/2026-10-22/lean-formalization/checks/20261023T045855511121Z-2911dd87.json)

Audits and status: [hierarchy_oldnew_colourcollapse.json](source/research/2026-10-22/lean-formalization/verification-updates/hierarchy_oldnew_colourcollapse.json)


<a id="rigidity-classifications"></a>
## Rigidity has exact power, uniformization and algebraic descriptions

**Atomicity + Rigid Comprehension implies Weakly Rigid Power. Full Weakly Rigid Power is equivalent to Tame Rigidity + Rigid Power + bounded future-tameness. Uniform weak/rigid comprehension is equivalent to local ND plus the corresponding weak/rigid comprehension schema.**

**Scope:** Pure C, full schemas with nullary and finite-tuple cases. Bounded future-tameness says every future weakly rigid subrelation of an actual rigid bound is rigid. The WRP-to-RP route uses the next property type.

**Lean:** Exact full schemas and stated fragment/retraction certificates checked.

The final four schema reports list propext/Quot.sound. Current normalizer laws are not automatically boxed laws about all future inputs. Full TR + RP alone implying WRP remains distinct.

Trace IDs: `rigidity.02`, `rigidity.08`, `rigidity.11`, `rigidity.12`.

Principal declarations:

- `Classicism.Meta.Research.RigidityClosure.atomicity_rc_weak_power`
- `Classicism.Meta.Research.RigidityClosure.weak_power_decomposition_equivalent`
- `Classicism.Meta.Research.RigidityClosure.uniform_weak_equivalent`
- `Classicism.Meta.Research.RigidityClosure.uniform_rigid_equivalent`

Prose proofs: [maximalism-modal.md](source/research/2026-10-22/notes/maximalism-modal.md) · [rigidity-by-joins-and-boolean-closure.md](source/research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md)

Lean sources: [RigidityClosureResearchContinuationSchemas.lean](source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchContinuationSchemas.lean) · [RigidityClosureResearchBounded.lean](source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchBounded.lean)

Compiler manifests: [20261023T044252100669Z-9b8e2beb.json](source/research/2026-10-22/lean-formalization/checks/20261023T044252100669Z-9b8e2beb.json)

Audits and status: [local_rigidity_closure_replacement.json](source/research/2026-10-22/lean-formalization/verification-updates/local_rigidity_closure_replacement.json)


<a id="sections-retractions"></a>
## Choice and Plenitude decompose into Actuality and inverse maps

**Functional Choice iff Actuality plus pointwise sections of actual surjections; Plenitude iff Actuality plus pointwise retractions of actual injections. Their necessitated ordinary-splitting formulations, and specified persistence and involution-representation laws, are also checked.**

**Scope:** C; splitting source and target types are relational. Functional Choice retains its original admitted input/output scope. Actual inverse equations and necessary inverse equations are distinguished.

**Lean:** Ordinary and necessitated ordinary-splitting equivalences checked; one stronger formulation remains.

Necessary FC iff necessary Actuality plus unboxed strong sections is mathematically proved in the notes but remains a separate Lean obligation. This must not be confused with the checked necessitated ordinary-section equivalence.

Trace IDs: `choice.01`, `choice.02`, `choice.03`, `choice.05`, `choice.06`, `choice.07`.

Principal declarations:

- `Classicism.Meta.Research.Splitting.functional_choice_equivalence`
- `Classicism.Meta.Research.Splitting.plenitude_equivalence`
- `Classicism.Meta.Research.Splitting.necessary_choice_equivalence`
- `Classicism.Meta.Research.Splitting.necessary_plenitude_equivalence`

Prose proofs: [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md) · [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md)

Lean sources: [SectionsRetractionsSchemas.lean](source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsSchemas.lean) · [SectionsRetractionsBoxedSchemas.lean](source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsBoxedSchemas.lean)

Compiler manifests: [20261023T053945495916Z-2d579847.json](source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json)

Audits and status: [choice_sections_retractions.json](source/research/2026-10-22/lean-formalization/verification-updates/choice_sections_retractions.json)


<a id="logical-necessity-separation"></a>
## Logical Necessity and strong selection laws do not force Actuality

**For the concrete one-predicate signature, Logical Necessity + boxed all-type BF + boxed Relational Choice is consistent and does not entail Actuality or Vicinity.**

**Scope:** C with the explicitly interpreted one-constant signature. The concrete supported-product model supplies the semantics. The ordinary prose also treats arbitrary set-sized signatures and additional verdicts, which are not all covered by this certificate.

**Lean:** Displayed one-signature countermodel and nonentailments checked.

Exact boxed Tame Rigidity, internal Countable BC, the separate full-BC symmetric-surjection construction, arbitrary-signature extension and moving-individual Infinity variants retain separate obligations.

Trace IDs: `F07`.

Principal declarations:

- `Classicism.Meta.Intensional.Central.OneConstant.package_consistent`
- `Classicism.Meta.Intensional.Central.OneConstant.package_not_entails_actuality`
- `Classicism.Meta.Intensional.Central.OneConstant.package_not_entails_vicinity`

Prose proofs: [central-map.md](source/research/2026-10-22/followup/central-map.md)

Lean sources: [CentralSupportedProductChoice.lean](source/topics/classicism/lean/Classicism/Semantics/Research/CentralSupportedProductChoice.lean) · [CentralSupportedProductVicinity.lean](source/topics/classicism/lean/Classicism/Semantics/Research/CentralSupportedProductVicinity.lean)

Compiler manifests: [20261023T054410104697Z-48120445.json](source/research/2026-10-22/lean-formalization/checks/20261023T054410104697Z-48120445.json) · [20261023T054809252922Z-5177013d.json](source/research/2026-10-22/lean-formalization/checks/20261023T054809252922Z-5177013d.json)

Audits and status: [modal_central_negative_models.json](source/research/2026-10-22/lean-formalization/verification-updates/modal_central_negative_models.json)


<a id="signature-independence"></a>
## Independence coexists with extensionality and strong Choice

**For Σ={c:et}, full one-world models satisfy Independence together with the stated Extensionality/C5/Atomicity/Choice packages and refute the indicated Infinity implications. Two concrete models answer twelve displayed signature-uniform rows.**

**Scope:** Exactly the one-predicate signature; either two individuals or natural-number individuals, with a proper nonempty interpretation of c. It is not an existence theorem for every richer fixed signature.

**Lean:** Concrete models and displayed twelve-row applications checked.

Twelve applications reuse two models; they are not twelve unrelated constructions. Completion of these certificates does not certify the separate nominal-world classifications.

Trace IDs: `central.signature_countermodels`.

Principal declarations:

- `Classicism.Meta.SinglePredicateFull.bool_complete_countermodel`
- `Classicism.Meta.SinglePredicateFull.nat_complete_countermodel`
- `Classicism.Meta.SinglePredicateFull.extensional_independence_choice_not_infinity`

Prose proofs: [central-questions-audit.md](source/research/2026-10-22/central-questions-audit.md)

Lean sources: [SinglePredicateCountermodelChecks.lean](source/topics/classicism/lean/Classicism/Models/SinglePredicateCountermodelChecks.lean)

Compiler manifests: [20261023T051126488606Z-b00090cd.json](source/research/2026-10-22/lean-formalization/checks/20261023T051126488606Z-b00090cd.json)

Audits and status: [model_foundations_signature_nominal.json](source/research/2026-10-22/lean-formalization/verification-updates/model_foundations_signature_nominal.json)


<a id="arithmetic-foundations"></a>
## Frege number structure and transfer can be separated from stronger model claims

**The cited certificates establish the exact successor-noncollapse/bottom-number equivalences, finite-versus-Dedekind-infinite number-field results, and specified number-map/Hume-class and C5-Actuality transfer results.**

**Scope:** Internal Frege finite cardinalities at the source's admitted counting types. Domain Infinity, arithmetic noncollapse, the finite-numeral schema and external standardness are different conditions.

**Lean:** Named foundations checked; complete interpretation/conservativity only partly formalized.

External syntax induction/reflection is not an object-C derivation builder or arbitrary-intensional-model truth lemma. The broad first-order arithmetic conservativity and effective-degree classifications are not marked fully formalized here.

Trace IDs: `principles.01`, `principles.02`, `R04`, `model_interpretation.01`.

Principal declarations:

- `Classicism.Research.FregeNoncollapse.noncollapse_iff_bottom_not_number.derivable`
- `Classicism.Research.FregeNoncollapse.arithmeticI_iff_istar.derivable`
- `Classicism.Research.FregeNoncollapse.finite_numbers_iff_bottom_number.derivable`
- `Classicism.Research.FregeNoncollapse.infinite_numbers_iff_dedekind.derivable`

Prose proofs: [frege-infinity-20261022-1726.md](source/research/2026-10-22/notes/frege-infinity-20261022-1726.md) · [infinity-core-number-isomorphism.md](source/research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md)

Lean sources: [FregeNoncollapseCertificates.lean](source/topics/classicism/lean/Classicism/Results/Research/FregeNoncollapseCertificates.lean) · [C5ActualityNumbersCertificates.lean](source/topics/classicism/lean/Classicism/Results/Research/C5ActualityNumbersCertificates.lean) · [FregeHumeClassesCertificates.lean](source/topics/classicism/lean/Classicism/Results/Research/FregeHumeClassesCertificates.lean)

Compiler manifests: [20261023T052411006203Z-90a4d7dd.json](source/research/2026-10-22/lean-formalization/checks/20261023T052411006203Z-90a4d7dd.json)

Audits and status: [infinity_arithmetic_profiles.json](source/research/2026-10-22/lean-formalization/verification-updates/infinity_arithmetic_profiles.json)


<a id="evaluators-cores"></a>
## Actual-truth evaluators and current extensional cores

**The prose distinguishes six evaluator strengths and constructs Actuality/Gallin extensional cores. Checked certificates include canonical current evaluators, graph normalization/realization, extension-invariant predicate transfer and the canonical current truth bridge.**

**Scope:** Current predicates and actual-world codes; a single necessarily correct evaluator is stronger than necessary local existence. No future-domain identification or uniformly boxed quantifier law is silently added.

**Lean:** Substantial exact components checked; entire hierarchy and core interpretation incomplete.

The full arbitrary-Henkin truth induction, Gallin comparison and every strictness countermodel are separate from the checked kernels.

Trace IDs: `choice.08`, `choice.09`, `choice.10`, `choice.12`, `choice.16`, `choice.23`, `R08`.

Principal declarations:

- `Classicism.Research.canonicalEvaluator_all.derivable`
- `Classicism.Research.canonicalEvaluator_exists.derivable`
- `Classicism.Research.ActualityCore.graph_normalization_law`
- `Classicism.Research.ActualityCore.canonical_truth_bridge`

Prose proofs: [actual-truth-evaluator-ladder.md](source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md) · [canonical-actual-evaluator.md](source/research/2026-10-22/proof-refinements/canonical-actual-evaluator.md) · [actuality-world-slice-core.md](source/research/2026-10-22/notes/actuality-world-slice-core.md)

Lean sources: [CanonicalEvaluatorCertificates.lean](source/topics/classicism/lean/Classicism/Results/Research/CanonicalEvaluatorCertificates.lean) · [ActualityCoreGraphsCertificates.lean](source/topics/classicism/lean/Classicism/Results/Research/ActualityCoreGraphsCertificates.lean) · [ActualityCoreBridgeCertificates.lean](source/topics/classicism/lean/Classicism/Results/Research/ActualityCoreBridgeCertificates.lean)

Compiler manifests: [20261023T053945495916Z-2d579847.json](source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json) · [20261023T043023549683Z-0cf20b33.json](source/research/2026-10-22/lean-formalization/checks/20261023T043023549683Z-0cf20b33.json)

Audits and status: [world_actuality_gallin.json](source/research/2026-10-22/lean-formalization/verification-updates/world_actuality_gallin.json)


<a id="sp-criteria"></a>
## Strong Possibility reflection and algebraic criteria

**Twelve SP/Max modules establish their stated conditional reflection, universal-core, disjunction/conservativity, Boolean-algebra and computability results. Their exact statements are collected in the corrected prose proof summary.**

**Scope:** Disjunction/conservativity equivalences retain Con(Max). UniversalCore allows arbitrary typed terms, including quantified terms inside identities; it is not a quantifier-free arithmetic hierarchy theorem. InfinitaryNumerals explicitly enlarges the syntax.

**Lean:** Twelve-module verification package complete; wider SP research remains partial.

No SP consistency proof is supplied. The shallow reflected_neg_box intentionally uses Classicism.em; its translated C proof is separately audited. Module counts do not count independent research results.

Trace IDs: `sp_supplement.01`, `sp_supplement.02`, `F13`, `F14`, `F15`.

Principal declarations:

- `Classicism.Meta.Research.StrongPossibilityConsequences.UniversalCore.sp_consistent_iff_universal_core`
- `Classicism.Meta.Research.StrongPossibilityConsequences.MaxConservativity.identity_conservative_iff_max_consistent`

Prose proofs: [proof-summary.md](source/research/2026-10-22/lean-formalization/sp-verification/proof-summary.md) · [reflection-universal-core-20261022.md](source/research/2026-10-22/notes/reflection-universal-core-20261022.md)

Lean sources: [StrongPossibilityConsequencesUniversalCore.lean](source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesUniversalCore.lean) · [StrongPossibilityConsequencesMaxConservativity.lean](source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesMaxConservativity.lean)

Compiler manifests: [20261023T044759304508Z-f503b46f.json](source/research/2026-10-22/lean-formalization/checks/20261023T044759304508Z-f503b46f.json) · [20261023T044336274999Z-6b5c1cb4.json](source/research/2026-10-22/lean-formalization/sp-universal-verification/checks/20261023T044336274999Z-6b5c1cb4.json)

Audits and status: [verification-status.json](source/research/2026-10-22/lean-formalization/sp-verification/verification-status.json) · [verification-status.md](source/research/2026-10-22/lean-formalization/sp-verification/verification-status.md)


<a id="choice-no-finite-basis"></a>
## Full necessary Functional Choice has no finite fixed-type basis

**The ordinary proof reports that full boxed Functional Choice cannot be axiomatized over C by finitely many fixed-type closed formulas; it gives strict cofinal and bounded-type-order refinements.**

**Scope:** Original relational grammar and ordinary ZFC metatheory, using symmetric forcing and ground Henkin extraction. This does not rule out a finite number of unbounded type schemata.

**Lean:** Positive hierarchy and support lemmas checked; negative main theorem not fully formalized.

The surviving ordinary proof has an author audit, not a complete independent Lean certificate. Do not replace the missing forcing/extraction construction by an assumed finite-fragment-gap premise.

Trace IDs: `F09`.

Prose proofs: [finite-functional-choice.md](source/research/2026-10-22/followup/finite-functional-choice.md) · [finite-choice-negative-audit.md](source/research/2026-10-22/lean-formalization/finite-choice-negative-audit.md)

Lean sources: [ChoiceFreshColumns.lean](source/topics/classicism/lean/Classicism/Models/ChoiceFreshColumns.lean)

Audits and status: [hierarchy_oldnew_colourcollapse.json](source/research/2026-10-22/lean-formalization/verification-updates/hierarchy_oldnew_colourcollapse.json)


<a id="probability"></a>
## Faithful probability has an exact finite-fibre condition and type ceiling

**Over C + necessary Plenitude + quantified Infinity_e, the ordinary proofs equate faithful probability with admitted finite-fibre numerical labelling of world atoms. Countable Choice for finite fields upgrades this to internal countability. Higher-type probability has a finiteness obstruction.**

**Scope:** Internal Dedekind reals and represented families. The weaker local version uses Actuality + Atomicity_t + BC_t + Infinity_e and graph-valued probabilities in the current core; it need not supply an ambient operation or future-stable real codes.

**Lean:** Arithmetic/real/finite-family components checked; main probability equivalences incomplete.

Real multiplication/positive normalization and the full threshold/finite-fibre/interpretation bridges remain. A countably additive replacement exists in the ordinary proof; the original finite-additive state is not thereby shown countably additive.

Trace IDs: `choice.18`, `choice.19`, `R02`, `R05`, `R06`, `R07`, `R09`.

Prose proofs: [choice-free-faithful-probability.md](source/research/2026-10-22/proof-refinements/choice-free-faithful-probability.md) · [choice-free-probability-type-ceiling.md](source/research/2026-10-22/proof-refinements/choice-free-probability-type-ceiling.md) · [local-propositional-probability.md](source/research/2026-10-22/proof-refinements/local-propositional-probability.md)

Audits and status: [probability_internal_constructions.json](source/research/2026-10-22/lean-formalization/verification-updates/probability_internal_constructions.json)


<a id="profile-world-algebra"></a>
## Profile Realization and the Boolean structure of worlds

**The ordinary notes give world-indexed representations over necessary Plenitude, consistent individual profile-realization strengthenings, relational-input diagonal obstructions, and nominal examples with all finite supported richness ranks but without Functional Choice.**

**Scope:** Admitted internal fields; original rigid/possible PR and raw world representation are identified only under the stated background. Supported finite-rank richness is not unrestricted realization at relational input types, nor a quantified Infinity axiom.

**Lean:** Supporting sources and finite/arithmetic kernels; full classifications and models not certified.

PR is a research proposal, distinct from the original Actual Profile principle. B + individual quantified Infinity + PR yields the remaining Infinity instances in the ordinary arguments; PR does not itself supply Functional Choice.

Trace IDs: `world_algebra.01`, `world_algebra.05`, `world_algebra.12`, `world_algebra.25`.

Prose proofs: [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md)

Audits and status: [coverage-and-ownership.json](source/research/2026-10-22/lean-formalization/coverage-and-ownership.json) · [world_actuality_gallin.json](source/research/2026-10-22/lean-formalization/verification-updates/world_actuality_gallin.json)


<a id="arithmetic-comparison"></a>
## Arithmetic and effective strength of the competing theories

**The ordinary reports give the stated common first-order arithmetic theory of positive packages, Max's true-Pi1 strengthening, concrete graph-versus-operation obstructions, and conditional effective/model-degree comparisons.**

**Scope:** First-order arithmetic conservativity only; counting-base, finite-proof, adequate-code, external-source and consistency assumptions remain. SP's complexity classification is conditional on consistency. Standard-number models are distinct from arbitrary Henkin models.

**Lean:** Selected foundations and metatheorems checked; full broad comparisons not certified.

Existing source claims are collected, not newly independently adjudicated. Literature novelty and the exact external-theorem locators remain separate review items.

Trace IDs: `principles.03`, `principles.04`, `principles.06`, `principles.16`, `principles.18`, `principles.25`.

Prose proofs: [infinity-world-richness-consolidation-20261022.md](source/research/2026-10-22/notes/infinity-world-richness-consolidation-20261022.md) · [relational-coding-recursion-20261022.md](source/research/2026-10-22/notes/relational-coding-recursion-20261022.md) · [comparison-handoff-20261022.md](source/research/2026-10-22/notes/comparison-handoff-20261022.md)

Audits and status: [infinity_arithmetic_profiles.json](source/research/2026-10-22/lean-formalization/verification-updates/infinity_arithmetic_profiles.json) · [strong_possibility.json](source/research/2026-10-22/lean-formalization/verification-updates/strong_possibility.json)

## Remaining boundaries

Strong Possibility consistency is not proved. Relational Choice alone implying Transversal Choice and the full all-type Tame Rigidity + Rigid Power implication remain separate unresolved questions. The finite-Choice negative theorem, probability classifications, full profile/model classifications and broad arithmetic/effective comparisons retain the partial formalization boundaries above. The package is a complete snapshot of the selected collection, not a claim that every tracked mathematical family is complete.
