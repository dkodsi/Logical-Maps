# Full results, supplements and certificates

[Main results](../MAIN-RESULTS.md) · [Questions](../CONJECTURES.md) · [Catalog](../CATALOG.md) · [Database integration](../DATABASE-INTEGRATION.md)

Full statements, supporting results, proofs and certificates.

## Browse by category

### Headline results

- [Max + Atomicity (type t) ⇒ ⊥](#max-atomicity)
- [Choice and completeness produce Actuality and transversals](#choice-completeness)
- [Signature SP entails pure SP exactly when signature SP is inconsistent](#sp-signature-conflict)
- [☐Functional Choice and ☐Plenitude have the same ordinary arithmetic](#arithmetic-comparison)
- [Pure SP proves true Π₂ arithmetic, with a sharp conditional boundary](#sp-arithmetic-reflection)
- [Classicism can be reconstructed without primitive lambda](#lambda-free-translation) · [Beta identity plus a theorem rule yields contextual beta eta](#beta-eta-conversion)
- [Logical observer separation: a strict hierarchy from BF to Extensionality](#logical-observers)
- [Infinitary Comprehension and C5 characterize full standard models](#infinitary-comprehension)

<a id="supplement-central-results"></a>
**Supplemental results**

- [Atomicity under C5 removes pure contingency](#npc-atomicity)
- [Independence coexists with extensionality and strong Choice](#signature-independence)

### Choice and rigidity

- [Choice and Plenitude decompose into Actuality and inverse maps](#sections-retractions) · [Complete Boolean retractions characterize ☐Functional Choice](#boolean-retractions-choice) · [C5 is exactly strong retractions of actual injections](#c5-strong-retractions)
- [Countable completeness forces Frege finiteness at countable Boolean types](#countable-boolean-finiteness)
- [Logical Necessity and strong selection laws do not force Actuality](#logical-necessity-separation)
- [Functional Choice and ☐Functional Choice have no finite fixed-type basis](#choice-no-finite-basis)
- [Four rigidity principles coincide over ND and Boolean Completeness](#rigidity-nd-bc) · [ND and Boolean Completeness do not give Rigid Comprehension](#oldnew-separation)
- [Strong Leibniz Biconditionals and Rigid Comprehension force modal stability](#modal-propagation)
- [Rigidity has exact power, uniformization and algebraic descriptions](#rigidity-classifications) · [TR + RP does not imply WRP](#finite-compression-separation)
- [Comprehension, completeness and choice do not force ☐Tame Rigidity](#fixed-point-entrance)

<a id="supplement-choice-and-rigidity"></a>
**Supplemental results**

- [Rigid Power at one type does not close the rigidity gap](#colour-collapse-scope)
- [Canonical operations on coextension classes require Actuality](#coextension-operations)
- [Finite cell ambiguity is the exact remaining coherence condition](#choice-coherence)

### Arithmetic and analysis

- [Proposed exact arithmetic strength of pure Maximalism](#max-arithmetic-equality)
- [Maximalism forbids a numerical predecessor operation](#max-predecessor)
- [Rigid Comprehension stabilizes a possible real structure](#analytic-rigidification)
- [Finiteness is classified by the base types occurring in a type](#finite-type-propagation)
- [Infinity schemata do not imply their quantified axioms, even with necessary Choice](#infinity-schema-separation)

<a id="supplement-arithmetic-and-evaluation"></a>
**Supplemental results**

- [Frege number structure and transfer can be separated from stronger model claims](#arithmetic-foundations)

### Continuum Hypothesis and forcing

- [CH can vary despite boxed structural principles](#ch-coalesced)
- [Maximalism is incompatible with Non-contingency of CH](#max-ch)
- [The full modalized cloud realizes both sides of CH](#forcing-transfer)
- [Strict-smallness Forcing Possibilism is independent of necessary Choice and Infinity](#forcing-possibilism)

<a id="supplement-continuum-hypothesis-and-forcing"></a>
### Evaluation and separating operators

- [Actual-truth evaluators and current extensional cores](#evaluators-cores)
- [Uniform evaluator selection measures well-orderability and Choice](#uniform-complete-evaluators)
- [Stable atoms are exactly what diagonal separation requires](#diagonal-characters)
- [Full identity observers have atomic and symmetry representations](#full-identity-observers)

<a id="supplement-operators-and-evaluation"></a>
**Supplemental results**

- [An actual evaluator commuting with modality forces Extensionality](#evaluator-modal-commutation)

### Observer separation over H

- [Observer separation over H: primitive packages, representation and higher types](#h-observer-space)

<a id="supplement-h-observer-separation"></a>
### Worlds and model structure

- [Profile Realization and the Boolean structure of worlds](#profile-world-algebra)
- [World orbits determine propositional Dedekind infinity](#nominal-orbits)
- [Faithful probability has an exact finite-fibre condition and type ceiling](#probability)
- [External atomic joins characterize full Gallin hierarchies](#full-standard-gallin)

<a id="supplement-worlds-and-probability"></a>
### Model theory and computational complexity

- [Theoremhood and model construction have successive jump thresholds](#computability-comparison)
- [A complete theory has a model of exactly its computational degree](#exact-model-degrees)
- [Standard natural numbers impose a much stronger computational barrier](#standard-number-models)
- [Finite descriptions distinguish the completion spaces](#completion-spaces)

<a id="supplement-model-theory-and-computational-complexity"></a>
### Strong Possibility and language

- [Strong Possibility is an exact universal-identity theory](#sp-criteria)
- [SP fixes the actual domain from the number of individual names](#sp-individual-cardinality)
- [An exact boundary for finite signature extensions](#signature-finite-boundary) · [An infinite reserve of names restores conservativity](#signature-infinite-reservoir)
- [Pointed theories determine the finite Boolean intervals forced by SP](#sp-finite-profile-rank)
- [Finite-signature SP refutes BF and Functionality at every input type](#sp-barcan-functionality)
- [Infinitary formation changes exhaustion and arithmetic](#infinitary-resources)

<a id="supplement-possibility-and-language"></a>
**Supplemental results**

- [A pure SP embedding must omit a whole numerical cut](#pure-sp-bounded-image)
- [One Henkin witness stage suffices for signature SP consistency](#signature-sp-survival)

<a id="max-atomicity"></a>
## Max + Atomicity (type t) ⇒ ⊥

**ID:** `MAX-ATOMICITY`. Tracked keys: `F11`.

C + pure Maximalism + Atomicity (type t) is inconsistent.

**Scope:** Original finitary relational language; pure signature. The final theorem has no additional selector, coding, rigidity, model-existence or non-theoremhood premise.

**Significance:** An exact incompatibility between two major principles: propositional Atomicity cannot be added to pure Maximalism, even without boxing Atomicity.

**Lean certified.**

**Notes:** The proof uses the Jech–Shelah rigid complete atomless algebra; the new contribution is its finite pure coding and application to Maximalism.

The substantial construction turns the Jech–Shelah rigid atomless algebra into a finite closed pure code; only then can a Max instance supply the contradiction with Atomicity.

**Proof length:** long (5,069 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [max-atomicity-canonical-code-proof.md](../source/research/2026-10-22/lean-formalization/max-atomicity-canonical-code-proof.md) · [max-atomicity-inconsistency-proof.md](../source/research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md)

**Earlier Lean sources:** [MaxAtomicityInconsistency.lean](../source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityInconsistency.lean)

**Earlier saved manifests:** [20261023T054730505817Z-9a834f08.json](../source/research/2026-10-22/lean-formalization/checks/20261023T054730505817Z-9a834f08.json)

**Scope evidence:** [max-certificate-audit.json](../source/research/2026-10-22/lean-formalization/max-certificate-audit.json) · [Classicism_Results_Research_MaxAtomicityInconsistency.log](../source/research/2026-10-22/lean-formalization/logs/runs/20261023T054730505817Z-9a834f08/Classicism_Results_Research_MaxAtomicityInconsistency.log)

**Principal declarations:**

- `Classicism.Meta.Research.MaxAtomicityInconsistency.maximalism_atomicity_inconsistent`

<a id="choice-completeness"></a>
## Choice and completeness produce Actuality and transversals

**ID:** `CHOICE-COMPLETENESS`. Tracked keys: `F01`, `rigidity.16`, `rigidity.19`.

Relational Choice from t to t plus Boolean Completeness (type tt) implies Actuality. Relational Choice plus Boolean Completeness implies Transversal Choice. The independent direct proofs also yield type-specific, represented-chain-completeness and countable-completeness/ccc refinements.

**Scope:** C. No ND or BF is added to the sharp Actuality theorem. The transversal refinements retain their exact point-selection, type and counting-base conditions.

**Significance:** Selection and Boolean completeness together recover an actual-world truth selector and quotient representatives. This identifies what completeness contributes beyond Relational Choice alone.

**Lean certified:** RC + BC ⇒ TC; the sharp Actuality theorem, Actuality-based TC, and the same-type RC + BC and CBC + CCC consequences.

**Notes:** The RC + BC proof factors through Actuality. The independent direct proof sharpens the choice and chain-completeness premises. RC alone ⇒ TC remains unresolved.

The direct proof adapts Bourbaki–Witt inside C: represented joins preserve partial transversals, and guarded progress yields a fixed point without assuming Plenitude.

**Proof length:** long (4,051 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [choice-completeness-actuality.md](../source/research/2026-10-22/followup/choice-completeness-actuality.md) · [relational-choice-boolean-completeness-transversal-proof.md](../source/research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md)

**Earlier Lean sources:** [ChoiceActualityCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/ChoiceActualityCertificates.lean) · [ChoiceSectionsRetractionsChecks.lean](../source/topics/classicism/lean/Classicism/Results/Research/ChoiceSectionsRetractionsChecks.lean)

**Earlier saved manifests:** [20261023T053945495916Z-2d579847.json](../source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json)

**Scope evidence:** [choice_sections_retractions.json](../source/research/2026-10-22/lean-formalization/verification-updates/choice_sections_retractions.json) · [direct-transversal-lean-coverage.json](direct-transversal-lean-coverage.json) · [choice-transversal-comparison.md](../proofs/choice-transversal-comparison.md) · [transversal-generated-acceptance-audit.json](transversal-generated-acceptance-audit.json)

**Principal declarations:**

- `Classicism.Research.Choice.choice_completeness_actuality_sharp.derivable`
- `Classicism.Research.Choice.choice_completeness_transversal_sharp.derivable`
- `Classicism.Research.Choice.local_choice_completeness_transversal.derivable`
- `Classicism.Research.Choice.local_choice_countable_ccc_transversal.derivable`

<a id="modal-propagation"></a>
## Strong Leibniz Biconditionals and Rigid Comprehension force modal stability

**ID:** `MODAL-PROPAGATION`. Tracked keys: `F05`, `rigidity.13`.

Strong Leibniz Biconditionals plus Rigid Comprehension entails ☐Strong Leibniz Biconditionals, ☐BF (type τ, τ ≠ e), ☐Rigid Comprehension and ☐Boolean Completeness.

**Scope:** Pure C; comprehension covers every admitted finite argument tuple, including individual and mixed tuples. The BF conclusion is restricted to relational types; it does not include BF (type e).

**Significance:** The two premises force several principles under ☐. This explains a substantial cluster of arrows in the map.

**Lean certified.**

**Proof length:** medium (2,286 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [strong-leibniz-rigid-bottom-cut.md](../source/research/2026-10-22/strong-leibniz-rigid-bottom-cut.md) · [modal-propagation.md](../source/research/2026-10-22/followup/modal-propagation.md)

**Earlier Lean sources:** [ModalPropagationSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/ModalPropagationSchemas.lean)

**Earlier saved manifests:** [20261023T030134260568Z.json](../source/research/2026-10-22/lean-formalization/checks/20261023T030134260568Z.json)

**Scope evidence:** [ModalPropagationAxioms.log](../source/research/2026-10-22/lean-formalization/logs/runs/20261023T030134260568Z/ModalPropagationAxioms.log) · [significant-results.json](../source/research/2026-10-22/lean-formalization/significant-results.json)

**Principal declarations:**

- `Classicism.Meta.Research.ModalPropagation.all_four`

<a id="rigidity-nd-bc"></a>
## Four rigidity principles coincide over ND and Boolean Completeness

**ID:** `RIGIDITY-ND-BC`. Tracked keys: `rigidity.10`.

Over C + ND + Boolean Completeness, Inextensible Comprehension, Rigid Comprehension, Tame Rigidity and Weakly Rigid Power are equivalent.

**Scope:** The equivalence uses the relational type schemas; the route to Weakly Rigid Power uses a higher property type.

**Significance:** Several seemingly different additions to this base express one strength. Combined with the old/new model, this identifies a real extra requirement rather than something already implied by ND + BC.

**Lean certified.**

**Proof length:** medium (1,024 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** “Exact classification over ND + BC”; corrected old/new separation

**Proofs:** [nd-inextensible-comprehension-implies-weak-power.md](../source/research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md) · [old-new-boolean-completeness-and-rigidity-separation.md](../source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md)

**Earlier Lean sources:** [RigidityClosureResearchSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchSchemas.lean) · [RigidityClosureResearchClassification.lean](../source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchClassification.lean)

**Earlier saved manifests:** [20261023T044252100669Z-9b8e2beb.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044252100669Z-9b8e2beb.json)

**Scope evidence:** [local_rigidity_closure_replacement.json](../source/research/2026-10-22/lean-formalization/verification-updates/local_rigidity_closure_replacement.json)

**Principal declarations:**

- `Classicism.Meta.Research.RigidityClosure.ic_rc_equivalent`
- `Classicism.Meta.Research.RigidityClosure.tame_rc_equivalent`
- `Classicism.Meta.Research.RigidityClosure.weak_power_rc_equivalent`

<a id="oldnew-separation"></a>
## ND and Boolean Completeness do not give Rigid Comprehension

**ID:** `OLDNEW-SEPARATION`. Tracked keys: `rigidity.31`.

A concrete model satisfies ND and Boolean Completeness, but fails Inextensible Comprehension (type et), Rigid Comprehension (type et), Tame Rigidity, and ☐Boolean Completeness (type et). Boolean Completeness (type et) also fails at each specified accessible E-to-O evaluation.

**Scope:** Pure C. The complete declaration uses the original old/new construction. No ☐Rigid Power or signature-extension verdict is inferred from it.

**Significance:** Completeness and ND still leave a rigidity gap. The corrected model supplies the lower side of the four-way equivalence over ND + BC.

**Lean certified.**

**Notes:** The external even-haecceity family is not admitted in the model; the corrected argument establishes BC at E.

**Attribution:** Existing construction and ND/Inextensible Comprehension verdicts: Claude Fable 5.1 and Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, October 2026, using Dorr’s symmetric ideally-full semantics. The all-type BC verification and corrected separation are new arguments in this research collection.

**Proof length:** medium (1,894 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [old-new-boolean-completeness-and-rigidity-separation.md](../source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md) · [old-new-boolean-completeness-source-caveat.md](../source/research/2026-10-22/notes/old-new-boolean-completeness-source-caveat.md)

**Earlier Lean sources:** [OldNewComplete.lean](../source/topics/classicism/lean/Classicism/Models/OldNewComplete.lean) · [OldNewSeparation.lean](../source/topics/classicism/lean/Classicism/Models/OldNewSeparation.lean)

**Earlier saved manifests:** [20261023T045855511121Z-2911dd87.json](../source/research/2026-10-22/lean-formalization/checks/20261023T045855511121Z-2911dd87.json)

**Scope evidence:** [hierarchy_oldnew_colourcollapse.json](../source/research/2026-10-22/lean-formalization/verification-updates/hierarchy_oldnew_colourcollapse.json)

**Principal declarations:**

- `Classicism.Meta.Intensional.OldNew.complete_countermodel`
- `Classicism.Meta.Intensional.OldNew.background_consistent`
- `Classicism.Meta.Intensional.OldNew.not_entails_rc`
- `Classicism.Meta.Intensional.OldNew.not_entails_tame`
- `Classicism.Meta.Intensional.OldNew.not_entails_box_bc`

<a id="logical-necessity-separation"></a>
## Logical Necessity and strong selection laws do not force Actuality

**ID:** `LOGICAL-NECESSITY-SEPARATION`. Tracked keys: `F07`.

For the concrete one-predicate signature, Logical Necessity + ☐BF + ☐Relational Choice is consistent and does not entail Actuality or Vicinity.

**Scope:** C with the explicitly interpreted one-constant signature. The concrete supported-product model supplies the semantics. The ordinary prose also treats arbitrary set-sized signatures and additional verdicts, which are not all covered by this certificate.

**Significance:** Strong selection and modal laws can coexist with failure of Actuality. Logical Necessity therefore does not supply the actual-world structure by itself.

**Lean certified.**

**Proof length:** medium (1,900 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [central-map.md](../source/research/2026-10-22/followup/central-map.md)

**Earlier Lean sources:** [CentralSupportedProductChoice.lean](../source/topics/classicism/lean/Classicism/Semantics/Research/CentralSupportedProductChoice.lean) · [CentralSupportedProductVicinity.lean](../source/topics/classicism/lean/Classicism/Semantics/Research/CentralSupportedProductVicinity.lean)

**Earlier saved manifests:** [20261023T054410104697Z-48120445.json](../source/research/2026-10-22/lean-formalization/checks/20261023T054410104697Z-48120445.json) · [20261023T054809252922Z-5177013d.json](../source/research/2026-10-22/lean-formalization/checks/20261023T054809252922Z-5177013d.json)

**Scope evidence:** [modal_central_negative_models.json](../source/research/2026-10-22/lean-formalization/verification-updates/modal_central_negative_models.json)

**Principal declarations:**

- `Classicism.Meta.Intensional.Central.OneConstant.package_consistent`
- `Classicism.Meta.Intensional.Central.OneConstant.package_not_entails_actuality`
- `Classicism.Meta.Intensional.Central.OneConstant.package_not_entails_vicinity`

<a id="signature-independence"></a>
## Independence coexists with extensionality and strong Choice

**ID:** `SIGNATURE-INDEPENDENCE`. Tracked keys: `central.signature_countermodels`.

For Σ={c:et}, full one-world models satisfy Independence together with the stated Extensionality/C5/Atomicity/Choice packages and refute the indicated Infinity implications. Two concrete models answer twelve displayed signature-uniform rows.

**Scope:** Exactly the one-predicate signature; either two individuals or natural-number individuals, with a proper nonempty interpretation of c. It is not an existence theorem for every richer fixed signature.

**Significance:** Concrete interpretations answer several central signature questions while showing why a result for one specified language must not be promoted to every signature.

**Lean certified.**

**Proof length:** short (730 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [central-questions-audit.md](../source/research/2026-10-22/central-questions-audit.md)

**Earlier Lean sources:** [SinglePredicateCountermodelChecks.lean](../source/topics/classicism/lean/Classicism/Models/SinglePredicateCountermodelChecks.lean)

**Earlier saved manifests:** [20261023T051126488606Z-b00090cd.json](../source/research/2026-10-22/lean-formalization/checks/20261023T051126488606Z-b00090cd.json)

**Scope evidence:** [model_foundations_signature_nominal.json](../source/research/2026-10-22/lean-formalization/verification-updates/model_foundations_signature_nominal.json)

**Principal declarations:**

- `Classicism.Meta.SinglePredicateFull.bool_complete_countermodel`
- `Classicism.Meta.SinglePredicateFull.nat_complete_countermodel`
- `Classicism.Meta.SinglePredicateFull.extensional_independence_choice_not_infinity`

<a id="sections-retractions"></a>
## Choice and Plenitude decompose into Actuality and inverse maps

**ID:** `SECTIONS-RETRACTIONS`. Tracked keys: `choice.01`, `choice.02`, `choice.03`, `choice.05`, `choice.06`, `choice.07`.

Functional Choice is equivalent to Actuality plus pointwise sections of actual surjections; Plenitude is equivalent to Actuality plus pointwise retractions of actual injections. ☐Functional Choice is also equivalent to ☐Actuality plus the strong-section schema.

**Scope:** The splitting maps run between relational types. Strong sections require actual surjectivity and a necessarily correct right inverse. Functional Choice still allows individual inputs.

**Significance:** Choice and Plenitude each separate into Actuality and a familiar inverse-map principle. This makes their different strengths easier to compare.

**Lean certified.**

**Notes:** The strong-section result uses No Pure Contingency to box pure FC instances; it does not necessitate optional assumptions.

The reverse direction encodes witnesses into an actual surjection so that any section yields Choice. The necessary version also uses the substantial pure-term invariance proof behind No Pure Contingency.

**Proof length:** medium (2,876 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [functional-choice-by-sections.md](../source/research/2026-10-22/notes/functional-choice-by-sections.md) · [choice-uniformization.md](../source/research/2026-10-22/notes/choice-uniformization.md)

**Earlier Lean sources:** [SectionsRetractionsSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsSchemas.lean) · [SectionsRetractionsBoxedSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsBoxedSchemas.lean)

**Earlier saved manifests:** [20261023T053945495916Z-2d579847.json](../source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json)

**Scope evidence:** [choice_sections_retractions.json](../source/research/2026-10-22/lean-formalization/verification-updates/choice_sections_retractions.json) · [integration-scope-reconciliation.json](integration-scope-reconciliation.json)

**Selected exact certificates:** [certificate.json](certificates/strong-sections/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.Splitting.functional_choice_equivalence`
- `Classicism.Meta.Research.Splitting.plenitude_equivalence`
- `Classicism.Meta.Research.Splitting.necessary_choice_equivalence`
- `Classicism.Meta.Research.Splitting.necessary_plenitude_equivalence`

<a id="rigidity-classifications"></a>
## Rigidity has exact power, uniformization and algebraic descriptions

**ID:** `RIGIDITY-CLASSIFICATIONS`. Tracked keys: `rigidity.02`, `rigidity.08`, `rigidity.11`, `rigidity.12`.

Atomicity + Rigid Comprehension implies Weakly Rigid Power. Weakly Rigid Power is equivalent to Tame Rigidity + Rigid Power + bounded future-tameness. Uniform weak/rigid comprehension is equivalent to ND plus the corresponding weak/rigid comprehension schema.

**Scope:** Pure C, full schemas with nullary and finite-tuple cases. Bounded future-tameness says every future weakly rigid subrelation of an actual rigid bound is rigid. The WRP-to-RP route uses the next property type.

**Significance:** The decomposition identifies bounded future-tameness as the additional condition relating Weakly Rigid Power to Tame Rigidity plus Rigid Power.

**Lean certified.**

**Notes:** The finite-compression countermodel shows that bounded future-tameness cannot be dropped.

**Proof length:** medium (1,806 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [maximalism-modal.md](../source/research/2026-10-22/notes/maximalism-modal.md) · [rigidity-by-joins-and-boolean-closure.md](../source/research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md)

**Earlier Lean sources:** [RigidityClosureResearchContinuationSchemas.lean](../source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchContinuationSchemas.lean) · [RigidityClosureResearchBounded.lean](../source/topics/classicism/lean/Classicism/Results/Research/RigidityClosureResearchBounded.lean)

**Earlier saved manifests:** [20261023T044252100669Z-9b8e2beb.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044252100669Z-9b8e2beb.json)

**Scope evidence:** [local_rigidity_closure_replacement.json](../source/research/2026-10-22/lean-formalization/verification-updates/local_rigidity_closure_replacement.json)

**Principal declarations:**

- `Classicism.Meta.Research.RigidityClosure.atomicity_rc_weak_power`
- `Classicism.Meta.Research.RigidityClosure.weak_power_decomposition_equivalent`
- `Classicism.Meta.Research.RigidityClosure.uniform_weak_equivalent`
- `Classicism.Meta.Research.RigidityClosure.uniform_rigid_equivalent`

<a id="boolean-retractions-choice"></a>
## Complete Boolean retractions characterize ☐Functional Choice

**ID:** `BOOLEAN-RETRACTIONS-CHOICE`. Tracked keys: `world_algebra.12`.

Over C + ☐Plenitude, ☐Functional Choice is equivalent to the schema saying every admitted rigid internally complete Boolean subalgebra of every relational-type Boolean algebra has a complete Boolean retraction.

**Scope:** Internal completeness ranges over admitted families. The all-type requirement is essential; a single canonical membership inclusion per output type suffices for the converse.

**Significance:** This supplies an algebraic characterization of the step from the Plenitude baseline to full Choice. Retractions select representatives of the corresponding equivalence classes of atoms.



**Proof length:** long (4,578 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §§16,18–19,38

**Proofs:** [structural-algebraic-core.md](../source/research/2026-10-22/notes/structural-algebraic-core.md)

<a id="countable-boolean-finiteness"></a>
## Countable completeness forces Frege finiteness at countable Boolean types

**ID:** `COUNTABLE-BOOLEAN-FINITENESS`. Tracked keys: `rigidity.20`.

In bare C, an internally countable relational Boolean type is countably complete iff it is internally Frege-finite. Consequently internal countability plus the matching Countable Boolean Completeness implies Actuality.

**Scope:** Countability is relative to a specified admitted counting base. No Choice, Infinity, BF, ND or Plenitude premise is required. Internal finiteness does not imply external finiteness.

**Significance:** This gives a route to Actuality from internal countability and countable completeness, without selection assumptions. It also specifies when countable completeness reduces to internal finiteness.



**Proof length:** medium (2,512 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §§21–21.3

**Proofs:** [quotient-abstraction-lane.md](../source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="choice-no-finite-basis"></a>
## Functional Choice and ☐Functional Choice have no finite fixed-type basis

**ID:** `CHOICE-NO-FINITE-BASIS`. Tracked keys: `F09`.

Neither Functional Choice nor ☐Functional Choice is equivalent over C to any finite list of pure fixed-type sentences. Selector strength forms a strict hierarchy as the available types increase.

**Scope:** Original relational grammar and ZFC metatheory. The Boolean-valued construction recovers ordinary one-world general C-models satisfying any prescribed finite Choice fragment and failing a further instance. The theorem concerns equivalent bases, not finite strictly stronger theories or finitely many unbounded type schemata. No additional object-language Infinity assumption is used. The extracted models need not preserve the Boolean hierarchy’s external cardinalities.

**Significance:** The obstruction applies to arbitrary finite proposed axiomatizations, not just finite subsets of the Choice schema.

**Lean certified.**

A coherent Boolean-valued type hierarchy supports lower-type selectors and a higher-type obstruction. Countable witness extraction recovers an ordinary C-model, and translation back to the original pure syntax yields the finite-basis obstruction.

**Proof length:** long (3,741 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Boolean finite Choice §§1–10 and the final unboxed extension; independent review, Conclusion and critical checks 4–5.

**Proofs:** [boolean-finite-choice.md](../proofs/boolean-finite-choice.md) · [finite-functional-choice.md](../source/research/2026-10-22/followup/finite-functional-choice.md) · [finite-choice-negative-audit.md](../source/research/2026-10-22/lean-formalization/finite-choice-negative-audit.md) · [choice-nonfinite-basis.md](../proofs/choice-nonfinite-basis.md)

**Earlier Lean sources:** [ChoiceFreshColumns.lean](../source/topics/classicism/lean/Classicism/Models/ChoiceFreshColumns.lean)

**Earlier saved manifests:** [selected-manifest.json](certificates/finite-choice-full-construction/selected-manifest.json)

**Scope evidence:** [hierarchy_oldnew_colourcollapse.json](../source/research/2026-10-22/lean-formalization/verification-updates/hierarchy_oldnew_colourcollapse.json) · [certification-closeout.json](certification-closeout.json) · [acceptance.json](certificates/finite-choice-full-construction/acceptance.json)

**Selected exact certificates:** [certificate.json](certificates/final-choice-boolean-foundations-axioms/certificate.json) · [certificate.json](certificates/final-choice-first-order-recovery/certificate.json) · [certificate.json](certificates/final-boolean-protected-coverage/certificate.json) · [certificate.json](certificates/finite-choice-full-construction/certificate.json)

**Principal declarations:**

- `Classicism.Meta.ChoiceFirstOrder.Structure.model`
- `Classicism.Meta.ChoiceFirstOrder.admit_definable`
- `Classicism.Meta.ChoiceFirstOrder.valueCode_correct`
- `Classicism.Meta.ChoiceFirstOrder.translate_correct`
- `Classicism.Meta.ChoiceFirstOrder.isModel`
- `Classicism.Meta.ChoiceFirstOrder.c_theorem_holds`
- `Classicism.Meta.ChoiceFirstOrder.sentenceTranslation_correct`
- `Classicism.Meta.ChoiceFirstOrder.Formula.realize_agree`
- `Classicism.Meta.ChoiceFirstOrder.Formula.reify_correct`
- `Classicism.Meta.ChoiceFirstOrder.smallSentenceTranslation_correct`
- `Classicism.Meta.ChoiceFirstOrder.isModel_of_small_comprehension`
- `Classicism.Meta.ChoiceFirstOrder.small_c_theorem_holds`
- `Classicism.Meta.ChoiceFirstOrder.Full.comprehension`
- `Classicism.Meta.ChoiceFirstOrder.Full.isModel`
- `Classicism.Meta.ChoiceFirstOrder.Full.serial_has_operation`
- `Classicism.Meta.ChoiceFirstOrder.smallFormula_countable`
- `Classicism.Meta.ChoiceFirstOrder.contextFormula_countable`
- `Classicism.Meta.ChoiceFirstOrder.smallComprehensionIndex_countable`
- `Classicism.Meta.ChoiceFirstOrder.SmallFormula.decode_code`
- `Classicism.Meta.ChoiceFirstOrder.SmallFormula.code_injective`
- `Classicism.Meta.ChoiceFirstOrder.smallSentenceEmbedding`
- `Classicism.Meta.ChoiceFirstOrder.smallSentenceCode_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.language_countable`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.profile_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.variable_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.guardedAll_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.guardedEx_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.allArgs_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.exArgs_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.translate_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.sentence_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.profile_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.variable_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.guardedAll_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.guardedEx_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.allArgs_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.exArgs_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.raw_translate_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.raw_sentence_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.rawRealize_recoverStructure`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.Recovery.sentence_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.raw_rename_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.raw_insertWitness_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.axiomIndex_countable`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.theory_countable`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.nonempty_sentence_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.extensionality_sentence_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.comprehension_sentence_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.model_nonempty`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.model_extensional`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.recovered_smallComprehension`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.recovered_isModel`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.recovered_sentence_correct`
- `Classicism.Meta.ChoiceFirstOrder.MathlibBridge.AxiomTheory.recovered_c_theorem_holds`
- `Classicism.Meta.ChoiceBoolean.ColumnConditions.small_chain_lower_bound`
- `Classicism.Meta.ChoiceBoolean.ColumnDistributivity.binary_distributivity`
- `Classicism.Meta.ChoiceBoolean.TypedTermSemantics.term_comprehension`
- `Classicism.Meta.ChoiceBoolean.SmallFormulaSemantics.small_comprehension`
- `Classicism.Meta.ChoiceBoolean.ProtectedCoverage.ground_coverage`
- `Classicism.Meta.ChoiceBoolean.ChoiceCutoff.exists_regular_cutoff`
- `Classicism.Meta.ChoiceBoolean.SupportedSelection.row_equation`
- `Classicism.Meta.ChoiceBoolean.IndexedProfiles.columns_eqv_zero`
- `Classicism.Meta.ChoiceBoolean.SelectorObstruction.selector_existence_value_zero`
- `Classicism.Meta.ChoiceBoolean.TaggedFirstOrder.sentence_value`
- `Classicism.Meta.ChoiceBoolean.ModelExtraction.realize_iff_secured`
- `Classicism.Meta.ChoiceBoolean.BooleanAxiomTheory.axioms_value_one`
- `Classicism.Meta.ChoiceBoolean.RecoveredModel.isModel`
- `Classicism.Meta.ChoiceBoolean.RecoveredModel.small_transfer_one`
- `Classicism.Meta.ChoiceBoolean.RecoveredModel.small_failure_zero`
- `Classicism.Meta.ChoiceBoolean.ChoiceModel.isModel`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.holds_boxed_functionalChoice`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.fails_boxed_selector`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.finite_boxed_countermodel`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.finite_unboxed_countermodel`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.boxed_finite_fragment_gap`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.unboxed_finite_fragment_gap`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.boxed_not_finitely_axiomatizable`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.unboxed_not_finitely_axiomatizable`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.selector_stage_strict`
- `Classicism.Meta.ChoiceBoolean.FiniteChoice.adjacent_selector_countermodel`
- `Classicism.Meta.ChoiceBoolean.SchemaConsequences.not_finitely_axiomatizable_of_equiv`
- `Classicism.Meta.ChoiceBoolean.SchemaConsequences.allStages_not_finitely_axiomatizable`
- `Classicism.Meta.ChoiceBoolean.SchemaConsequences.diagonalChoice_not_finitely_axiomatizable`
- `Classicism.Meta.ChoiceBoolean.SchemaConsequences.fullChoice_entails_boxedSelector`
- `Classicism.Meta.ChoiceBoolean.SchemaConsequences.boxedSelector_entails_fullChoice`
- `Classicism.Meta.ChoiceBoolean.SchemaConsequences.boxedSelector_not_finitely_axiomatizable`

<a id="arithmetic-foundations"></a>
## Frege number structure and transfer can be separated from stronger model claims

**ID:** `ARITHMETIC-FOUNDATIONS`. Tracked keys: `principles.01`, `principles.02`, `R04`, `model_interpretation.01`.

The cited certificates establish the exact successor-noncollapse/bottom-number equivalences, finite-versus-Dedekind-infinite number-field results, and specified number-map/Hume-class and C5-Actuality transfer results.

**Scope:** Internal Frege finite cardinalities at the source's admitted counting types. Domain Infinity, arithmetic noncollapse, the finite-numeral schema and external standardness are different conditions.

**Significance:** Arithmetic noncollapse, quantified domain Infinity, and an infinity schema are different resources. The transfer theorems specify what survives changes of counting base or passage to a core.

**Lean certified:** The displayed Frege noncollapse and finiteness equivalences, number-map/Hume-class results, and C5–Actuality transfer results.

**Notes:** The semantic certificates cover inner-domain reflection, four C5 base-infinity models, conditional frame counting, the two-stage model and number field, and the extensionally-full orbit bridge. They do not establish standardness for arbitrary Henkin models, numeral-map injectivity, or a uniform object-C proof builder.

**Proof length:** long (7,433 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [frege-infinity-20261022-1726.md](../source/research/2026-10-22/notes/frege-infinity-20261022-1726.md) · [infinity-core-number-isomorphism.md](../source/research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md)

**Earlier Lean sources:** [FregeNoncollapseCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/FregeNoncollapseCertificates.lean) · [C5ActualityNumbersCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/C5ActualityNumbersCertificates.lean) · [FregeHumeClassesCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/FregeHumeClassesCertificates.lean)

**Earlier saved manifests:** [20261023T052411006203Z-90a4d7dd.json](../source/research/2026-10-22/lean-formalization/checks/20261023T052411006203Z-90a4d7dd.json)

**Scope evidence:** [infinity_arithmetic_profiles.json](../source/research/2026-10-22/lean-formalization/verification-updates/infinity_arithmetic_profiles.json) · [certification-closeout.json](certification-closeout.json) · [arithmetic-closeout.json](arithmetic-closeout.json) · [arithmetic-closeout-references.json](arithmetic-closeout-references.json)

**Selected exact certificates:** [certificate.json](certificates/generated-algebra-source/certificate.json) · [certificate.json](certificates/generated-algebra-target/certificate.json) · [certificate.json](certificates/generated-algebra-left-inverse-zero/certificate.json) · [certificate.json](certificates/final-generated-algebra-finite-fold-certificates-base/certificate.json) · [certificate.json](certificates/final-generated-algebra-finite-factored-certificates-left-inverse1/certificate.json) · [certificate.json](certificates/final-intensional-arithmetic-reflection/certificate.json) · [certificate.json](certificates/final-two-stage-arithmetic-model/certificate.json) · [certificate.json](certificates/final-generated-algebra-finite-factored-certificates-left-inverse2/certificate.json) · [certificate.json](certificates/arithmetic-closeout-20261024T022609307928Z-123e4fa6/certificate.json) · [certificate.json](certificates/arithmetic-closeout-20261024T024202505795Z-196c65f3/certificate.json) · [certificate.json](certificates/arithmetic-closeout-20261024T022027443032Z-16979b8f/certificate.json)

**Principal declarations:**

- `Classicism.Research.FregeNoncollapse.noncollapse_iff_bottom_not_number.derivable`
- `Classicism.Research.FregeNoncollapse.arithmeticI_iff_istar.derivable`
- `Classicism.Research.FregeNoncollapse.finite_numbers_iff_bottom_number.derivable`
- `Classicism.Research.FregeNoncollapse.infinite_numbers_iff_dedekind.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.source_op0.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.source_op1.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.source_op2.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.source_op3.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.source_op4.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.source_op5.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.point_persistent0.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.persistent0.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.rigid0.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.point_persistent1.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.persistent1.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.rigid1.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.point_persistent2.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.persistent2.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.rigid2.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.target_op0.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.target_op1.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.target_op2.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.target_op3.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.target_op4.derivable`
- `Classicism.Research.GeneratedAlgebraFinite.target_op5.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFold.forward0.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFold.forward1.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFold.forward2.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.onto0.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.onto1.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.onto2.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.left_inverse0.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.injective0.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.right_inverse0.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.left_inverse1.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.injective1.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.right_inverse1.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.left_inverse2.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.injective2.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.right_inverse2.derivable`
- `Classicism.Research.FregeFiniteSets.finite_self_injection_surjective.derivable`
- `Classicism.Research.C5ActualityNumbers.order_iff_c5.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.pullback_op0.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.pullback_op1.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.pullback_op2.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.pullback_op3.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.pullback_op4.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFactored.pullback_op5.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFold.source_fold0.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFold.source_fold1.derivable`
- `Classicism.Research.GeneratedAlgebraFiniteFold.source_fold2.derivable`

<a id="evaluators-cores"></a>
## Actual-truth evaluators and current extensional cores

**ID:** `EVALUATORS-CORES`. Tracked keys: `choice.08`, `choice.09`, `choice.10`, `choice.12`, `choice.16`, `choice.23`, `R08`, `choice.13`, `choice.14`, `choice.15`, `choice.17`.

The prose distinguishes six evaluator strengths and constructs Actuality/Gallin extensional cores. Checked certificates include canonical current evaluators, graph normalization/realization, extension-invariant predicate transfer and the canonical current truth bridge.

**Scope:** Current predicates and actual-world codes; a single necessarily correct evaluator is stronger than necessary local existence. No future-domain identification or uniformly boxed quantifier law is silently added.

**Significance:** An evaluator correct now, one correct at a selected world, and one fixed evaluator necessarily correct are different demands. The hierarchy explains why apparently similar definitions of evaluation have different strength.

**Lean certified:** Actuality-core conversion and admitted-value lemmas.

**Proof length:** long (5,834 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [actual-truth-evaluator-ladder.md](../source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md) · [canonical-actual-evaluator.md](../source/research/2026-10-22/proof-refinements/canonical-actual-evaluator.md) · [actuality-world-slice-core.md](../source/research/2026-10-22/notes/actuality-world-slice-core.md)

**Earlier Lean sources:** [CanonicalEvaluatorCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/CanonicalEvaluatorCertificates.lean) · [ActualityCoreGraphsCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/ActualityCoreGraphsCertificates.lean) · [ActualityCoreBridgeCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/ActualityCoreBridgeCertificates.lean)

**Earlier saved manifests:** [20261023T053945495916Z-2d579847.json](../source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json) · [20261023T043023549683Z-0cf20b33.json](../source/research/2026-10-22/lean-formalization/checks/20261023T043023549683Z-0cf20b33.json)

**Scope evidence:** [world_actuality_gallin.json](../source/research/2026-10-22/lean-formalization/verification-updates/world_actuality_gallin.json)

**Principal declarations:**

- `Classicism.Research.canonicalEvaluator_all.derivable`
- `Classicism.Research.canonicalEvaluator_exists.derivable`
- `Classicism.Research.ActualityCore.graph_normalization_law`
- `Classicism.Research.ActualityCore.canonical_truth_bridge`

<a id="max-predecessor"></a>
## Maximalism forbids a numerical predecessor operation

**ID:** `MAX-PREDECESSOR`. Tracked keys: `principles.05`, `principles.06`.

At every admitted counting type σ, pure Max refutes an operation f satisfying f(Sσ n)=n for all Frege numbers n. The ordinary argument also gives a total single-valued predecessor graph which cannot be represented by such an operation.

**Scope:** No condition on f(0) is imposed. The all-type no-operation theorem has no Infinity or consistency premise. The stronger graph and Plenitude certificate is a separate target at counting type e.

**Significance:** A total functional arithmetic graph need not have an intensional operation representing it. This pinpoints how Max can support relational arithmetic while opposing individual Plenitude instances.

**Lean certified:** The no-predecessor theorem at every closed counting type; the total unique graph and Plenitude failure at e.

**Proof length:** short (636 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §38; related cross-base graph/operation results in §§34–35

**Proofs:** [predecessor.md](../proofs/predecessor.md)

**Selected exact certificates:** [certificate.json](certificates/max-predecessor/certificate.json) · [certificate.json](certificates/max-predecessor-graph/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.MaxPredecessorSchema.maximalism_no_predecessor`

<a id="arithmetic-comparison"></a>
## ☐Functional Choice and ☐Plenitude have the same ordinary arithmetic

**ID:** `ARITHMETIC-COMPARISON`. Tracked keys: `principles.03`, `principles.06`, `principles.16`, `principles.18`, `principles.25`.

Over C with Axiom of Infinity (types e and t), replacing ☐Plenitude by ☐Functional Choice adds no ordinary first-order arithmetic theorems. Both have the arithmetic consequences of C plus numerical noncollapse at e, and this remains true after adding ☐Axiom of Infinity (type σ) at every admitted σ.

**Scope:** Finitary derivability of sentences under the fixed Frege translation. The proof uses the current quotient and McLarty’s number-preserving finite-order interpretation, with rank chosen for each finite proof. It establishes no higher-order, modal or parameterized conservation and does not settle the separate exact Max arithmetic equality. The effective-degree comparisons retain their own coding and consistency assumptions.

**Significance:** ☐Functional Choice contributes selection and structural consequences beyond ☐Plenitude, but no additional ordinary first-order arithmetic theorems under the stated infinity assumptions.



**Attribution:** Existing Frege-infinity note §36 argument and 23 October 2026 audits by OpenAI Codex, prompted by Daniel Kodsi. The finite-order interpretation theorem is due to Colin McLarty, using the cited Simpson constructibility results.

The interpretation chain must preserve the arithmetic sort and the quantified Infinity axioms. Equiconsistency alone would not give conservation of individual arithmetic sentences.

**Proof length:** long (4,600 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Frege infinity §§35–36.5 and §36.7; detailed proof §§1–6; McLarty, arXiv:1207.6357v5, §§2–5, pp. 2–6; Uniformity, Arithmetic and Recovery of a Mathematical Core, Theorem 5

**Proofs:** [full-choice-arithmetic-conservativity.md](../proofs/full-choice-arithmetic-conservativity.md) · [infinity-world-richness-consolidation-20261022.md](../source/research/2026-10-22/notes/infinity-world-richness-consolidation-20261022.md) · [relational-coding-recursion-20261022.md](../source/research/2026-10-22/notes/relational-coding-recursion-20261022.md) · [comparison-handoff-20261022.md](../source/research/2026-10-22/notes/comparison-handoff-20261022.md) · [uniformity-arithmetic-core.tex](../papers/uniformity-arithmetic-core.tex)

**Scope evidence:** [infinity_arithmetic_profiles.json](../source/research/2026-10-22/lean-formalization/verification-updates/infinity_arithmetic_profiles.json) · [strong_possibility.json](../source/research/2026-10-22/lean-formalization/verification-updates/strong_possibility.json) · [full-choice-arithmetic-review.json](full-choice-arithmetic-review.json) · [full-choice-arithmetic-delivery.json](full-choice-arithmetic-delivery.json)

<a id="max-arithmetic-equality"></a>
## Proposed exact arithmetic strength of pure Maximalism

**ID:** `MAX-ARITHMETIC-EQUALITY`. Tracked keys: `principles.04`.

The supplied ordinary proof proposes that pure Maximalism proves exactly the ordinary first-order arithmetic consequences of the positive packages’ common arithmetic theory together with all standard-true Π₁ sentences.

$$
\mathrm{Th}_{\mathrm{arith}}(\mathrm{Max}(C))=\mathrm{Cn}\bigl(T_{\mathrm{arith}}\cup\mathrm{True}_{\Pi_1}\bigr).
$$

**Scope:** Finitary pure Maximalism over fixed C, with the fixed Frege interpretation at any fixed counting type. T_arith is the ordinary arithmetic consequence theory shared by C+I and the positive quantified-Infinity packages. Standard truth on the right is metalinguistic; Cn means first-order deductive closure. This is a claim about actual arithmetic theorems, not higher-order/modal conservation or SP consistency.

**Significance:** This gives an exact upper as well as lower bound on Max’s added arithmetic strength. It distinguishes stronger actual arithmetic from the structural and modal benefits of the positive packages, without identifying Max with all arithmetic truth.



**Notes:** The upper inclusion uses an internal Henkin and bounded free-root construction with arithmetic preservation. It still awaits independent review.

**Attribution:** Existing research argument by OpenAI Codex, prompted by Daniel Kodsi, using the explicitly cited external interpretation and completeness theorems. Its promotion from catalog key principles.04 is a presentation change, not a new theorem discovery.

**Proof length:** long (7,849 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Frege infinity §37.1: lower inclusion and initial countermodel; §§37.2–37.7: upper inclusion; §37.8: limits; §37.9: current-choice extension; McLarty, arXiv:1207.6357v5, §§2–5, pp. 2–6; Bacon–Dorr, Classicism, 1 July 2022 draft, §3.1, Theorem 3.2 and footnote 64, pp. 44–45

**Proofs:** [max-arithmetic-equality.md](../proofs/max-arithmetic-equality.md)

**Earlier Lean sources:** [FiniteChoiceBasis.lean](../source/topics/classicism/lean/Classicism/Syntax/FiniteChoiceBasis.lean) · [FregeArithmeticReflection.lean](../source/topics/classicism/lean/Classicism/Results/Research/FregeArithmeticReflection.lean)

<a id="profile-world-algebra"></a>
## Profile Realization and the Boolean structure of worlds

**ID:** `PROFILE-WORLD-ALGEBRA`. Tracked keys: `world_algebra.01`, `world_algebra.05`, `world_algebra.12`, `world_algebra.25`.

The ordinary notes give world-indexed representations over ☐Plenitude, consistent individual profile-realization strengthenings, relational-input diagonal obstructions, and nominal examples with all finite supported richness ranks but without Functional Choice.

**Scope:** Admitted internal fields; original rigid/possible PR and raw world representation are identified only under the stated background. Supported finite-rank richness is not unrestricted realization at relational input types, nor a quantified Infinity axiom.

**Significance:** World richness and Choice are separate dimensions of strength. Individual-profile realization can coexist with failure of Functional Choice, while unrestricted relational-input realization hits a diagonal obstruction.

**Lean certified:** The finite-profile and atomic-profile results.

**Notes:** PR is distinct from the database’s Actual Profile principle. C + ☐Plenitude + Axiom of Infinity (type e) + PR yields the remaining Axiom of Infinity instances; PR does not itself supply Functional Choice.

**Proof length:** long (8,772 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [world-cardinality-ucp-20261022.md](../source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) · [structural-world-representation.md](../source/research/2026-10-22/notes/structural-world-representation.md) · [structural-algebraic-core.md](../source/research/2026-10-22/notes/structural-algebraic-core.md)

**Scope evidence:** [world_actuality_gallin.json](../source/research/2026-10-22/lean-formalization/verification-updates/world_actuality_gallin.json) · [integration-scope-reconciliation.json](integration-scope-reconciliation.json)

**Selected exact certificates:** [certificate.json](certificates/finite-profiles/certificate.json)

<a id="probability"></a>
## Faithful probability has an exact finite-fibre condition and type ceiling

**ID:** `PROBABILITY`. Tracked keys: `choice.18`, `choice.19`, `R02`, `R05`, `R06`, `R07`, `R09`.

Over C + ☐Plenitude + Axiom of Infinity (type e), the ordinary proofs equate faithful probability with admitted finite-fibre numerical labelling of world atoms. Countable Choice for finite fields upgrades this to internal countability. Higher-type probability has a finiteness obstruction.

**Scope:** Internal Dedekind reals and represented families. The weaker version uses Actuality + Atomicity (type t) + Boolean Completeness (type t) + Axiom of Infinity (type e) and graph-valued probabilities in the current core; it need not supply an ambient operation or future-stable real codes.

**Significance:** Faithful probability is controlled by internal world size, with an exact weaker labelling condition before Choice is added. The obstruction becomes stronger as the event type rises.

**Lean certified:** Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.

**Proof length:** long (4,289 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [choice-free-faithful-probability.md](../source/research/2026-10-22/proof-refinements/choice-free-faithful-probability.md) · [choice-free-probability-type-ceiling.md](../source/research/2026-10-22/proof-refinements/choice-free-probability-type-ceiling.md) · [local-propositional-probability.md](../source/research/2026-10-22/proof-refinements/local-propositional-probability.md)

**Earlier saved manifests:** [selected-manifest.json](certificates/probability-source-principal-audit/selected-manifest.json) · [selected-manifest.json](certificates/probability-numeric-operations-twelve/selected-manifest.json) · [selected-manifest.json](certificates/probability-addition-basic/selected-manifest.json)

**Scope evidence:** [probability_internal_constructions.json](../source/research/2026-10-22/lean-formalization/verification-updates/probability_internal_constructions.json) · [integration-scope-reconciliation.json](integration-scope-reconciliation.json) · [certification-closeout.json](certification-closeout.json) · [acceptance.json](certificates/probability-source-principal-audit/acceptance.json) · [acceptance.json](certificates/probability-numeric-operations-twelve/acceptance.json) · [probability-certificate-coverage.json](probability-certificate-coverage.json) · [acceptance.json](certificates/probability-addition-basic/acceptance.json) · [probability-prepared-sources.json](probability-prepared-sources.json)

**Selected exact certificates:** [certificate.json](certificates/final-atomic-probability-concrete-real-addition/certificate.json) · [certificate.json](certificates/probability-source-principal-audit/certificate.json) · [certificate.json](certificates/probability-numeric-operations-twelve/certificate.json) · [certificate.json](certificates/probability-addition-basic/certificate.json)

**Principal declarations:**

- `Classicism.Research.ProbabilityCutCrossing.represented_adjacent_exit`
- `Classicism.Research.ProbabilityCutCrossing.natural_multiple_exceeds_fraction`
- `Classicism.Research.ProbabilityCutCrossing.stepTerm_in_field`
- `Classicism.Research.ProbabilityCutCrossing.stepTerm_zero`
- `Classicism.Research.ProbabilityCutCrossing.stepTerm_suc`
- `Classicism.Research.ProbabilityCutCrossing.cut_step_eventually_outside`
- `Classicism.Research.ProbabilityCutCrossing.cut_has_adjacent_step`
- `Classicism.Research.ProbabilityCutCrossing.cut_has_small_gap`
- `Classicism.Research.ProbabilityRationals.rneg_zero`
- `Classicism.Research.ProbabilityRationals.rneg_reverses`
- `Classicism.Research.ProbabilityRationals.rneg_sub`
- `Classicism.Research.ProbabilityRationals.rsub_sub_self`
- `Classicism.Research.ProbabilityConcreteReals.realNeg_below`
- `Classicism.Research.ProbabilityConcreteReals.realNeg_supported`
- `Classicism.Research.ProbabilityConcreteReals.negative_member_not_neg`
- `Classicism.Research.ProbabilityConcreteReals.realNeg_in_field`
- `Classicism.Research.ProbabilityConcreteReals.realNeg_antitone`
- `Classicism.Research.ProbabilityConcreteReals.realNeg_involution`
- `Classicism.Research.ProbabilityConcreteReals.realAdd_neg`
- `Classicism.Research.ProbabilityConcreteReals.realSub_in_field`
- `Classicism.Research.ProbabilityConcreteReals.realSub_self`
- `Classicism.Research.ProbabilityConcreteReals.realAdd_cancel_right`
- `Classicism.Research.ProbabilityConcreteReals.realAdd_le_iff_le_sub`
- `Classicism.Research.ProbabilityNumericOperations.plus_eq.derivable`
- `Classicism.Research.ProbabilityNumericOperations.times_eq.derivable`
- `Classicism.Research.ProbabilityNumericOperations.plus_graph.derivable`
- `Classicism.Research.ProbabilityNumericOperations.times_graph.derivable`
- `Classicism.Research.ProbabilityNumericOperations.plus_numbers.derivable`
- `Classicism.Research.ProbabilityNumericOperations.times_numbers.derivable`
- `Classicism.Research.ProbabilityNumericOperations.number_induction.derivable`
- `Classicism.Research.ProbabilityNumericOperations.number_cases.derivable`
- `Classicism.Research.ProbabilityNumericOperations.plus_zero_right.derivable`
- `Classicism.Research.ProbabilityNumericOperations.plus_suc_right.derivable`
- `Classicism.Research.ProbabilityNumericOperations.times_zero_right.derivable`
- `Classicism.Research.ProbabilityNumericOperations.times_suc_right.derivable`
- `Classicism.Research.ProbabilityNumericOperations.plus_zero_left.derivable`
- `Classicism.Research.ProbabilityNumericOperations.plus_suc_left.derivable`
- `Classicism.Research.ProbabilityNumericOperations.plus_comm.derivable`

<a id="sp-criteria"></a>
## Strong Possibility is an exact universal-identity theory

**ID:** `SP-CRITERIA`. Tracked keys: `sp_supplement.01`, `sp_supplement.02`, `F13`, `F14`, `F15`.

Over C, pure Strong Possibility is equivalent to the schema of all closed pure universal finite-Boolean-identity sentences individually consistent with Max. With Con(Max) retained, SP is consistent iff Max has the restricted finite-disjunction property for existential finite-Boolean-identity sentences.

**Scope:** Universal prefixes and finite Boolean matrices of typed identities; the terms inside those identities may contain quantifiers. Max-consistency is the original metalinguistic side condition. The disjunction property is a criterion, not a proved property of Max.

**Significance:** SP can be analyzed through jointly realizable universal identity constraints. Its consistency question becomes a precise restricted disjunction question about Max, rather than an unspecified search for richer worlds.

**Lean certified:** The universal-core equivalence and the stated conditional disjunction criterion.

**Notes:** No consistency or inconsistency proof for SP is supplied. The separate elementary-extension embedding criterion has an ordinary proof; the full genuine-Henkin construction is not certified by the twelve checked modules.

**Proof length:** medium (1,175 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [proof-summary.md](../source/research/2026-10-22/lean-formalization/sp-verification/proof-summary.md) · [reflection-universal-core-20261022.md](../source/research/2026-10-22/notes/reflection-universal-core-20261022.md)

**Earlier Lean sources:** [StrongPossibilityConsequencesUniversalCore.lean](../source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesUniversalCore.lean) · [StrongPossibilityConsequencesMaxConservativity.lean](../source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesMaxConservativity.lean)

**Earlier saved manifests:** [20261023T044759304508Z-f503b46f.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044759304508Z-f503b46f.json) · [20261023T044336274999Z-6b5c1cb4.json](../source/research/2026-10-22/lean-formalization/sp-universal-verification/checks/20261023T044336274999Z-6b5c1cb4.json)

**Scope evidence:** [verification-status.json](../source/research/2026-10-22/lean-formalization/sp-verification/verification-status.json) · [verification-status.md](../source/research/2026-10-22/lean-formalization/sp-verification/verification-status.md)

**Principal declarations:**

- `Classicism.Meta.Research.StrongPossibilityConsequences.UniversalCore.sp_consistent_iff_universal_core`
- `Classicism.Meta.Research.StrongPossibilityConsequences.MaxConservativity.identity_conservative_iff_max_consistent`

<a id="sp-signature-conflict"></a>
## Signature SP entails pure SP exactly when signature SP is inconsistent

**ID:** `SP-SIGNATURE-CONFLICT`. Tracked keys: `principles.27`.

For every map-admitted signature Σ, SP(Σ) entails pure SP iff SP(Σ) is inconsistent. More strongly, pure SP is incompatible with signature Max. The reverse implication from pure SP to SP(Σ) holds iff pure SP is inconsistent.

**Scope:** Σ contains at least one relational nonlogical constant; it may be finite or infinite and may also contain individual names. Original finitary syntax and the distinct reference Max theories are retained.

**Significance:** Adding names changes which sentences are Max-consistent. Signature SP therefore need not extend pure SP: their demands conflict, and a proof of the proposed arrow would establish inconsistency of its antecedent.

**Lean certified:** The signature-splitting lemma.

**Notes:** Witness: A is Fregean ∧ ExactlyOneIndividual and U is Atom_t(A). The pure-profile model gives Con(Max(pure)+U); pure SP entails U; two signature-Max instances split A and give ¬U. This proves neither SP theory consistent or inconsistent separately.

**Proof length:** medium (2,053 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** audit-signature-to-pure-sp-20261022.md §§1–5; audit-signature-conservativity-obstruction-20261022.md §§3–6; profile-root-construction-20261022.md §§1–4

**Proofs:** [audit-signature-to-pure-sp-20261022.md](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md) · [audit-signature-conservativity-obstruction-20261022.md](../source/research/2026-10-22/notes/audit-signature-conservativity-obstruction-20261022.md) · [profile-root-construction-20261022.md](../source/research/2026-10-22/notes/profile-root-construction-20261022.md)

**Earlier Lean sources:** [StrongPossibilityConsequencesSignatureSplit.lean](../source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSignatureSplit.lean)

**Earlier saved manifests:** [20261023T044759304508Z-f503b46f.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044759304508Z-f503b46f.json) · [20261023T044336274999Z-6b5c1cb4.json](../source/research/2026-10-22/lean-formalization/sp-universal-verification/checks/20261023T044336274999Z-6b5c1cb4.json)

**Scope evidence:** [proof-summary.md](../source/research/2026-10-22/lean-formalization/sp-verification/proof-summary.md)

**Principal declarations:**

- `Classicism.Meta.Research.StrongPossibilityConsequences.SignatureSplit.maximalist_not_atom_cell`
- `Classicism.Meta.Research.StrongPossibilityConsequences.SignatureSplit.maximalist_add_atom_inconsistent`

<a id="signature-finite-boundary"></a>
## An exact boundary for finite signature extensions

**ID:** `SIGNATURE-FINITE-BOUNDARY`. Tracked keys: `principles.12`.

For a proper extension of finite signatures Σ ⊊ Σ′, Max(Σ′) preserves all Max(Σ)-consistent old-language conditions iff the extension adds exactly one individual name, adds no relational constants, and Σ has no individual names.

**Scope:** Signatures contain only constants of the admitted types. This comparative result also discusses signatures outside the map convention. Equal signatures are the trivial preservation case.

**Significance:** This is a classification, not just a failed generic-expansion argument. It isolates the one harmless finite extension and explains the otherwise conflicting SP schemes.



**Notes:** In the negative cases the two SP theories are incompatible, and each direction of entailment is equivalent to inconsistency of its antecedent. In the positive case the larger-language SP entails the smaller-language SP; no reverse SP implication is asserted.

**Proof length:** medium (2,684 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §§6,9

**Proofs:** [audit-signature-to-pure-sp-20261022.md](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

<a id="signature-infinite-reservoir"></a>
## An infinite reserve of names restores conservativity

**ID:** `SIGNATURE-INFINITE-RESERVOIR`. Tracked keys: `principles.13`.

If Σ ⊆ Σ′ and Σ already has infinitely many constants of every type at which Σ′ adds constants, Max(Σ′) and SP(Σ′) are conservative over the corresponding old-language theories, preserving old-language consistency conditions.

**Scope:** Every proof is finite, so fresh old constants of matching types can replace the finitely many new names it uses. No generic expansion of each individual model is asserted.

**Significance:** Finite-signature nonconservativity and infinite-language conservativity have different mechanisms. The supply of unused names is the exact hypothesis used by this positive result.



**Proof length:** short (465 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §8

**Proofs:** [audit-signature-to-pure-sp-20261022.md](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

<a id="sp-individual-cardinality"></a>
## SP fixes the actual domain from the number of individual names

**ID:** `SP-INDIVIDUAL-CARDINALITY`. Tracked keys: `principles.27`.

If Σ has exactly u < ∞ individual constant symbols, SP(Σ) entails exactly max(1,u) actual individuals. For u ≥ 1 the individual names enumerate the domain bijectively. Pure SP therefore entails exactly one actual individual.

**Scope:** The relational part of Σ may be infinite. This is an actual-domain assertion, not a boxed cardinality claim. No exhaustion claim is made for infinitely many individual names.

**Significance:** SP has a much sharper cardinal consequence than an informal plenitude reading suggests. Adding individual names can change the forced actual cardinality and make theories incompatible.

**Lean certified:** The conditional monism/reflection lemma.

**Notes:** The Max-consistent profile-root cardinality sentence transfers by universal-identity reflection; signature Max makes distinct individual name symbols denote distinct actual individuals. This remains a consequence of SP, not an SP consistency proof.

**Proof length:** medium (1,894 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §10

**Proofs:** [audit-signature-to-pure-sp-20261022.md](../source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

**Earlier Lean sources:** [StrongPossibilityConsequencesSchemas.lean](../source/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSchemas.lean)

**Earlier saved manifests:** [20261023T044759304508Z-f503b46f.json](../source/research/2026-10-22/lean-formalization/checks/20261023T044759304508Z-f503b46f.json) · [20261023T044336274999Z-6b5c1cb4.json](../source/research/2026-10-22/lean-formalization/sp-universal-verification/checks/20261023T044336274999Z-6b5c1cb4.json)

**Scope evidence:** [proof-summary.md](../source/research/2026-10-22/lean-formalization/sp-verification/proof-summary.md)

<a id="sp-finite-profile-rank"></a>
## Pointed theories determine the finite Boolean intervals forced by SP

**ID:** `SP-FINITE-PROFILE-RANK`. Tracked keys: `principles.10`, `principles.11`, `principles.26`, `principles.28`.

For closed pure A, let S_A be the space of complete consistent theories extending C(a)+A for one fresh individual name a. Max + Width_k(A) is consistent iff S_A has at most k members. If S_A has exactly finite k members, pure SP forces exactly k atoms and 2^k elements below A.

**Scope:** k is an external fixed finite number; Width_k excludes k+1 disjoint nonzero subpropositions. When S_A is infinite, Max already refutes each finite width bound.

**Significance:** The atom obstruction is one case of a general classification. It computes entire finite intervals of the propositional algebra from pointed logical possibilities.



**Notes:** The finite-signature notes refine the cell counts using pointed isomorphism orbits. None of the profile models is asserted to satisfy full SP.

**Proof length:** medium (2,311 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** sp-finite-profile-rank-20261022.md §§1–5; finite-c5-profile-cells-20261022.md §§1–8; finite-c5-signature-cells-20261022.md

**Proofs:** [sp-finite-profile-rank-20261022.md](../source/research/2026-10-22/notes/sp-finite-profile-rank-20261022.md) · [finite-c5-profile-cells-20261022.md](../source/research/2026-10-22/notes/finite-c5-profile-cells-20261022.md) · [finite-c5-signature-cells-20261022.md](../source/research/2026-10-22/notes/finite-c5-signature-cells-20261022.md)

<a id="sp-barcan-functionality"></a>
## Finite-signature SP refutes BF and Functionality at every input type

**ID:** `SP-BARCAN-FUNCTIONALITY`. Tracked keys: `principles.29`.

For every finite signature Σ, including the empty signature, SP(Σ) refutes BF (type α) at every admitted α and every Functionality instance with input α and relational output β. Explicit counterpredicates and pairs of operations witness the failures.

**Scope:** For an infinite relational signature with finitely many individual names, only the individual-input result is extended by this proof. Relational-input failures use a finite complete signature diagram.

**Significance:** The failure is type-by-type, including individual inputs, rather than merely failure of an all-type conjunction. Future domains contain values not transported from the actual domain.



**Notes:** A failed schema has a counterinstance; not every formula or every pair of operations is a counterexample. Consistency of the SP antecedent remains unresolved.

**Proof length:** long (3,465 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** signature-sp-barcan-20261022.md §§1–7; finite-c5-profile-cells-20261022.md §9

**Proofs:** [signature-sp-barcan-20261022.md](../source/research/2026-10-22/notes/signature-sp-barcan-20261022.md) · [finite-c5-profile-cells-20261022.md](../source/research/2026-10-22/notes/finite-c5-profile-cells-20261022.md)

<a id="sp-arithmetic-reflection"></a>
## Pure SP proves true Π₂ arithmetic, with a sharp conditional boundary

**ID:** `SP-ARITHMETIC-REFLECTION`. Tracked keys: `F14`.

Pure SP proves every true Π⁰₂ arithmetic sentence under the specified pure Frege-arithmetic translation. More generally, if C + I_e proves every standard numeral instance of a fixed pure P(n), SP proves its universal numerical closure. If SP is consistent, some true Π⁰₃ sentence is not an SP theorem.

**Scope:** The one-step ω-rule has C + I_e as its reference theory. It uses external separate finite proofs, not an infinitary object-language formula. It is not an iterated ω-rule for SP.

**Significance:** This exhibits a concrete arithmetic gain over Max and a limit to that gain. The reflection principle is stronger than merely recognizing a list of familiar arithmetic axioms.



**Notes:** The ordinary argument uses the standard-arithmetic Max model and the stated arithmetic interpretation. The upper-bound conclusion retains Con(SP); no standard-arithmetic SP model is supplied.

**Proof length:** medium (1,587 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** “A one-step omega-rule consequence of pure SP”; “Pure SP contains true Pi^0_2 arithmetic”; “The arithmetic correctness bound is sharp if SP is consistent”

**Proofs:** [strong-possibility.md](../source/research/2026-10-22/followup/strong-possibility.md)

<a id="npc-atomicity"></a>
## Atomicity under C5 removes pure contingency

**ID:** `NPC-ATOMICITY`. Tracked keys: `synthesis.npc-atomicity`.

C5 plus Atomicity (type t) entails No Pure Contingency: each closed pure sentence, if true, is necessary.

**Scope:** C5 is C + ☐ND. The theorem holds at every admitted signature, with its conclusion restricted to pure sentences.

**Significance:** Atomic world structure turns modal stability into necessity for pure truths, and supplies the key step in the strong-section characterization of necessary Choice.

**Lean certified.**

**Attribution:** Goodsell and Yli-Vakkuri theorem; existing writeup following Cian Dorr’s sketch. This collection adds formalization evidence, not mathematical authorship.

The proof swaps two Boolean atoms, extends the swap by conjugation through every relational type, and proves that every closed pure term is fixed. The final contradiction is short once this invariance is established.

**Proof length:** medium (1,146 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [c5-and-atomicity-imply-no-pure-contingency.md](../source/topics/classicism/writeups/c5-and-atomicity-imply-no-pure-contingency.md)

**Selected exact certificates:** [certificate.json](certificates/npc/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.NPC.c5_and_atomicity_t_imply_no_pure_contingency`

<a id="colour-collapse-scope"></a>
## Rigid Power at one type does not close the rigidity gap

**ID:** `COLOUR-COLLAPSE-SCOPE`. Tracked keys: `synthesis.colour-collapse-scope`.

The colour-collapse model satisfies Tame Rigidity and ☐BF, together with ☐Rigid Power (type et), but fails Weakly Rigid Power (type et). It also fails Rigid Power (type (et)t).

**Scope:** This is a single-type separation. The same model cannot refute the implication from full Tame Rigidity plus full Rigid Power to full Weakly Rigid Power.

**Significance:** Moving to the next property type changes the verdict. The distinction explains why a convincing local counterexample does not answer the full-schema question.

**Lean certified.**

The model proof classifies rigid unary relations as finite or whole and shows how they lift; the higher-power obstruction explains why this construction alone cannot settle the full-schema question.

**Proof length:** medium (2,995 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [colour-collapse-entrance.md](../source/research/2026-10-22/notes/colour-collapse-entrance.md) · [colour-collapse.md](../proofs/colour-collapse.md)

**Selected exact certificates:** [certificate.json](certificates/colour-collapse/certificate.json) · [certificate.json](certificates/colour-collapse-higher/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Intensional.ColourCollapse.central_countermodel`

<a id="diagonal-characters"></a>
## Stable atoms are exactly what diagonal separation requires

**ID:** `DIAGONAL-CHARACTERS`. Tracked keys: `synthesis.diagonal-characters`.

Separation of propositions by diagonal characters is equivalent over C to ND (type t) together with Atomicity (type t).

**Scope:** For $E^{tt}$, put

$$
w_E:=\forall p^t\, .\,Ep\to p.
$$

A diagonal character preserves bottom and negation, has only top or bottom as each current value, and accepts $w_E$.

**Significance:** A single diagonal acceptance condition replaces a much larger quantifier-preservation demand. Each character determines a necessarily nonbottom atom; no Barcan, C5 or Choice assumption is needed.

**Lean certified.**

**Notes:** The reconstruction is pointwise identity of outputs, not identity between operations. Stable nonbottomness does not assert necessary atomhood.

**Proof length:** medium (1,030 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [diagonal-characters.md](../proofs/diagonal-characters.md)

**Selected exact certificates:** [certificate.json](certificates/diagonal-characters/certificate.json)

**Principal declarations:**

- `Classicism.Research.DiagonalCharacters.separation_iff_nd_atomicity.derivable`
- `Classicism.Research.DiagonalCharacters.diagonal_stable_atom.derivable`
- `Classicism.Research.DiagonalCharacters.diagonal_pointwise.derivable`

<a id="evaluator-modal-commutation"></a>
## An actual evaluator commuting with modality forces Extensionality

**ID:** `EVALUATOR-MODAL-COMMUTATION`. Tracked keys: `synthesis.evaluator-modal-commutation`, `choice.11`.

Existence of an actual truth evaluator that commutes with box is equivalent to Extensionality. The same is true with diamond in place of box.

**Scope:** An actual evaluator sends each currently true proposition to top and each currently false proposition to bottom. Commutation is pointwise identity.

**Significance:** Correct evaluation can coexist with intensional distinctions; requiring it to commute with modality makes those distinctions collapse.

**Lean certified.**

**Proof length:** short (309 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [gallin-bivalent-evaluator.md](../source/research/2026-10-22/notes/gallin-bivalent-evaluator.md)

**Scope evidence:** [integration-scope-reconciliation.json](integration-scope-reconciliation.json)

**Selected exact certificates:** [certificate.json](certificates/evaluator-modal/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.EvaluatorModalCommutation.box_evaluator_iff_extensionality_in`
- `Classicism.Meta.Research.EvaluatorModalCommutation.diamond_evaluator_iff_extensionality_in`

<a id="coextension-operations"></a>
## Canonical operations on coextension classes require Actuality

**ID:** `COEXTENSION-OPERATIONS`. Tracked keys: `synthesis.coextension-operations`.

At any fixed relational type with nonempty argument domains, Actuality is equivalent to an extension-preserving operation whose internal invariant closure exhausts every actual coextension class. Finite iteration of coextension-class coding preserves all selector ambiguity.

**Scope:** Internal invariant closure is defined using admitted invariant predicates, not an external finite orbit. The code operations have explicit literal left inverses.

**Significance:** These results explain why two natural attempts to derive coherent selectors from Relational Choice alone need extra structure. They leave the weaker Relational Choice to Transversal Choice question unresolved.

**Lean certified:** Orbit averaging and finite code towers; orbit/Actuality equivalence at t and inhabited unary types.

**Notes:** The code rules cover tuple inputs, including the empty tuple, and every closed admitted chooser-output type. Finite towers use split/composition.

**Proof length:** medium (1,118 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [coextension-operations.md](../proofs/coextension-operations.md)

**Selected exact certificates:** [certificate.json](certificates/orbit-code-towers/certificate.json)

<a id="logical-observers"></a>
## Logical observer separation: a strict hierarchy from BF to Extensionality

**ID:** `LOGICAL-OBSERVERS`. Tracked keys: `synthesis.logical-observers`.

Over H, OS entails C + BF; full typed endpoint separation is equivalent to C5 + Atomicity (type t), and full typed factive separation is equivalent to Extensionality. Over C, the strict hierarchy is Extensionality ⇒ C5 + Atomicity (type t) ⇒ ☐OS ⇒ OS ⇒ BF. Atomicity (type t) + BF implies OS. Over C5 + Actuality, OS, ☐OS and Atomicity (type t) are equivalent. Over C5, ☐OS + ◇Actuality entails ☐Plenitude; replacing ☐OS by OS does not suffice. Given OS, uniqueness of the qualified logical observer is equivalent to Extensionality. Reversible separation is equivalent to involutive separation and to its separately boxed schema, and entails C5 + ☐OS. Reversible separation together with Actuality, one atom, or one qualified observer at t with finitely many outputs is equivalent to endpoint separation. Finite-image separation is incomparable with reversible separation, C + Atomicity (type t) + BF, and ☐OS. Under C5, propositional atoms correspond bijectively to endpoint observers qualified at t. In the propositional conjunction/universal fragment, requiring jointly qualified observers is strictly stronger over H than requiring separate separating classes. Over C, universal separation and joint separation are equivalent to the corresponding unboxed BF instances for each finite type list. Over C, each singleton connective-preservation separation principle holds, while any two of conjunction, disjunction and negation preserved by the same observers give Boolean separation. Top-accepting identity-fixing separation at t is exactly ND (type t); adjoining universal preservation at the finite list Δ gives ND (type t) + BF at Δ, hence C5 when t belongs to Δ. Over C, an endpoint-fixing operator with range {⊤,⊥} exists exactly when modal .2 holds. Over C5, propositional separation by Boolean observers preserving the universal quantifier at t is equivalent to full OS. Over C, either of the accepting, identity-fixing mixed N/Q_t or V/Q_t separation formulas characterizes C5 + OS. The finite-support natural-numbers/singleton all-maps model gives OS with failure of ☐BF_e, ☐BF_t and ☐Functionality at (e,t). Under C5, ☐OS plus one atom is equivalent to endpoint separation; the single boxed propositional Good_{ {t} } separation formula suffices. Reversible logical separation implies No Pure Contingency without atoms or Actuality. The implication from reversible separation to C5 + ☐OS is strict even in atomless models. The finite-block symmetry countermodel makes the pure six-element subset-selection sentence contingent. Reversible separation is equivalently logical separation by necessarily bijective observers; over C it is also separation by invertible universal-preserving observers at finite type lists containing t. Full separation by observers with admitted qualified right inverses is exactly reversible separation. Qualified left-inverse separation is strictly weaker, even with C5 and its own boxed schema; it implies OS but does not imply C5, ☐OS, its own boxed schema, ☐BF or ☐Functionality. Separate full endpoint-fixing M/Q/P, V/Q/P and N/Q/P separation, even with all their boxed instances and boxed BF and Functionality, does not imply Boolean separation: the ternary Cantor model refutes the unrestricted mixed-quantifier reductions. The arrow from qualified left-inverse separation to OS is also strict, and SplitMono is incomparable with ☐OS. Under internal finiteness of all propositions, full SplitMono, Rev and endpoint separation coincide. Even C5 + ☐SplitMono + No Pure Contingency does not imply Rev. Rev implies the stronger noncontingency schema for pure formulas with finitely many individual parameters and endpoint-valued first-order relation parameters. Over C + BF, each fixed-list left-inverse separation instance is equivalent to the corresponding reversible instance or ordinary separation together with one qualified left-inverse pair having a true kernel element. Full H scope gives an external schema of such alternatives, not a global disjunction. If every admitted injective proposition operation is onto, full left-inverse and reversible separation coincide; the two-colour atomless model satisfies this condition and Rev while endpoint separation fails. Over H, endpoint separation is equivalent to OS + Plenitude at (t,t), OS + full Plenitude, C5 + OS + Actuality, C5 + OS + Boolean Completeness, and C5 + Atomicity (type t). Already C + BF (type t) + Plenitude at (t,t) is equivalent to C5 + Actuality. Over C5, each currently surjective Good observer at a finite list containing t has a definable admitted same-list qualified right inverse; hence Rev is equivalent over H to C5 + full surjective logical separation. Both chains Rev ⇒ SurjSep ⇒ OS and Rev ⇒ SplitMono ⇒ OS are strict. SurjSep and SplitMono are incomparable even over C + ☐BF + ☐OS, witnessed by the full omega-chain and the C5 finite-block model. Within C5, SurjSep is Rev and does imply SplitMono. The linear/circular fibre model satisfies C5 + ☐OS + D_t with atomless propositions but fails SplitMono at the explicit propositional list {t,e,et,eet,(et)t,((et)t)t}; a contingent closed pure sentence about infinite amorphous cells proves the obstruction. A specified countably infinite sequence fixed by a source symmetry group in the all-bijections finite-pinning framework gives one qualified left-inverse pair with a true kernel element, normalizing ordinary separators at that source. At the trivial-symmetry object of the qualitative-contrast model, C5 + SplitMono holds but ☐OS and ☐SplitMono fail. Thus SplitMono and ☐OS are incomparable even over C5. Every full cancellative-monoid action model with singleton individuals satisfies separately boxed full SurjSep. A specified infinite sequence of distinct units also gives separately boxed full SplitMono, with one common qualified left inverse. A nonunit refutes C5. The concrete monoid ℤ×ℕ therefore refutes ☐SurjSep + ☐SplitMono ⇒ Rev, even over C + ☐BF. SurjSep + SplitMono lies strictly below Rev and strictly above each factor; its two witness families may be different. Over C + BF (type t), Onto(E) implies ☐Onto(E), with E a free parameter; Good qualification is persistent over C. Full SurjSep nevertheless gives neither ☐OS nor ☐SurjSep, even with ☐BF and ☐Functionality. A root truth-profile extension of a fixed/free symmetry tail supplies this countermodel, with failure already at the future propositional Boolean instance. Thus Rev ⇒ ☐SurjSep ⇒ SurjSep and ☐SurjSep ⇒ ☐OS are strict. SurjSep does not imply ☐BF, with failure at every admitted type in the integer-shift predecessor model. Over C5, every admitted Good-{t} observer E has admitted order adjoints L ⊣ E ⊣ R, with Rq=∃p[(Ep≤q)∧p] and Lq=¬R(¬q). With k=RBottom and a=¬k, R(Ep)=p∨k and L(Ep)=p∧a, giving a Boolean order isomorphism from [Bottom,a] onto the admitted image. Injectivity is equivalent to RBottom=Bottom or LTop=Top; onto is equivalent to join preservation by R or meet preservation by L; bijectivity is equivalent to R=L or negation preservation by either adjoint. The admitted image floor ER and ceiling EL are idempotent, with ER≤I≤EL and mutual absorption. ER is an auxiliary S5 interior and equals native Box exactly when E is endpoint-valued. The endpoint-fixing envelopes T−q=(a∧Rq)∨(k∧q) and T+q=Lq∨(k∧q) preserve M/all Q and V/all P respectively, and coincide exactly when E is onto. Already for a Boolean E over C5, commuting with native Box or Diamond is exactly injectivity, without Q_t. The integer-shift predecessor model satisfies C + full typed SurjSep + BF while ☐BF_σ fails at every admitted type σ. In the finite-pinning tail over ℕ×ℤ and {∗}×ℤ, split epimorphisms approximate finite pins and invertible integer translations supply prescribed-coordinate kernel pairs. The root truth-profile extension combines all-type evaluation readers with those onto tails. A future object has nononto transport at every type and refutes every BF instance. Hence SurjSep ⇒ ☐BF is refuted with exact all-type scope.

**Scope:** Observers preserve Boolean and quantifier operations by identities between the composite operations, at each finite list of types. Endpoint observers satisfy ∀p(Ep = ⊤ ∨ Ep = ⊥); factive observers satisfy ∀p(Ep → p). Over C, the single propositional endpoint-separation instance testing quantifiers at t already characterizes C5 + Atomicity (type t), and its separately boxed form is equivalent. Over H, the recovery of C uses the full typed schema. The equality laws are redundant over C; they support the H proof transformation. Finite image is expressed by the database’s Frege FiniteCardinality at t, with no common bound and no assumption that internal finiteness has an externally finite extension. The single finite-image witness need not itself separate. Endpoint truth follows from Boolean preservation over H, and endpoint identity over C. Including explicit endpoint identities gives an equivalent full separation theory over H, although standalone qualification there can be stronger. The conjunction/universal comparisons concern propositional separation; the displayed strict witnesses test type t. Relational extension requires Functionality. Fixing identity judgments means the full composite identity (λp,q.E(p=q))=(λp,q.p=q). This fragment differs from identity-fixing logical separation, which is C5 + OS. The comparisons form a proved fragment; reversible separation is strictly stronger than C5 + ☐OS, including in the atomless case. The H observer atlas records the full typed factorization and independent-primitive distinctions separately. The reduction to Q_t assumes C5 and uses full composite identities. The endpoint-parameter schema covers relations of types eⁿt with n ≥ 1, not arbitrary higher-type parameters. The component-shift countermodel uses a restricted group of arrows, so it does not contradict the one-object all-bijections sufficient theorem. The adjoint tests concern individual observers over C5, not separation principles. The native modal commutation criterion needs Boolean qualification only; the adjoints require Good-{t}. Their construction uses admitted families and lambda terms, with no external completeness or Choice. The integer-shift model has current BF at its root, not necessary BF; its negative verdict holds at every admitted type.

**Significance:** Restrictions on the observers characterize both C5 + Atomicity and Extensionality. Ordinary OS has atomless models and adds structure beyond BF without requiring Actuality or ND. Over C, making the finite qualification necessary adds no strength, while requiring separation necessarily does. Reversibility forces the proposition algebra to be either atomless or atomic with a true atom; a single finite-image observer selects the latter case.

**Lean certified:** H + OS ⇒ C + BF with explicit endpoint identities. Their omission is justified by the linked ordinary reduction proof.

**Notes:** The no-conjunction obstruction inherits the source countermodels’ metatheoretic qualifications. It does not exclude arbitrary Boolean combinations involving disjunction. The composite qualification does not inherit certificates for other observer qualifications. The endpoint-clause reduction is in logical-observer-endpoint-reduction.md; the saved formal certificate retains explicit endpoint identities.

**Proof length:** long (66,238 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Right-inverse separation §§1–4; left-inverse models §§1–7; ternary Cantor model §§1–9; modal selectors §§6–7.; Fork and finite boundary §§1–5; component-shift model §§1–8; endpoint-parameter noncontingency §6.; Left-inverse decomposition §§1–6; finite colour-pattern propositions §§1–5.; Plenitude/endpoint bridge §§1–5; surjective observers §§1–7; linear/circular fibre model §§1–10; omega-chain observer classification §§1–6.; fixed-point symmetry §§1–7; cancellative monoid observers §§1–7.; root truth-profile surjective separation §§1–7.; Canonical adjoints §§2–7; integer-shift predecessor §§1–7.

**Proofs:** [logical-observer-hierarchy.md](../proofs/logical-observer-hierarchy.md) · [logical-observers.md](../proofs/logical-observers.md) · [operator-representation.md](../proofs/operator-representation.md) · [full-identity-observers.md](../proofs/full-identity-observers.md) · [observer-models.md](../proofs/observer-models.md) · [observer-countermodel.md](../proofs/observer-countermodel.md) · [local-observers.md](../proofs/local-observers.md) · [logical-observer-endpoint-reduction.md](../proofs/logical-observer-endpoint-reduction.md) · [meet-quantifier-separation.md](../proofs/meet-quantifier-separation.md) · [observer-lattice.md](../proofs/observer-lattice.md) · [observer-lattice-models.md](../proofs/observer-lattice-models.md) · [modal-selectors-and-quantifier-reduction.md](../proofs/modal-selectors-and-quantifier-reduction.md) · [logical-separation-with-contingent-barcan.md](../proofs/h-observer-space/logical-separation-with-contingent-barcan.md) · [necessary-separation-and-atoms.md](../proofs/h-observer-space/necessary-separation-and-atoms.md) · [reversible-separation-and-pure-truth.md](../proofs/h-observer-space/reversible-separation-and-pure-truth.md) · [finite-block-symmetry-reversible-gap.md](../proofs/h-observer-space/finite-block-symmetry-reversible-gap.md) · [reversible-quantifier-observers.md](../proofs/h-observer-space/reversible-quantifier-observers.md) · [local-conjugacy-and-reversible-observers.md](../proofs/h-observer-space/local-conjugacy-and-reversible-observers.md) · [split-inverse-logical-observers.md](../proofs/h-observer-space/split-inverse-logical-observers.md) · [finite-block-symmetry-left-inverse.md](../proofs/h-observer-space/finite-block-symmetry-left-inverse.md) · [ternary-cantor-observer-model.md](../proofs/h-observer-space/ternary-cantor-observer-model.md) · [fork-one-sided-inverse-separation.md](../proofs/h-observer-space/fork-one-sided-inverse-separation.md) · [component-shift-symmetry-reversible-gap.md](../proofs/h-observer-space/component-shift-symmetry-reversible-gap.md) · [left-inverse-separation-decomposition.md](../proofs/h-observer-space/left-inverse-separation-decomposition.md) · [finite-pinning-dedekind-propositions.md](../proofs/h-observer-space/finite-pinning-dedekind-propositions.md) · [plenitude-endpoint-bridge.md](../proofs/h-observer-space/plenitude-endpoint-bridge.md) · [surjective-logical-observers.md](../proofs/h-observer-space/surjective-logical-observers.md) · [linear-circular-fibre-left-inverse-gap.md](../proofs/h-observer-space/linear-circular-fibre-left-inverse-gap.md) · [omega-chain-surjective-observers.md](../proofs/h-observer-space/omega-chain-surjective-observers.md) · [fixed-point-symmetry-left-inverse-separation.md](../proofs/h-observer-space/fixed-point-symmetry-left-inverse-separation.md) · [full-cancellative-monoid-observers.md](../proofs/h-observer-space/full-cancellative-monoid-observers.md) · [root-truth-profile-surjective-separation.md](../proofs/h-observer-space/root-truth-profile-surjective-separation.md) · [canonical-adjoints-and-image-factorization.md](../proofs/h-observer-space/canonical-adjoints-and-image-factorization.md) · [integer-shift-predecessor-contingent-barcan.md](../proofs/h-observer-space/integer-shift-predecessor-contingent-barcan.md)

**Earlier saved manifests:** [original-manifest.json](certificates/full-typed-logical-separation-actual-c/original-manifest.json)

**Scope evidence:** [certification-closeout.json](certification-closeout.json) · [acceptance.json](certificates/full-typed-logical-separation-actual-c/acceptance.json)

**Selected exact certificates:** [certificate.json](certificates/final-full-typed-logical-separation-h-transport/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-h-bridge/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-h-closure/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-h-consequences/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-c-holes/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-c-transport/certificate.json) · [certificate.json](certificates/full-typed-logical-separation-actual-c/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.FullTypedLogicalSeparation.actual_c_sequent`
- `Classicism.Meta.Research.FullTypedLogicalSeparation.actual_c_theorem`
- `Classicism.Meta.Research.FullTypedLogicalSeparation.h_full_logical_separation_actual_c`

<a id="analytic-rigidification"></a>
## Rigid Comprehension stabilizes a possible real structure

**ID:** `ANALYTIC-RIGIDIFICATION`. Tracked keys: `synthesis.analytic-rigidification`.

Over C5 plus ☐Rigid Comprehension, a possible real structure at a fixed type has a rigid representative which is necessarily a real structure. Represented powers can be supplied simultaneously at each prescribed finite list of arities.

**Scope:** The initial possibility premise remains. Completeness concerns nonempty bounded internal subproperties; represented powers are not external full powersets.

**Significance:** The result carries internal analysis across worlds without assuming Atomicity or external fullness.

**Lean certified:** Rigidification and simultaneous represented powers of every prescribed finite list of positive arities, at every closed admitted type and in arbitrary signatures.

**Attribution:** Existing analytic-necessitism argument credited to Goodsell and Claude Fable 5.1, following Bacon; current work supplies the indicated formalization.

**Proof length:** short (486 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [analytic-rigidification.md](../proofs/analytic-rigidification.md)

**Scope evidence:** [certification-closeout.json](certification-closeout.json)

**Selected exact certificates:** [certificate.json](certificates/analytic-rigidification/certificate.json) · [certificate.json](certificates/final-analytic-reuse-quotation/certificate.json) · [certificate.json](certificates/final-analytic-finite-packing/certificate.json) · [certificate.json](certificates/final-analytic-power-existence-certificates/certificate.json) · [certificate.json](certificates/final-analytic-power-vocabulary/certificate.json) · [certificate.json](certificates/final-analytic-finite-schema/certificate.json)

<a id="full-standard-gallin"></a>
## External atomic joins characterize full Gallin hierarchies

**ID:** `FULL-STANDARD-GALLIN`. Tracked keys: `synthesis.full-standard-gallin`.

Over C + C5 + Atomicity (type t), Arbitrary Atomic Joins at every relational type is equivalent to fullness of the canonical standard hierarchy. Equivalently, every subset of each typed domain is the actual extension of an admitted property. No fixed bound on the indexed families suffices across arbitrary model sizes.

**Scope:** Set-sized models in ZFC; C5 is ☐ND at all types. The canonical principal-world representation is derived from the stated premises. Neither Choice nor either Axiom of Infinity is an additional object-language premise.

**Significance:** Internal Boolean Completeness ranges over admitted families. External atomic joins specify the additional closure needed to recover every external subset and function.



**Notes:** Full validity is computably equivalent to full second-order validity. A sound atomic-join rule exists, but set-coded proofs with uniformly parameter-free Σ₁ admissibility cannot be complete; the result does not exclude every conceivable calculus.

**Proof length:** long (3,902 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [full-gallin.md](../proofs/full-gallin.md) · [atomic-join-calculus.md](../proofs/atomic-join-calculus.md) · [infinitary-canonical-representation.md](../proofs/infinitary-canonical-representation.md)

<a id="forcing-transfer"></a>
## The full modalized cloud realizes both sides of CH

**ID:** `FORCING-TRANSFER`. Tracked keys: `synthesis.forcing-transfer`.

In the specified full modalized-domain construction, recursive normal forms identify every finite relational type with its Boolean-valued counterpart. The lottery cloud therefore makes both CH and its negation possible for real structures at the same fixed type et.

**Scope:** The comparison concerns the explicitly full construction. Generic quotients are full relative to the forcing extension. Real completeness uses nonempty bounded internal subproperties.

**Significance:** The construction connects modal variation in mathematics to forcing semantics. Existing full-action models refute the abstract implication under the database’s strict-smallness convention; exact correspondence with the attributed source formulation remains unresolved.



**Notes:** The model-specific comparison does not identify the separate lottery presentations. The strict-smallness audit preserves the attributed source statement and distinguishes the encoded countermodels from a refutation of the intended source theorem. Completeness uses nonempty bounded subsets; the countermodels contain actual real structures.

**Attribution:** Underlying modalized-domain construction: Andrew Bacon and Claude Opus 5.5 (Anthropic), 20 October 2026 draft. The typed comparison is original research, source misc.

**Proof length:** long (5,756 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [forcing-transfer.md](../proofs/forcing-transfer.md) · [forcing-reals.md](../proofs/forcing-reals.md)

**Scope evidence:** [forcing-formulation.md](../proofs/forcing-formulation.md)

<a id="finite-compression-separation"></a>
## TR + RP does not imply WRP

**ID:** `FINITE-COMPRESSION-SEPARATION`. Tracked keys: `synthesis.finite-compression-separation`.

A finite compression labelled entrance model satisfies Tame Rigidity and Rigid Power, but refutes Weakly Rigid Power (type et).

**Scope:** The root has infinitely many individuals. The model fails BF (type e) and ☐Tame Rigidity; the separation does not include these extra premises.

**Significance:** This answers the full-schema TR + RP to WRP question negatively. It is stronger than the earlier single-type colour-collapse separation.

**Lean certified.**

**Notes:** Section 10 also refutes the inverse-image preservation shortcut under TR, RP and WRP.

Compression and return maps remove label parameters from rigid subrelations, while approximate lifting supplies Rigid Power at every type.

**Proof length:** long (3,131 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [finite-compression.md](../proofs/finite-compression.md)

**Selected exact certificates:** [certificate.json](certificates/finite-compression/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Intensional.FiniteCompression.central_countermodel`
- `Classicism.Meta.Intensional.FiniteCompression.not_entails_weakly_rigid_power`

<a id="lambda-free-translation"></a>
## Classicism can be reconstructed without primitive lambda

**ID:** `LAMBDA-FREE-TRANSLATION`. Tracked keys: `synthesis.lambda-free-translation`.

An explicit classical lambda-free applicative calculus has exactly C’s consequences in its original language, including open contexts and finite lists of assumptions. A conservative named extension reconstructs arbitrary C terms and full contextual beta eta delta conversion.

**Scope:** The base retains object quantifier binders, typed equality, existence at e, a first-class necessity operation, K, theorem-only necessitation, Intensionality at every relational type including t, and finite-body uniform strong comprehension. No Choice, BF or Infinity is added. The exact equivalence uses actual C.Derivable. Optional purity-sensitive or reference-theory-sensitive schemas require their own translation argument.

**Significance:** Abstraction, beta eta identities, quantifier operators and the literal box operator can be recovered from uniform representation. Unrestricted globally necessitable epsilon instead collapses modality.

**Lean certified.**

**Notes:** Decoding compiled terms gives a provable object identity in C.

The proof constructs bracket abstraction, substitution coherence and both term round trips, then conservatively erases the finitely many names used by each proof.

**Proof length:** long (9,373 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [lambda-free-reconstruction.md](../proofs/lambda-free-reconstruction.md) · [lambda-logical-operators.md](../proofs/lambda-logical-operators.md) · [lambda-finite-name-erasure.md](../proofs/lambda-finite-name-erasure.md) · [bracket-abstraction.md](../proofs/bracket-abstraction.md)

**Selected exact certificates:** [certificate.json](certificates/stable-naming/certificate.json) · [certificate.json](certificates/representation-core/certificate.json) · [certificate.json](certificates/lambda-free-reconstruction/certificate.json)

**Principal declarations:**

- `Classicism.Research.ModalLambdaFreeEquivalence.classical_lambda_free_iff_C`
- `Classicism.Research.ModalLambdaFreeEquivalence.classical_lambda_free_theorem_iff_C`
- `Classicism.Research.ModalNamedToC.named_derives_toC`

<a id="beta-eta-conversion"></a>
## Beta identity plus a theorem rule yields contextual beta eta

**ID:** `BETA-ETA-CONVERSION`. Tracked keys: `synthesis.beta-eta-conversion`.

On raw typed lambda syntax, beta identity at every relational output type, ordinary application congruence and the theorem-only fresh-variable rule from Fx=Gx to F=G derive eta, lambda congruence and every contextual beta eta conversion.

**Scope:** Positive-arity Intensionality, generalization and theorem-only necessitation already supply the fresh-variable rule; nullary Intensionality is unnecessary for this conversion result. Primitive lambda formation and beta identities at all relational output types remain assumed. Conversion transfers derivations while leaving optional premises unchanged.

**Significance:** The proof identifies a sufficient conversion basis without assuming eta or lambda congruence in the raw equality calculus. It does not eliminate lambda term formation or prove a minimal basis.

**Lean certified.**

**Notes:** Beta identity alone with the full intended equality calculus remains unresolved here. Bacon–Dorr’s H0 plus saturated material zeta-Equivalence result is a separate source-reported positive theorem; the weaker unary beta counterexample does not refute it.

**Proof length:** short (694 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [beta-eta.md](../proofs/beta-eta.md) · [beta-reduced-bases.md](../proofs/beta-reduced-bases.md)

**Selected exact certificates:** [certificate.json](certificates/beta-eta/certificate.json) · [certificate.json](certificates/beta-positive-arity/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.BetaIdentity.contextual_conversion_sound`
- `Classicism.Meta.Research.BetaIdentity.ModalBridge.contextual_conversion`
- `Classicism.Meta.Research.BetaIdentity.PositiveArityModalBridge.contextual_conversion`

<a id="finite-type-propagation"></a>
## Finiteness is classified by the base types occurring in a type

**ID:** `FINITE-TYPE-PROPAGATION`. Tracked keys: `synthesis.finite-type-propagation`.

Under the Functionality instances in its type tree, a relational type containing no e is finite iff t is finite; one containing e is finite iff both e and t are finite. The downward implications already hold over bare C. Consequently, over C, quantified Infinity at t is equivalent to quantified Infinity at every relational type, and Infinity at e and t is equivalent to Infinity at every admitted type.

**Scope:** Closed admitted types and actual Frege finiteness. Full BF supplies Functionality; C5 additionally propagates necessary finiteness. The uniform quantified-Infinity equivalences need neither Functionality nor C5. These are schema statements, not an object-language quantifier over types, and do not assert external standardness of number fields.

**Significance:** The apparent hierarchy of quantified Infinity assumptions reduces to the two base types even over C. Finiteness requires additional Functionality for the converse propagation, and the stated models show why.

**Lean certified:** Finiteness propagation, descent, and the exact classification by type. The four C5 base-infinity combinations and the stated two-stage model/finiteness/Functionality endpoints.

**Notes:** Full constant-domain models realize all four base-finiteness patterns. Two-stage expanding-individual models show that bare C does not propagate finite base domains upward, and that all-type finiteness does not imply Functionality.

**Proof length:** medium (1,185 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [finite-types.md](../proofs/finite-types.md) · [finite-type-classification.md](../proofs/finite-type-classification.md)

**Scope evidence:** [certification-closeout.json](certification-closeout.json)

**Selected exact certificates:** [certificate.json](certificates/finite-type-classification/certificate.json) · [certificate.json](certificates/final-intensional-arithmetic-reflection/certificate.json) · [certificate.json](certificates/final-two-stage-arithmetic-model/certificate.json)

<a id="choice-coherence"></a>
## Finite cell ambiguity is the exact remaining coherence condition

**ID:** `CHOICE-COHERENCE`. Tracked keys: `synthesis.choice-coherence`.

For a fixed actual equivalence R, two specified Relational Choice instances yield a transversal exactly when a successor chooser on good histories has some nonempty internally finite ambiguity cell at each active history.

**Scope:** The choice instances are RC_(σt,σ) and RC_((σt)σt,σ). Symmetry preserving a selector graph forces a fixed point in every nonempty invariant set with a finite-orbit property code, with an internal finite-envelope analogue.

**Significance:** This sharpens both proof and countermodel routes for RC to TC. Arbitrary RC witnesses need not satisfy the coherence condition, and RC alone to TC remains unresolved.



**Proof length:** long (5,090 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [choice-coherence.md](../proofs/choice-coherence.md)

<a id="full-identity-observers"></a>
## Full identity observers have atomic and symmetry representations

**ID:** `FULL-IDENTITY-OBSERVERS`. Tracked keys: `synthesis.full-identity-observers`.

Over C, Atomicity (type t) and BF at each tested type give separation by operators preserving Boolean connectives and both quantifiers as composite operation identities. Over C + ☐ND (type t) + Actuality this separation is equivalent to Atomicity (type t).

**Scope:** For finite pinning in symmetric ideally-full models, arrow evaluation is representable exactly by the finite-stabilizer containment criterion when target symmetry groups are closed. Extreme amenability supplies Boolean observers; an ordered symmetry model has necessary Boolean separation and necessary Barcan but fails quantifier separation at e.

**Significance:** The composite operation laws have positive representation theorems in atomless models and countermodels separating Boolean preservation, quantifier preservation and necessary separation.

**Lean certified:** Simultaneous propositional separation for every finite list of closed quantifier types under C5 + Atomicity (type t), including its necessary schema; the converses and equivalence of the two schemas under C5 + Actuality.

**Notes:** Over C, ND (type t) + Actuality + propositional full-composite separation at quantifier type t entails Atomicity (type t). Over C + ☐ND (type t) + Actuality, Atomicity (type t), separation at t, and its necessity are equivalent.

**Proof length:** long (6,455 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [operator-representation.md](../proofs/operator-representation.md) · [ordered-observers.md](../proofs/ordered-observers.md) · [full-identity-observers.md](../proofs/full-identity-observers.md) · [local-observers.md](../proofs/local-observers.md) · [operator-boundaries.md](../proofs/operator-boundaries.md) · [observer-lattice.md](../proofs/observer-lattice.md)

**Earlier saved manifests:** [selected-manifest.json](certificates/full-observers-simultaneous-finite-schema/selected-manifest.json)

**Scope evidence:** [acceptance.json](certificates/full-observers-simultaneous-finite-schema/acceptance.json)

**Selected exact certificates:** [certificate.json](certificates/full-observers-propositional/certificate.json) · [certificate.json](certificates/full-observers-simultaneous-finite-schema/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.qualified_atoms`
- `Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.necessarily_qualified_atoms`
- `Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.c5_atomicity_entails_full_finite`
- `Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.c5_atomicity_entails_necessary_full_finite`
- `Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.full_finite_entails_atomicity`
- `Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.necessary_full_finite_entails_atomicity`
- `Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.full_finite_entails_necessary`
- `Classicism.Meta.Research.FullLogicalObserversFiniteSchemas.necessary_full_finite_entails_current`

<a id="pure-sp-bounded-image"></a>
## A pure SP embedding must omit a whole numerical cut

**ID:** `PURE-SP-BOUNDED-IMAGE`. Tracked keys: `synthesis.pure-sp-bounded-image`.

In the specified two-axiom pure SP test for a true independent Π₂ arithmetic sentence, any full pure-term embedding between the required Max endpoints sends every source number below every target counterexample.

**Scope:** The source number field includes all its nonstandard values. Its target image and downward closure cannot be admitted predicates there. Numerically cofinal embeddings are therefore impossible.

**Significance:** This rules out a broad class of candidate embeddings and explains why finite numerical approximations do not settle the consistency test. It proves neither consistency nor inconsistency of pure SP.



**Proof length:** medium (1,857 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [pure-sp-bounded-image.md](../proofs/pure-sp-bounded-image.md) · [pure-sp-omitted-cut.md](../proofs/pure-sp-omitted-cut.md)

<a id="signature-sp-survival"></a>
## One Henkin witness stage suffices for signature SP consistency

**ID:** `SIGNATURE-SP-SURVIVAL`. Tracked keys: `synthesis.signature-sp-survival`.

For exactly one unary predicate constant and no individual names, nonemptiness of the first witness-derivative stage K₁ implies consistency of full signature SP. K₁ is nonempty exactly when each existential theorem of the marked Max theory has a named instance consistent with that theory.

**Scope:** The Max reference remains the original finitary C(Σ). Ordinary Henkin completion can add unnamed entities. Full fixed-domain survival is stronger: its kernel is perfect, nonhyperarithmetic, and first stabilizes nonempty at ω₁CK.

**Significance:** This replaces a full transfinite survival problem by a sufficient first-stage test. The test is still unresolved. Numerical and Boolean witness fragments survive, but finite Herbrand extraction fails and the original singleton-profile root is deleted at stage one.



**Notes:** Neither K₁ emptiness nor failure of the fixed-domain construction would by itself refute signature SP. No successful survivor has been constructed.

**Proof length:** long (6,123 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [signature-sp-first-stage.md](../proofs/signature-sp-first-stage.md) · [signature-sp-derivative.md](../proofs/signature-sp-derivative.md) · [signature-sp-effective.md](../proofs/signature-sp-effective.md)

<a id="infinitary-resources"></a>
## Infinitary formation changes exhaustion and arithmetic

**ID:** `INFINITARY-RESOURCES`. Tracked keys: `synthesis.infinitary-resources`.

One admitted predicate saying “different from every name” gives countable named-exhaustion reflection. A separate profile construction proves Max-eligibility for an explicit semantic reference theory Td, so SP(Td) entails exactly countably many actual individuals and failure of necessary exhaustion.

**Scope:** The claim for an unspecified infinitary proof calculus remains conditional on its identity-separation/completeness bridge. SP(Td) consistency is not established. One countable numeral abstraction already standardizes Frege arithmetic and conflicts with Max referenced to original finitary C.

**Significance:** Infinitary assertion, term formation and inference have different effects. Fixed bounds on parameter formation or atomic joins do not give unbounded fullness.



**Notes:** Finite named exhaustion is already a schema of ordinary object-language sentences. The external index of an infinitary scheme is metalinguistic; each admitted instance is an object-language formula.

**Proof length:** long (4,650 words in the [selected exposition](proof-lengths.json)).

**Proofs:** [infinitary-resources.md](../proofs/infinitary-resources.md)

<a id="nominal-orbits"></a>
## World orbits determine propositional Dedekind infinity

**ID:** `NOMINAL-ORBITS`. Tracked keys: `model_interpretation.02`.

In the finite-support hierarchy for the full permutation group G of an atom set A, with finitely supported worlds W, an admitted injective nonsurjective operation on propositions exists iff the set of world orbits W/G is infinite. On atom worlds W=A, ☐Intensional Choice holds at every admitted type while this operational Dedekind infinity necessarily fails, including when A is infinite.

**Scope:** ZFC metatheory; arbitrary atom set, finite supports, trivial-action individuals ℕ, and a nonempty pointed world domain. The quotient W/G is taken in the metatheory. Operational Dedekind infinity means an admitted operation at tt that is injective and not surjective; it is distinct from the quantified Frege Axiom of Infinity.

**Significance:** The number of symmetry orbits, rather than the number of worlds, determines this form of propositional infinity. Necessary all-type Intensional Choice can coexist with its necessary failure.

**Lean certified.**

**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026; refinements of the existing nominal construction.

The key combinatorial step makes each fixed-support proposition stratum finite when there are finitely many world orbits; an injective operation omitting a value would produce infinitely many distinct iterates in one such stratum.

**Proof length:** medium (1,091 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §§1–4: finite-pattern orbit refinement, Dedekind equivalence and all-type Intensional Choice on atom worlds.

**Proofs:** [nominal-orbit-classification.md](../proofs/nominal-orbit-classification.md)

**Selected exact certificates:** [certificate.json](certificates/nominal-orbit-classification/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Nominal.dedekind_iff_infinite_orbit_quotient`
- `Classicism.Meta.Nominal.Hierarchy.dedInfT_iff_infinite_orbit_quotient`
- `Classicism.Meta.Nominal.Examples.finite_atoms_boxed_ic_and_not_dedInfT`

<a id="ch-coalesced"></a>
## CH can vary despite boxed structural principles

**ID:** `CH-COALESCED`. Tracked keys: `synthesis.coalesced-ch`.

Assuming Con(ZFC), a coalesced sum of two extensional Henkin models makes CH and its negation possible at the same type e. It satisfies ☐Atomicity, ☐BF, ☐Strong Leibniz, ☐Rigid Rigidity, ☐Weakly Rigid Weak Rigidity, ☐Tame Rigidity and Modal Well-Ordering together.

**Scope:** Classical set-theoretic metatheory with Choice and Con(ZFC). Atomicity, Strong Leibniz and the rigidity schemata range over every admitted relational type; BF and Well-Ordering include e. The component function domains are full relative to their respective first-order set-theoretic models. The accepted formal construction uses Lean’s ambient universe metatheory and the external Flypitch forcing/completeness development; its component endpoints have no explicit Con(ZFC) premise. The ordinary relative-consistency argument and the ambient formal construction have distinct metatheoretic scopes.

**Significance:** One joint countermodel settles a family of proposed implications to Non-contingency of CH. Strong atomic and rigidity principles, Barcan and Modal Well-Ordering do not suffice together.

**Lean certified:** Opposite-CH components at type e and their coalesced C countermodel with ☐BF, constructed in Lean’s ambient metatheory.

**Notes:** The model also has ☐Intensional Choice, ☐Distinctness-Preserving Collapse and ☐Boolean Completeness at t. It is a distinct CH specialization; the arithmetic-disagreement model’s arithmetic and Rigid Power failures are not inherited.

**Attribution:** Dorr’s two-component coalesced construction and its generic structural arguments; the CH choice of components and its verification were developed with OpenAI Codex at Daniel Kodsi’s request on 23 October 2026. Direct source misc.

The two leaves use their own set-theoretic real fields and disagree about CH. Free root components preserve the generic atomicity, Barcan, rigidity and well-ordering arguments.

**Proof length:** medium (2,614 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** coalesced-ch.md §§1–3; Opposite CH components: internal hierarchy, comprehension, real structure and CH truth correspondence; selected-ordinal alternative

**Proofs:** [coalesced-ch.md](../proofs/coalesced-ch.md) · [opposite-ch-components.md](../proofs/opposite-ch-components.md)

**Earlier saved manifests:** [selected-manifest.json](certificates/coalesced-ch-expanded/selected-manifest.json)

**Scope evidence:** [ch-intake.json](ch-intake.json) · [acceptance.json](certificates/coalesced-ch-conditional/acceptance.json) · [acceptance.json](certificates/coalesced-ch-expanded/acceptance.json)

**Selected exact certificates:** [certificate.json](certificates/coalesced-ch-conditional/certificate.json) · [certificate.json](certificates/coalesced-ch-expanded/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.CoalescedCH.consistent_witnesses_of_components`
- `Classicism.Meta.Research.CoalescedCH.coalesced_countermodel`
- `Classicism.Meta.Research.CoalescedCH.coalesced_box_barcan_countermodel`
- `ClassicismZFC.OppositeCHComponents.positive_component`
- `ClassicismZFC.OppositeCHComponents.negative_component`
- `ClassicismZFC.OppositeCHComponents.opposite_components`
- `ClassicismZFC.OppositeCHComponents.coalesced_countermodel`
- `ClassicismZFC.OppositeCHComponents.consistent_opposite_witnesses`
- `ClassicismZFC.OppositeCHComponents.maximalism_with_CH_noncontingency_inconsistent`
- `ClassicismZFC.OppositeCHComponents.maximalism_with_CH_noncontingency_schema_inconsistent`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.component_of_model`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.component_of_satisfiable`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.consistent_of_model`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.consistent_of_satisfiable`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.countermodel_of_models`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.countermodel_of_satisfiable`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_inconsistent_of_models`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_inconsistent_of_satisfiable`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_schema_inconsistent_of_satisfiable`
- `ClassicismZFC.SelectedFieldForcing.positive_real_witnesses`
- `ClassicismZFC.CodedFieldForcing.negative_cardinal_witnesses`
- `ClassicismZFC.InternalHierarchy.component_isModel`
- `ClassicismZFC.TypedReal.component_hasReal`
- `ClassicismZFC.TypedCHTransport.naturalCode_eq`
- `ClassicismZFC.TypedCHTransport.structuralCH_iff`
- `ClassicismZFC.TypedCHTransport.component_hasRealCH`
- `ClassicismZFC.TypedCHTransport.component_hasRealNotCH`

<a id="max-ch"></a>
## Maximalism is incompatible with Non-contingency of CH

**ID:** `MAX-CH`. Tracked keys: `synthesis.max-ch`.

Pure Maximalism together with Non-contingency of CH is inconsistent.

**Scope:** The separate C-consistency of the two closed pure real-structure assertions is justified under the metatheory of CH-COALESCED. Both assertions use type e; Bacon’s existing same-type witnesses at et provide another route. The accepted formal construction uses Lean’s ambient universe metatheory and the external Flypitch forcing/completeness development; its component endpoints have no explicit Con(ZFC) premise. The ordinary relative-consistency argument and the ambient formal construction have distinct metatheoretic scopes.

**Significance:** A short application of Maximalism’s possibility form gives a CH-specific conclusion beyond its recorded incompatibility with Necessity of Analysis.

**Lean certified:** Maximalism + Non-contingency of CH ⇒ ⊥, using constructed type-e components in Lean’s ambient metatheory.

**Notes:** Bacon’s known C5 countermodel and the current Relational Choice argument are retained in coalesced-ch.md §5 as source context, rather than presented as another new headline result.

**Attribution:** Original deduction developed with OpenAI Codex at Daniel Kodsi’s request on 23 October 2026, using the component consistency facts and the existing possibility form of pure Maximalism. Direct source misc.

**Proof length:** medium (1,927 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** coalesced-ch.md §§1 and 4; Opposite CH components: internal hierarchy, comprehension, real structure and CH truth correspondence; selected-ordinal alternative

**Proofs:** [coalesced-ch.md](../proofs/coalesced-ch.md) · [opposite-ch-components.md](../proofs/opposite-ch-components.md)

**Earlier saved manifests:** [selected-manifest.json](certificates/coalesced-ch-expanded/selected-manifest.json)

**Scope evidence:** [ch-intake.json](ch-intake.json) · [acceptance.json](certificates/coalesced-ch-conditional/acceptance.json) · [acceptance.json](certificates/coalesced-ch-expanded/acceptance.json)

**Selected exact certificates:** [certificate.json](certificates/coalesced-ch-conditional/certificate.json) · [certificate.json](certificates/coalesced-ch-expanded/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Research.CoalescedCH.maximalism_inconsistent_of_components`
- `Classicism.Meta.Research.CoalescedCH.maximalism_schema_inconsistent_of_components`
- `ClassicismZFC.OppositeCHComponents.maximalism_with_CH_noncontingency_inconsistent`
- `ClassicismZFC.OppositeCHComponents.maximalism_with_CH_noncontingency_schema_inconsistent`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_inconsistent_of_models`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_inconsistent_of_satisfiable`
- `Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_schema_inconsistent_of_satisfiable`

<a id="infinitary-comprehension"></a>
## Infinitary Comprehension and C5 characterize full standard models

**ID:** `INFINITARY-COMPREHENSION`. Tracked keys: `synthesis.infinitary-comprehension`.

In the specified classical infinitary language, Infinitary Comprehension together with C5 characterizes the full standard relational hierarchies among set-sized models. Atomicity follows and need not be assumed. For every infinite regular κ, allowing fewer than κ simultaneous parameters leaves a countermodel, even when formula size is unrestricted. Without C5, the surjection and idempotent full action models satisfy the specified infinitary comprehension schema while retaining their failures of ND or BF.

**Scope:** Arbitrary set-sized well-founded conjunctions and disjunctions, ordinary pointwise truth clauses, and arbitrary simultaneous typed parameter families. Types retain finite arity and relational outputs. The result is a semantic characterization in ZFC, with the original theoremhood restriction preserved in the finitary fragment. The certified forward direction explicitly assumes closure under actual infinitary term denotations at reachable worlds, unrestricted Comprehension for original closed-type matrices, and boxed propositional ND. It concerns universe-0 categorical premodels with coherent injective inclusions into intensions; fullness, constant domains, BF, object-language Choice and Infinity are not premises.

**Significance:** A familiar comprehension schema gives a direct route from an infinitary object language to full standard models. The support countermodel isolates the strength contributed by unbounded parameter families.

**Lean certified:** For universe-0 categorical premodels, term-denotation closure + unrestricted original-closed-type Infinitary Comprehension + ☐ND (type t) imply faithful full-standard representation; full standard models satisfy the corresponding infinitary axioms.

**Notes:** The infinitary base supplies Actuality and propositional Atomicity; Comprehension extends joins, meets and Atomicity to every relational type and gives Rigid Comprehension. With C5, full domains give ☐Functional Choice in ZFC. Neither Axiom of Infinity follows. This is not a completeness theorem for an effective proof calculus. The original finitary verdicts of these two full action models are due to Bacon and Dorr; their extension to infinitary syntax is the additional result here.

**Attribution:** Original mathematical development by OpenAI Codex at Daniel Kodsi’s request, 23 October 2026, source misc. The finite lambda-free reconstruction and canonical representation are cited dependencies.

**Proof length:** long (8,194 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** infinitary-comprehension.md §§1–4, 5 (source Theorem 5.3), and 6; infinitary-canonical-representation.md §5

**Proofs:** [infinitary-comprehension.md](../proofs/infinitary-comprehension.md) · [infinitary-canonical-representation.md](../proofs/infinitary-canonical-representation.md) · [lambda-free-reconstruction.md](../proofs/lambda-free-reconstruction.md)

**Earlier saved manifests:** [selected-manifest.json](certificates/infinitary-cardinal-closure/selected-manifest.json) · [selected-manifest.json](certificates/infinitary-support-and-finite-syntax/selected-manifest.json) · [selected-manifest.json](certificates/infinitary-action-countermodels/selected-manifest.json) · [selected-manifest.json](certificates/infinitary-full-representation/selected-manifest.json)

**Scope evidence:** [infinitary-comprehension-intake.json](infinitary-comprehension-intake.json) · [acceptance.json](certificates/infinitary-cardinal-closure/acceptance.json) · [acceptance.json](certificates/infinitary-support-and-finite-syntax/acceptance.json) · [acceptance.json](certificates/infinitary-action-countermodels/acceptance.json) · [acceptance.json](certificates/infinitary-full-representation/acceptance.json)

**Selected exact certificates:** [certificate.json](certificates/infinitary-cardinal-closure/certificate.json) · [certificate.json](certificates/infinitary-support-and-finite-syntax/certificate.json) · [certificate.json](certificates/infinitary-action-countermodels/certificate.json) · [certificate.json](certificates/infinitary-full-representation/certificate.json)

**Principal declarations:**

- `Classicism.Research.InfinitaryComprehension.CardinalClosure.short_family_bounded`
- `Classicism.Research.InfinitaryComprehension.CardinalClosure.exists_closed_elementarySubstructure`
- `Classicism.Research.InfinitaryComprehension.CardinalClosure.exists_short_sequence_closed_elementarySubstructure`
- `Classicism.Research.InfinitaryComprehension.FiniteBridge.embed_rename`
- `Classicism.Research.InfinitaryComprehension.FiniteBridge.embed_subst`
- `Classicism.Research.InfinitaryComprehension.FiniteBridge.embed_inst`
- `Classicism.Research.InfinitaryComprehension.FiniteBridge.eval_embed`
- `Classicism.Research.InfinitaryComprehension.FiniteBridge.finite_comprehension`
- `Classicism.Research.InfinitaryComprehension.FiniteBridge.sequent_at_iff`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.assignment_supported`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.bounded_comprehension`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.colour_not_supported`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.colour_comprehension_false`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.fixed_bound_strictness`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.comprehension_of_occurrence_bound`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.finite_occurrence_comprehension`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.finite_branching_comprehension`
- `Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.occurrence_fixed_bound_strictness`
- `Classicism.Research.InfinitaryComprehension.Strictness.Expansion.model`
- `Classicism.Research.InfinitaryComprehension.Strictness.Expansion.faithful`
- `Classicism.Research.InfinitaryComprehension.Strictness.Expansion.relation_atomicity`
- `Classicism.Research.InfinitaryComprehension.Strictness.Expansion.profile_atomic`
- `Classicism.Research.InfinitaryComprehension.Strictness.Expansion.c_theorem_holds`
- `Classicism.Research.InfinitaryComprehension.Strictness.Expansion.not_comp`
- `Classicism.Research.InfinitaryComprehension.Strictness.reduct_certificate`
- `Classicism.Research.InfinitaryComprehension.Strictness.exists_strictness_certificate`
- `Classicism.Research.InfinitaryComprehension.Strictness.exists_atomic_modal_collapse_not_comp`
- `Classicism.Research.InfinitaryComprehension.Nominal.eval_parameter_congr`
- `Classicism.Research.InfinitaryComprehension.Nominal.Hierarchy.comprehension_of_supported_evaluation`
- `Classicism.Research.InfinitaryComprehension.Countermodels.surjection_comprehension_barcan_not_nd`
- `Classicism.Research.InfinitaryComprehension.Countermodels.idempotent_comprehension_not_barcan`
- `Classicism.Research.InfinitaryComprehension.Countermodels.idempotent_comprehension_not_nd`
- `Classicism.Research.InfinitaryComprehensionObservers.equality_separation_c5.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.atomicity_equality_separation_iff_c5.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.atomicity_logical_separation_nd_iff_c5.derivable`
- `Classicism.Research.InfinitaryComprehension.Canonical.originalModel_domain`
- `Classicism.Research.InfinitaryComprehension.Canonical.originalModel_truth`
- `Classicism.Research.InfinitaryComprehension.Canonical.original_full_standard_representation`
- `Classicism.Research.InfinitaryComprehension.Canonical.originalModel_full_functions`
- `Classicism.Research.InfinitaryComprehension.Canonical.originalModel_full_propositions`
- `Classicism.Research.InfinitaryComprehension.Term.full_comprehension`
- `Classicism.Research.InfinitaryComprehension.full_coext_intensionality`
- `Classicism.Research.InfinitaryComprehension.Canonical.closed_proposition_atomicity`
- `Classicism.Research.InfinitaryComprehension.Canonical.closed_proposition_actuality`
- `Classicism.Research.InfinitaryComprehension.Canonical.action_holds_atomicity`
- `Classicism.Research.InfinitaryComprehension.Canonical.action_holds_rigid_comprehension`
- `Classicism.Research.InfinitaryComprehensionObservers.logical_separation_barcan.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.equality_separation_logical.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.equality_separation_barcan.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.equality_separation_nd.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.logical_separation_nd_c5.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.logical_separation_nd_necessary_nd.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.equality_separation_necessary_nd.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.c5_atomicity_equality_separation.derivable`
- `Classicism.Research.InfinitaryComprehensionObservers.c5_atomicity_logical_separation.derivable`
- `Classicism.Research.InfinitaryComprehension.Term.eval_C5`

<a id="computability-comparison"></a>
## Theoremhood and model construction have successive jump thresholds

**ID:** `COMPUTABILITY-COMPARISON`. Tracked keys: `principles.14`, `principles.15`, `principles.16`, `principles.17`, `principles.18`, `principles.25`.

The positive theories, Max and SP occupy three successive levels of computational strength.

| Pure theory | Theoremhood | Oracles computing some adequate countable model |
|---|---|---|
| C + ☐Plenitude + Axiom of Infinity (types e and t) | $\Sigma^0_1$-complete | PA degrees |
| C + ☐Functional Choice + Axiom of Infinity (types e and t) | $\Sigma^0_1$-complete | PA degrees |
| Max | $\Sigma^0_2$-complete | PA degrees over $0'$ |
| SP, **if consistent** | $\Sigma^0_3$-complete | PA degrees over $0''$ |

Adequate codes provide term interpretation and actual truth. PA degree over an oracle means the ability to compute a binary diagonally nonrecursive function relative to it; ordinary PA degrees use no oracle. The positive bounds already hold with the weaker Infinity schema at one admitted type. The theoremhood classifications persist under consistent extensions enumerable in the corresponding oracle.

**Scope:** The original pure finitary relational language and fixed reference C are used throughout. Completeness is under ordinary computable many-one reductions. Model capacity means computing some countable BBK model with sorted domains, equality, uniform finite-term interpretation and actual truth. No bound for a bare action/category presentation is inferred. All SP existence and complexity conclusions require Con(SP).

**Significance:** Arithmetic conservation does not erase the computational gaps between the positive packages, Max and SP. Theoremhood and selecting a complete model are different computational problems.



**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 22 October 2026. Imported mathematical results retain the attribution and locators given in the proofs.

**Proof length:** long (13,702 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Positive effective model theory §§1–8, 13–16; Max degree §§1–5, 8–10; Strong Possibility degree §§1–6

**Proofs:** [positive-effective.md](../source/research/2026-10-22/notes/positive-effective.md) · [max-degree.md](../source/research/2026-10-22/notes/max-degree.md) · [strong-possibility-degree.md](../source/research/2026-10-22/notes/strong-possibility-degree.md)

<a id="exact-model-degrees"></a>
## A complete theory has a model of exactly its computational degree

**ID:** `EXACT-MODEL-DEGREES`. Tracked keys: `model_interpretation.05`.

From any supplied complete consistent pure theory Γ extending C, one can uniformly construct a countable BBK model whose complete pure theory is exactly Γ and whose adequate code has exactly Γ’s Turing degree. Consequently the positive and Max bounds above describe the exact degrees realized by models, not merely the oracles from which some model can be computed.

**Scope:** The positive exact-degree theorem applies to any fixed consistent c.e. extension of C plus the Infinity schema at an admitted type; the Max theorem to any fixed consistent 0′-c.e. theory entailing pure Max. Degrees range across all models of the theory, not copies of one fixed structure. Codes contain canonical operational data and actual truth, without unrelated padding. No standardness or full-domain conclusion is asserted.

**Significance:** The passage from a supplied complete theory to a model introduces no extra computational strength. The converse coding recovers information from original pure truth values.



**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 22 October 2026. Imported mathematical results retain the attribution and locators given in the proofs.

**Proof length:** long (5,509 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Exact completion/model spectra §§1–6; Positive effective model theory §16; Max degree §§8–9

**Proofs:** [exact-completion-model-spectra-20261022.md](../source/research/2026-10-22/notes/exact-completion-model-spectra-20261022.md) · [positive-effective.md](../source/research/2026-10-22/notes/positive-effective.md) · [max-degree.md](../source/research/2026-10-22/notes/max-degree.md)

<a id="standard-number-models"></a>
## Standard natural numbers impose a much stronger computational barrier

**ID:** `STANDARD-NUMBER-MODELS`. Tracked keys: `principles.19`, `principles.20`.

Every adequate code of a C-model satisfying numerical noncollapse at σ and having externally standard Frege numbers at σ computes every hyperarithmetical real, and is itself nonhyperarithmetical. For any theory enumerable in a hyperarithmetical oracle with those arithmetic premises, if a standard model exists, some standard codes lie strictly below Kleene’s O; exactly the hyperarithmetical reals are computable from every standard code, and there is no least solution degree. For the specified positive and Max standard-number model classes, finite-condition satisfiability is Σ¹₁-complete and validity is Π¹₁-complete.

**Scope:** Numerical noncollapse is Iσ = ◇I*σ in the cited notes. Standardness means that the actual number domain consists exactly of the distinct standard numeral denotations; it is a semantic restriction, not a finitary axiom. Standard models are supplied for the positive packages with the specified Infinity assumptions and for Max. An SP application requires existence of a standard SP model, not merely Con(SP). The analytic-completeness result uses the separate branch-graph constructions for the positive and Max classes; it is not asserted for every hyperarithmetically enumerable theory.

**Significance:** Low unrestricted models and standard-number models have sharply different complexity. No fixed hyperarithmetical oracle can uniformly turn arbitrary adequate models into standard ones.



**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 22 October 2026. Imported mathematical results retain the attribution and locators given in the proofs.

**Proof length:** long (6,474 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Positive effective model theory §§18–21.5; Max degree §§10.1–10.2, 13

**Proofs:** [positive-effective.md](../source/research/2026-10-22/notes/positive-effective.md) · [max-degree.md](../source/research/2026-10-22/notes/max-degree.md)

<a id="completion-spaces"></a>
## Finite descriptions distinguish the completion spaces

**ID:** `COMPLETION-SPACES`. Tracked keys: `principles.21`, `principles.22`.

In the space of complete consistent pure C-theories, Max forms a nonempty closed nowhere-dense set: every consistent finite description admits a refinement violating Max. C + ☐Plenitude forms a clopen set. For either C + ☐Plenitude or C + ☐Functional Choice, isolated completions are exactly the full Gallin theories with finite individual and world domains; removing those points leaves a perfect space with dense low completions. More generally, any consistent computably enumerable pure-complete extension of C fixes finite actual domains at every type, with recursively computable exact sizes and necessary finite bounds.

**Scope:** Basic open sets specify finitely many pure sentences. The completion-space claims use general Henkin/BBK semantics, not full-semantics compactness. The positive isolated-point classification is stated without imposing Infinity; the positive infinite part and Max are each abstractly homeomorphic to Cantor space despite their different positions in the ambient space. Necessary finite bounds need not equal the exact actual sizes and do not by themselves yield C5.

**Significance:** The comparison explains what finite descriptions can fix, and why the Max obstruction is stronger than the familiar failure of effective axiomatization.



**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 22 October 2026. Imported mathematical results retain the attribution and locators given in the proofs.

**Proof length:** long (7,030 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Theory-space comparison §§1–4, 8; Gallin comparison §§14.1–14.3; Effective refinements §§9.3–9.4; Positive effective model theory §16; Max degree §§8–9

**Proofs:** [theory-space-comparison.md](../source/research/2026-10-22/notes/theory-space-comparison.md) · [gallin-comparison.md](../source/research/2026-10-22/notes/gallin-comparison.md) · [effective-refinements.md](../source/research/2026-10-22/notes/effective-refinements.md) · [positive-effective.md](../source/research/2026-10-22/notes/positive-effective.md) · [max-degree.md](../source/research/2026-10-22/notes/max-degree.md)

<a id="uniform-complete-evaluators"></a>
## Uniform evaluator selection measures well-orderability and Choice

**ID:** `UNIFORM-COMPLETE-EVALUATORS`. Tracked keys: `world_algebra.17`.

Over C + ☐Plenitude, one admitted operator choosing, for each nonzero proposition p, a complete bivalent evaluator sending p to ⊤ exists exactly when the world atoms admit a represented well-order. Requiring such selectors at every relational type is equivalent to ☐Functional Choice. The propositional requirement and all-type Intensional Choice are independent over C + ☐Plenitude.

**Scope:** A complete evaluator is a unital Boolean homomorphism into {⊥, ⊤} preserving every admitted rigid meet. It need not evaluate actual truth: it selects an atom below its input. Completeness and well-ordering quantify over represented families, without external powerset fullness. The independence claims have the two explicit finite-support models in §42.1.

**Significance:** This isolates the extra strength of assembling separate evaluators into one operator, and connects evaluation directly to the distinction between Intensional and Functional Choice.



**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 22 October 2026. Imported mathematical results retain the attribution and locators given in the proofs.

**Proof length:** long (4,683 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Structural algebraic core §§0–2, 9, 42–42.2; Structural world representation §§0–2

**Proofs:** [structural-algebraic-core.md](../source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-world-representation.md](../source/research/2026-10-22/notes/structural-world-representation.md)

<a id="c5-strong-retractions"></a>
## C5 is exactly strong retractions of actual injections

**ID:** `C5-STRONG-RETRACTIONS`. Tracked keys: `choice.04`.

Over C, C5 is equivalent to the schema that every actually injective operation between relational types has a left inverse whose inverse equation holds necessarily. The t→tt and tt→tt instances suffice for the converse.

**Scope:** Both domain and codomain are relational, so the inverse operation is admitted. A strong retraction requires ☐∀x g(fx)=x; ordinary pointwise retractions have a different strength. Actuality, Plenitude and Choice are not assumptions.

**Significance:** The placement of necessity in an inverse law separates C5 from the Actuality-plus-retraction characterization of Plenitude.

**Lean certified:** The C5 forward rules for persistent injectivity and strong retractions at all admitted relational types, the low-type converses to ☐ND (type t), and the per-map necessary-injectivity/strong-retraction equivalence.

**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 22 October 2026. Imported mathematical results retain the attribution and locators given in the proofs.

**Proof length:** medium (1,080 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Choice uniformization §2, Theorem 3; §§7, 9, Theorems 11–13

**Proofs:** [choice-uniformization.md](../source/research/2026-10-22/notes/choice-uniformization.md)

**Earlier Lean sources:** [SectionsRetractionsStrong.lean](../source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsStrong.lean) · [SectionsRetractionsStrongCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsStrongCertificates.lean) · [SectionsRetractionsMasks.lean](../source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsMasks.lean) · [SectionsRetractionsMasksCertificates.lean](../source/topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsMasksCertificates.lean)

**Earlier saved manifests:** [20261023T053945495916Z-2d579847.json](../source/research/2026-10-22/lean-formalization/checks/20261023T053945495916Z-2d579847.json)

**Scope evidence:** [integration-scope-reconciliation.json](integration-scope-reconciliation.json)

**Principal declarations:**

- `Classicism.Research.Splitting.c5_injectivity_persists.rule`
- `Classicism.Research.Splitting.c5_strong_retractions.listRule`
- `Classicism.Research.Splitting.c5_strong_retractions_t.derivable`
- `Classicism.Research.Splitting.low_strong_retractions_c5.rule`
- `Classicism.Research.Splitting.low_persistent_injections_c5.rule`
- `Classicism.Research.Splitting.necessary_injection_splitting.listRule`
- `Classicism.Research.Splitting.necessary_injection_iff_retraction.derivable`
- `Classicism.Research.Splitting.necessary_injection_iff_retraction_t.derivable`

<a id="forcing-possibilism"></a>
## Strict-smallness Forcing Possibilism is independent of necessary Choice and Infinity

**ID:** `FORCING-POSSIBILISM`. Tracked keys: `synthesis.forcing-possibilism`.

With the database’s strict-smallness definition, Forcing Possibilism is independent over C + ☐Functional Choice + Axiom of Infinity (types e and t). For any infinite world set W in external ZFC, full S5 satisfies FP exactly when 2^{|W|} equals the continuum. A free-root model satisfies FP and both quantified Infinity axioms while failing Intensional Choice.

**Scope:** The size comparison, complete Boolean algebra condition and isomorphism are unboxed, with every admitted carrier type, including e. Dedekind-finite is a separate qualifying disjunct. The S5 classification uses full relation domains and external ZFC; it is not equivalent to W being countable. The free-root separation asserts FP at the root, not ☐FP. The choice-free socks argument and unresolved no-countable-choice-for-reals cases are in the proof.

**Significance:** Even necessary Functional Choice and both quantified Infinity axioms leave strict FP undecided. FP itself does not supply Intensional Choice; its strength depends critically on the strict size bound.



**Notes:** The existing encoded CH incompatibility is refuted under this strict definition; this is not a new refutation of the source appendix’s non-strict principle. Eleven question rows and eighteen compatibility rows are not independent-result counts.

**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026. Recorded full-action arguments and the earlier lottery audit retain their existing attribution.

**Proof length:** medium (1,673 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §§1–4, 6–7

**Proofs:** [forcing-possibilism.md](../proofs/forcing-possibilism.md)

<a id="infinity-schema-separation"></a>
## Infinity schemata do not imply their quantified axioms, even with necessary Choice

**ID:** `INFINITY-SCHEMA-SEPARATION`. Tracked keys: `synthesis.infinity-schema-separation`.

C + ☐Functional Choice has a Henkin model satisfying both finite lower-bound Infinity schemata while necessarily refuting both corresponding quantified Axioms of Infinity. A second model satisfies ☐Functional Choice, ☐FP, ☐Axiom of Infinity (type t) and the individual Infinity schema while necessarily refuting Axiom of Infinity (type e).

**Scope:** The finite lower-bound schemata and the impredicative quantified Frege axioms are distinct. The constructions use many-sorted Henkin compactness in external ZFC; their limits are not externally full hierarchies. FP has the exact strict-smallness definition.

**Significance:** Having arbitrarily many externally distinct objects does not prevent a nonstandard internal finite cardinality from counting the whole domain. The mixed model preserves genuinely quantified propositional Infinity.



**Notes:** The finite-world construction alone does not establish the mixed separation, because it refutes quantified propositional Infinity.

**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026; source misc.

**Proof length:** short (651 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §§2, 5, 7

**Proofs:** [forcing-possibilism.md](../proofs/forcing-possibilism.md)

<a id="fixed-point-entrance"></a>
## Comprehension, completeness and choice do not force ☐Tame Rigidity

**ID:** `FIXED-POINT-ENTRANCE`. Tracked keys: `rigidity.32`.

A fixed-point entrance C-model with singleton individuals satisfies Atomicity, Boolean Completeness, Rigid Comprehension, Relational Choice, Tame Rigidity, Rigid Power and Weakly Rigid Power at every relational type, together with ☐Strong Actuality and BF (type e). It refutes ☐Tame Rigidity at type (tt)t, BF at every relational argument type, ND (type t), and Strong Leibniz Biconditionals at every relational type.

**Scope:** The listed unprefixed principles hold at the entrance root. Tame Rigidity holds there and fails at the accessible tail; the modal verdict is ¬☐Tame Rigidity, not ☐¬Tame Rigidity. The construction uses ordinary classical set-theoretic metatheory.

**Significance:** Even with Atomicity, Boolean Completeness, Rigid Comprehension, Relational Choice and Weakly Rigid Power, Tame Rigidity need not be necessary. BF at individuals can hold while every relational BF instance fails.

**Lean certified.**

**Notes:** The general entrance lemma in §7 is not included in this certificate scope.

Attach a fixed-point entrance to a qualitative tail. Exact-image relations supply comprehension and the rigid powers; the root relation algebras are complete and atomic. The substantial model argument constructs admitted qualitative codes, proves their injectivity and verifies finite pinning, yielding a weakly rigid relation whose transport is not weakly inextensible.

**Proof length:** medium (1,771 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** §§1–6

**Proofs:** [fixed-point-entrance-cone.md](../source/research/2026-10-22/notes/fixed-point-entrance-cone.md)

**Earlier saved manifests:** [original-manifest.json](certificates/fixed-point-entrance-complete/original-manifest.json)

**Scope evidence:** [acceptance.json](certificates/fixed-point-entrance-complete/acceptance.json)

**Selected exact certificates:** [certificate.json](certificates/fixed-point-entrance-complete/certificate.json)

**Principal declarations:**

- `Classicism.Meta.Intensional.FixedPointEntrance.syms_inv`
- `Classicism.Meta.Intensional.FixedPointEntrance.transport_fixed`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.isModel`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.collapse_not_sym`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Rigidity.holds_tame_schema`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Completeness.holds_bc_schema`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Comprehension.holds_rigid_comprehension_schema`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Distinctness.not_nd_t`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Distinctness.bf_e_at`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.root_profile`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Atomicity.holds_atomicity_schema`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.RelationalChoice.holds_relational_choice_schema`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Powers.holds_weak_power_schema`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Powers.holds_rigid_power_schema`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Barcan.externalEquality_mem`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Barcan.witness_changed`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Barcan.not_barcan_t`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.root_package`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.RelationalBarcan.not_barcan_relational`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Actuality.necessary_strongActuality`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Codes.code_rigid`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Codes.CodeInjectivity.code_injective_nonpoint`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.TameWitness.weak`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.TameWitness.not_rigid`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.TameWitness.not_tail_tame`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.holds_background`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.background_consistent`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.root_not_box_tame`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.not_entails_box_tame`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.complete_countermodel`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Leibniz.not_strongLeibniz`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Leibniz.not_strongLeibniz_t`
- `Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.full_countermodel`

<a id="h-observer-space"></a>
## Observer separation over H: primitive packages, representation and higher types

**ID:** `H-OBSERVER-SPACE`. Tracked keys: `synthesis.h-observer-space`.

For any finite set Γ of independent primitive preservation clauses M, V, N, Qσ, Pσ, put T_J = H + S[A ∧ Z ∧ J]. At a fixed preservation tier and fixed propositional or full relational scope, T_K entails T_J exactly when J ⊆ K. Uniform corruption models prove every omitted-clause non-implication. For every observer qualification K, full relational separation is equivalent over H to propositional separation plus Functionality. Conjoining separately separating classes can be strictly weaker than requiring one class to satisfy both qualifications. The accompanying representation theorems characterize the connective, quantifier and equality branches with their explicit premises. Reversible accepting/rejecting meet separation plus one atom makes atoms separate order, represents every proposition as the join of its atoms, and gives a unique true atom. Under internal Frege finiteness of all propositions, material and pointwise meet separation are equivalent, and likewise for join separation, retaining each acceptance/rejection orientation. Full relational separation collapses all three tiers. A least true meet element or greatest false join element suffices for the corresponding normalization without finiteness. Reversible meet separation plus one atom is exactly bounded atomistic meet structure, a true atom and transitivity of admitted full-meet automorphisms on atoms; arbitrary extra restrictions use the exact MoveTrue condition without closure assumptions. A six-element model shows that atomisticity and a true atom alone do not suffice. For each finite preservation signature, pointwise separation is equivalent to the existence of an admitted composition-closed separating family of material observers, equivalently such a composition-closed family containing identity. Finite-image material meet separation is equivalent to at-most-two-output pointwise meet separation, and likewise for join, without finiteness of the proposition domain. Full typed OS need not imply ☐BF or ☐Functionality. Endpoint logical separation is equivalent to C5 + ☐OS + one atom, and already to C5 plus the boxed propositional Good_{ {t} } separation instance plus one atom. Reversible logical separation implies C5 + ☐OS + No Pure Contingency, with no atom or Actuality premise. The proof extends qualified involutions by typewise conjugation and applies separation to each closed pure sentence. Reversible logical separation is strictly stronger than C5 + ☐OS, even among atomless models: the even-block/power-of-two-block symmetry model has necessary OS but a contingent closed pure six-element selection sentence. Over H + ND (type t), material and pointwise meet/universal separation have the same exact meet/GLB representation, with a dual join/existential result. Finite-image normalization extends to matching quantifiers and joint M,V,Q,P packages. Over C, an admitted whole inverse is equivalent to necessary bijectivity; invertible Q_t observers are automatically Boolean. Local stabilizer conjugacy supplies reversible observers in the stated symmetry-model families. Internal Frege finiteness also gives exact affine representation by two-output pointwise homomorphisms, separately for XOR and biconditional. Finite-image material affine separation has the same normalization without finiteness of the domain. Plenitude at (t,t), stated explicitly over H, normalizes all seven nonempty primitive connective signatures, each affine operation, and the verified matching lattice/quantifier packages, including infinite-image observers. Full qualified right-inverse separation is exactly Rev. Qualified left-inverse separation is strictly weaker even with C5 and its own boxed schema; it implies OS, but not C5, ☐OS, its own boxed schema, ☐BF or ☐Functionality. The ternary Cantor model satisfies the separate endpoint-fixing M/Q/P, V/Q/P and N/Q/P separation schemas and their boxes, together with C and boxed BF and Functionality, while even propositional Boolean separation fails. Both arrows Rev ⇒ SplitMono ⇒ OS are strict. The full fork satisfies ☐OS and all boxed BF and Functionality but fails SplitMono, so SplitMono and ☐OS are incomparable. Under internal Fin_t(All), full SplitMono, Rev and endpoint separation coincide. Over H plus the preorder Zorn instance at tt, every admitted partial Boolean-group truth character extends, and material affine separation is exactly the relevant group equations with the stated endpoint alignments. Under Plenitude at (t,t), material negation separation and each separate material affine separation are equivalent to pointwise involutive separation, fixing the endpoints mentioned by the qualification; whole identities retain local Functionality or full typed scope. The component-shift symmetry model satisfies C5 + ☐SplitMono + No Pure Contingency but not Rev. Rev further implies noncontingency for pure formulas with finitely many individual parameters and endpoint-valued first-order relation parameters. Zorn at tt also supplies admitted prime filters and extension of admitted partial lattice truth characters over H; material joint lattice and Boolean separation have exact algebraic converses under this explicit premise, with the stated endpoint alignments and derived operations. Over bare H, joint negation/affine material separation is exactly affine separation plus the translation identity ¬x=x+c, c=¬0. Joint XOR/biconditional separation is exactly XOR separation plus the corresponding translated-operation identity. Under the actual expansion X=¬D, all three two-operation material packages agree with the three-operation package; Plenitude supplies pointwise involutions for the linked signatures. Over C + BF, at each finite list Δ containing t and relational output type τ, SplitMonoSep(τ,Δ) is equivalent to RevSep(τ,Δ) or [OS(τ,Δ) and KΔ], where KΔ asserts one admitted qualified pair F∘E=I and a true c with Fc=Bottom. The full-H form is full OS plus the external schema RevSep(t,Δ) or KΔ. The condition D_t that every admitted injective E:tt is onto makes full SplitMono and Rev equivalent. It is strictly weaker than internal Frege finiteness: a two-colour finite-pinning model satisfies C5 + Rev + D_t with atomless propositions, while endpoint separation and internal Frege finiteness fail. Over H, endpoint separation is equivalent to OS + Plenitude at (t,t), OS + full Plenitude, C5 + OS + Actuality, C5 + OS + Boolean Completeness, and C5 + Atomicity (type t). Already C + BF (type t) + Plenitude at (t,t) is equivalent to C5 + Actuality. Over C5, each currently surjective Good observer at a finite list containing t has a definable admitted same-list qualified right inverse; hence Rev is equivalent over H to C5 + full surjective logical separation. Both chains Rev ⇒ SurjSep ⇒ OS and Rev ⇒ SplitMono ⇒ OS are strict. SurjSep and SplitMono are incomparable even over C + ☐BF + ☐OS, witnessed by the full omega-chain and the C5 finite-block model. Within C5, SurjSep is Rev and does imply SplitMono. The linear/circular fibre model satisfies C5 + ☐OS + D_t with atomless propositions but fails SplitMono at the explicit propositional list {t,e,et,eet,(et)t,((et)t)t}; a contingent closed pure sentence about infinite amorphous cells proves the obstruction. For an admitted group G of whole meet automorphisms over H, its common truth-profile relation is the largest admitted invariant truth-compatible equivalence and is a meet congruence; separation is exactly the absence of a nontrivial such congruence. On chains the obstruction is convex. An admitted order-primitive action on the interior of a bounded dense chain, together with an interior true/false pair, gives reversible meet separation. The rational-chain full-function model has joint reversible meet/join separation and all Functionality while C fails, with no atoms or truth extrema. Order primitivity is strictly weaker than order 2-homogeneity for admitted actions. A specified countably infinite sequence fixed by a source symmetry group in the all-bijections finite-pinning framework gives one qualified left-inverse pair with a true kernel element, normalizing ordinary separators at that source. At the trivial-symmetry object of the qualitative-contrast model, C5 + SplitMono holds but ☐OS and ☐SplitMono fail. Thus SplitMono and ☐OS are incomparable even over C5. Every full cancellative-monoid action model with singleton individuals satisfies separately boxed full SurjSep. A specified infinite sequence of distinct units also gives separately boxed full SplitMono, with one common qualified left inverse. A nonunit refutes C5. The concrete monoid ℤ×ℕ therefore refutes ☐SurjSep + ☐SplitMono ⇒ Rev, even over C + ☐BF. SurjSep + SplitMono lies strictly below Rev and strictly above each factor; its two witness families may be different. Over H, a bounded meet chain with a greatest false and a least true proposition and a specified admitted whole-meet automorphism group G has S[G] exactly when every nontrivial interval contains an adjacent pair and G is transitive on adjacent pairs. Plenitude at (t,t) plus Q_t/P_t supplying the admitted order bounds gives that truth cut, without C or Functionality. The full-function complete split interval is atomless and satisfies full reversible endpoint-fixing M,V,Q_Δ,P_Γ separation for every finite list while C fails; its observers need not preserve negation. For a specified admitted invariant convex block relation on the interior of a bounded dense chain, with each block without endpoints, global separation is exactly one crossed block, transitivity on blocks and separation by its admitted stabilizer. For a specified external finite central partition of a bounded distributive lattice preserved by G, global separation is exactly transitivity on factor units and stabilizer separation inside the unique true factor. Lexicographic rational-chain and finite-product atomless models give joint reversible M/V separation with all Functionality below C. Over C + BF (type t), Onto(E) implies ☐Onto(E), with E a free parameter; Good qualification is persistent over C. Full SurjSep nevertheless gives neither ☐OS nor ☐SurjSep, even with ☐BF and ☐Functionality. A root truth-profile extension of a fixed/free symmetry tail supplies this countermodel, with failure already at the future propositional Boolean instance. Thus Rev ⇒ ☐SurjSep ⇒ SurjSep and ☐SurjSep ⇒ ☐OS are strict. SurjSep does not imply ☐BF, with failure at every admitted type in the integer-shift predecessor model. Over C5, every admitted Good-{t} observer E has admitted order adjoints L ⊣ E ⊣ R, with Rq=∃p[(Ep≤q)∧p] and Lq=¬R(¬q). With k=RBottom and a=¬k, R(Ep)=p∨k and L(Ep)=p∧a, giving a Boolean order isomorphism from [Bottom,a] onto the admitted image. Injectivity is equivalent to RBottom=Bottom or LTop=Top; onto is equivalent to join preservation by R or meet preservation by L; bijectivity is equivalent to R=L or negation preservation by either adjoint. The admitted image floor ER and ceiling EL are idempotent, with ER≤I≤EL and mutual absorption. ER is an auxiliary S5 interior and equals native Box exactly when E is endpoint-valued. The endpoint-fixing envelopes T−q=(a∧Rq)∨(k∧q) and T+q=Lq∨(k∧q) preserve M/all Q and V/all P respectively, and coincide exactly when E is onto. Already for a Boolean E over C5, commuting with native Box or Diamond is exactly injectivity, without Q_t. The integer-shift predecessor model satisfies C + full typed SurjSep + BF while ☐BF_σ fails at every admitted type σ. In the finite-pinning tail over ℕ×ℤ and {∗}×ℤ, split epimorphisms approximate finite pins and invertible integer translations supply prescribed-coordinate kernel pairs. The root truth-profile extension combines all-type evaluation readers with those onto tails. A future object has nononto transport at every type and refutes every BF instance. Hence SurjSep ⇒ ☐BF is refuted with exact all-type scope.

**Scope:** H is the base of this development; C is recovered only in the complete logical region. The primitive-package theorem concerns independent logical primitives, not operations defined from one another. It classifies the displayed finite family, not all H theories or cross-tier comparisons. Full composite identities are the default; material and pointwise tiers are explicitly identified in comparison results. Type lists are external and finite. Quantifier-generated binary operations require an admitted exact binary-family constructor. Strong representation converses require the stated identity-bivalence and Functionality premises. Internal Frege finiteness is not external finite cardinality. The single Plenitude instance at (t,t) is an explicit H premise, not the C background imported from its database record. Finite-image affine normalization does not require the image to be a subgroup. A qualified left or right inverse is admitted, qualified at the same finite list, and satisfies the indicated whole-operation equation. The component-shift model restricts arrows to common integer shifts of components; it is not covered by the one-object all-bijections sufficient theorem. The parameter schema is universally closed over finite lists of individual and first-order relation parameters, under the condition that every relation value is an endpoint. It introduces no quantification over formulas. Plenitude involutions preserve separation of the chosen pair, not an earlier observer’s entire truth profile or extra operations. The decomposition is a fixed-instance disjunction over C + BF; its full-H version is an external schema of disjunctions, not one global disjunction between full theories. D_t quantifies over admitted tt operations, not arbitrary external functions or injective relations. Zorn’s lattice and Boolean converses preserve the distinction between original and derived operations and infer no quantifier preservation. Linked affine normalization requires the exact compatibility identities and endpoint alignments. Plenitude and OS in the endpoint bridge are current premises. Surjectivity is the internal formula ∀q∃p(Sp=q), distinct from an admitted right inverse. The definable-section theorem requires C5 and t in the qualification list; the SurjSep/SplitMono incomparability is not C5-relative. The order-action theorem quantifies over admitted relations and a group with explicit whole preservation and inverse identities; it is a sufficient atomless region, not an exhaustive characterization. Higher-type separation additionally requires Functionality. The fixed-point and unit sequences are specified external model data, not object-language enumerations or implicit Choice premises. The monoid need not be commutative. Adjacent gaps are not proposition atoms. The chain characterization retains the truth-cut and admitted-group hypotheses. Order preservation of admitted bounds is pointwise; whole identities require the stated Functionality, which the concrete full-function model supplies. The block and factor reductions retain specified admitted stabilizers and whole inverse identities. A finite number of factors is external and is not internal finiteness of propositions. The individual onto-persistence proof uses NI and BF without necessitating optional assumptions; it does not give persistent separating power. The adjoint tests concern individual observers over C5, not separation principles. The native modal commutation criterion needs Boolean qualification only; the adjoints require Good-{t}. Their construction uses admitted families and lambda terms, with no external completeness or Choice. The integer-shift model has current BF at its root, not necessary BF; its negative verdict holds at every admitted type.

**Significance:** Separates the choice of logical operations from the contribution of higher types, and gives a systematic H foundation for the C-relative observer hierarchy. General representation theorems and reusable countermodels replace disconnected partial-signature comparisons.

**Lean certified:** The foundational implication H + OS ⇒ C + BF, with explicit endpoint identities.

**Notes:** Only the finite independent primitive family is completely classified. Remaining comparisons concern infinite nonprincipal material-versus-pointwise M/V separation outside the proved sufficient hypotheses; bare-H infinite affine character existence without an admission premise; further partial-signature reversibility; further boxed inverse comparisons and intrinsic atomless-meet characterizations; and an exact converse for Rev beyond its modal and parameter-noncontingency consequences. Both arrows Rev ⇒ SplitMono ⇒ OS are proved strict. C5 + ☐OS + No Pure Contingency ⇒ Rev is refuted even after strengthening ☐OS to ☐SplitMono. Zorn supplies admitted characters; Plenitude supplies normalization and the specified involutive witnesses. Pointed and relative maximality characterize separation and partial-character extension respectively, without a converse to general Zorn. The parameter theorem covers finitely many individual and endpoint-valued first-order relation parameters, not arbitrary higher-type parameters. Internal finiteness, whole-operation identities and explicit H premises retain their stated scope. Zorn supplies both affine and lattice partial-character extension. D_t collapses the inverse comparison but not the endpoint comparison; the atomless two-colour model proves the latter failure. The atomless region includes exact gap, convex-block and finite-factor criteria under their stated structural hypotheses. SurjSep ⇒ ☐OS and SurjSep ⇒ ☐SurjSep are refuted; The root truth-profile countermodel retains ☐BF; the integer-shift predecessor separately refutes SurjSep ⇒ ☐BF at every admitted type.

**Attribution:** OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source misc; proof notes unpaginated. Cited source constructions retain their stated attribution and draft dates.

**Proof length:** long (95,742 words in the [selected exposition](proof-lengths.json)).

**Proof locators:** Primitive-package classification §§1–5; typed separation §§1–7; reversible meet atomicity §§1–6; remaining branches and frontier in MAP §§3–10.; Composition-closed characterization §§1–4; finite-image normalization §§1–5; contingent Barcan §§2–5; necessary separation and atoms §§1–4.; Finite-block symmetry §§1–8; ND representation §§1–6; reversible quantifiers §§1–4; local conjugacy §§2–6.; Finite affine normalization §§1–7; right-inverse separation §§1–4; Plenitude normalization §§1–6; left-inverse models §§1–7 (all-maps strengthening in §7); ternary Cantor model §§1–9; modal selectors §7.; Fork and finite boundary §§1–5; Zorn character extension §§1–7; partial reversible normalization §§1–5; component-shift model §§1–8, including the endpoint-parameter schema in §6.; Zorn lattice characters §§1–6; negation/affine compatibility §§1–7; left-inverse decomposition §§1–6; finite colour-pattern propositions §§1–5.; Plenitude/endpoint bridge §§1–5; surjective observers §§1–7; linear/circular fibre model §§1–10; omega-chain observer classification §§1–6.; Reversible order actions §§1–8; fixed-point symmetry §§1–7; cancellative monoid observers §§1–7.; Truth-gap chains §§1–7; convex-block and finite-factor reductions §§1–7; root truth-profile surjective separation §§1–7.; Canonical adjoints §§2–7; integer-shift predecessor §§1–7.

**Proofs:** [GRAPH.md](../proofs/h-observer-space/GRAPH.md) · [MAP.md](../proofs/h-observer-space/MAP.md) · [README.md](../proofs/h-observer-space/README.md) · [finite-affine-separation.md](../proofs/h-observer-space/finite-affine-separation.md) · [fork-without-binary-families.md](../proofs/h-observer-space/fork-without-binary-families.md) · [identity-collapse.md](../proofs/h-observer-space/identity-collapse.md) · [local-tiers-and-models.md](../proofs/h-observer-space/local-tiers-and-models.md) · [observer-restrictions.md](../proofs/h-observer-space/observer-restrictions.md) · [primitive-package-classification.md](../proofs/h-observer-space/primitive-package-classification.md) · [quantifier-generated-lattices.md](../proofs/h-observer-space/quantifier-generated-lattices.md) · [relational-clone-model.md](../proofs/h-observer-space/relational-clone-model.md) · [representation-under-identity-bivalence.md](../proofs/h-observer-space/representation-under-identity-bivalence.md) · [reversible-meet-atomicity.md](../proofs/h-observer-space/reversible-meet-atomicity.md) · [term-closure-and-affine-branches.md](../proofs/h-observer-space/term-closure-and-affine-branches.md) · [truth-profiles-and-connective-reducts.md](../proofs/h-observer-space/truth-profiles-and-connective-reducts.md) · [two-orders-model.md](../proofs/h-observer-space/two-orders-model.md) · [typed-separation-and-classicism.md](../proofs/h-observer-space/typed-separation-and-classicism.md) · [reversible-meet-characterization.md](../proofs/h-observer-space/reversible-meet-characterization.md) · [finite-semilattice-normalization.md](../proofs/h-observer-space/finite-semilattice-normalization.md) · [composition-closed-characterization.md](../proofs/h-observer-space/composition-closed-characterization.md) · [finite-image-material-normalization.md](../proofs/h-observer-space/finite-image-material-normalization.md) · [logical-separation-with-contingent-barcan.md](../proofs/h-observer-space/logical-separation-with-contingent-barcan.md) · [necessary-separation-and-atoms.md](../proofs/h-observer-space/necessary-separation-and-atoms.md) · [reversible-separation-and-pure-truth.md](../proofs/h-observer-space/reversible-separation-and-pure-truth.md) · [finite-block-symmetry-reversible-gap.md](../proofs/h-observer-space/finite-block-symmetry-reversible-gap.md) · [necessity-of-distinctness-representation.md](../proofs/h-observer-space/necessity-of-distinctness-representation.md) · [reversible-quantifier-observers.md](../proofs/h-observer-space/reversible-quantifier-observers.md) · [local-conjugacy-and-reversible-observers.md](../proofs/h-observer-space/local-conjugacy-and-reversible-observers.md) · [finite-affine-normalization.md](../proofs/h-observer-space/finite-affine-normalization.md) · [split-inverse-logical-observers.md](../proofs/h-observer-space/split-inverse-logical-observers.md) · [plenitude-material-normalization.md](../proofs/h-observer-space/plenitude-material-normalization.md) · [finite-block-symmetry-left-inverse.md](../proofs/h-observer-space/finite-block-symmetry-left-inverse.md) · [ternary-cantor-observer-model.md](../proofs/h-observer-space/ternary-cantor-observer-model.md) · [fork-one-sided-inverse-separation.md](../proofs/h-observer-space/fork-one-sided-inverse-separation.md) · [zorn-affine-character-extension.md](../proofs/h-observer-space/zorn-affine-character-extension.md) · [partial-reversible-normalization.md](../proofs/h-observer-space/partial-reversible-normalization.md) · [component-shift-symmetry-reversible-gap.md](../proofs/h-observer-space/component-shift-symmetry-reversible-gap.md) · [zorn-lattice-character-extension.md](../proofs/h-observer-space/zorn-lattice-character-extension.md) · [negation-affine-compatibility.md](../proofs/h-observer-space/negation-affine-compatibility.md) · [left-inverse-separation-decomposition.md](../proofs/h-observer-space/left-inverse-separation-decomposition.md) · [finite-pinning-dedekind-propositions.md](../proofs/h-observer-space/finite-pinning-dedekind-propositions.md) · [plenitude-endpoint-bridge.md](../proofs/h-observer-space/plenitude-endpoint-bridge.md) · [surjective-logical-observers.md](../proofs/h-observer-space/surjective-logical-observers.md) · [linear-circular-fibre-left-inverse-gap.md](../proofs/h-observer-space/linear-circular-fibre-left-inverse-gap.md) · [omega-chain-surjective-observers.md](../proofs/h-observer-space/omega-chain-surjective-observers.md) · [reversible-semilattice-order-actions.md](../proofs/h-observer-space/reversible-semilattice-order-actions.md) · [fixed-point-symmetry-left-inverse-separation.md](../proofs/h-observer-space/fixed-point-symmetry-left-inverse-separation.md) · [full-cancellative-monoid-observers.md](../proofs/h-observer-space/full-cancellative-monoid-observers.md) · [reversible-truth-gap-chains.md](../proofs/h-observer-space/reversible-truth-gap-chains.md) · [reversible-semilattice-local-global.md](../proofs/h-observer-space/reversible-semilattice-local-global.md) · [root-truth-profile-surjective-separation.md](../proofs/h-observer-space/root-truth-profile-surjective-separation.md) · [canonical-adjoints-and-image-factorization.md](../proofs/h-observer-space/canonical-adjoints-and-image-factorization.md) · [integer-shift-predecessor-contingent-barcan.md](../proofs/h-observer-space/integer-shift-predecessor-contingent-barcan.md)

**Earlier saved manifests:** [original-manifest.json](certificates/full-typed-logical-separation-actual-c/original-manifest.json)

**Scope evidence:** [certification-closeout.json](certification-closeout.json) · [acceptance.json](certificates/full-typed-logical-separation-actual-c/acceptance.json)

**Selected exact certificates:** [certificate.json](certificates/final-full-typed-logical-separation-h-transport/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-h-bridge/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-h-closure/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-h-consequences/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-c-holes/certificate.json) · [certificate.json](certificates/final-full-typed-logical-separation-c-transport/certificate.json) · [certificate.json](certificates/full-typed-logical-separation-actual-c/certificate.json)
