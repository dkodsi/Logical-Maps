# Database connections: integration register

Connections are pending until incorporated into the **upstream database**, including those already supplied in [PR #17](https://github.com/zwlgzwlg/Logical-Maps/pull/17). Checked against upstream `a89a5058` and PR head `a9d839a3` on 26 October 2026. The seven proposed patches remain unapplied upstream.

[Exact IDs, statements, proof locators, source hashes and comparison evidence](database-connections.json) accompany this page. The register covers the 10-24 v2 main and supplementary inventories, all 23 next-update entries, and the retained later follow-up. It distinguishes missing connections, new model verdicts, proof refinements and extensions requiring definitions.

All native connections below use C. RC means Relational Choice; Rigid Comprehension is written out. Unsubscripted principles are the full schemas. A model row records a simultaneous counterexample, not a theorem deriving its failures from its premises.

## Prepared native patches

| Family | Integration action | Delivery |
|---|---|---|
| C5 + RC ⇒ TC | New implication. The later Vicinity + RC result below subsumes it; preserve the C5 proof as a specialization. | [Patch 05](../next-update/patches/05-c5-choice.patch) |
| Vicinity + BCₜ + RC, or Zorn ⇒ Actuality | Two implications and the C5 + BCₜ + Zorn consequence. RC needs only t,t; Zorn only t. Keep the common construction and the BC_tt trade-off in one proof family. | [Patch 07](../next-update/patches/07-propositional-zorn-actuality.patch) |
| ☐Relational Choice and ☐Rigid Comprehension without Atomicityₜ | New Choice argument for both modalized atomless clouds. The exact strong joint package is retained in the machine register. | [Patch 02](../next-update/patches/02-cloud-relational-choice.patch) |
| C5 + Functional Choice and both quantified infinities without Necessity of Analysis | Constructible-ground Cohen model retaining Non-contingency of CH; preserve its specified ground and metatheory. | [Patch 03](../next-update/patches/03-analytical-contingency.patch) |
| Pure Maximalism with and without strict Forcing Possibilism | Add the positive definable-root and two negative pinned-root arguments. | [Patch 04](../next-update/patches/04-maximalism-forcing.patch); depends on 01 |
| Source corrections; FP ⇒ quantified Infinityₜ | Explanatory corrections and an alternative proof of an existing theorem, not new arrows. | [01](../next-update/patches/01-explanation-corrections.patch) and [06](../next-update/patches/06-forcing-infinity-proof.patch) |

The register includes each patch’s files, dependencies, new result specifications and model effects. Applying the patches in order gives the already-validated submission; integrating the stronger Vicinity theorem first makes the separate C5 edge redundant.

## Further connections awaiting integration

| Result or construction | Exact addition | Evidence and delivery |
|---|---|---|
| Vicinity and Choice | **Vicinity + RC ⇒ TC**; hence RC, TC, Zorn and Well-Ordering coincide over C + Vicinity. At σ, the choice instance is RC_(σt,σ); NDₜ is an alternative sufficient premise. | [Proof](proofs/vicinity-relational-choice-transversals.md) · Later follow-up; no patch. |
| Modal Choice | **NDₜ + BF + Intensional Choice ⇒ ☐Intensional Choice**, and the corresponding implication for Modalized Relational Choice. Only BF_(σt), respectively BF_(στt), is needed instancewise; the negations are rigid too. | [Proof](../next-update/proofs/choice-proof-simplifications.md) · PR item 17; no patch. See also `nd-bf-modalized-choice`. |
| Finite-signature Strong Possibility | For finite Σ, SP(Σ) is incompatible with each BF and Functionality instance. The infinite-signature extension only covers individual inputs when there are finitely many individual names. | [Proof](../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/signature-sp-barcan-20261022.md) · 10-24 v2; requires signature-qualified records. |
| Pure Strong Possibility | SP excludes arbitrary strong worlds, in particular Strong Actuality. The Strong Leibniz exclusion already follows upstream; no consistency claim is made. | [Proof](../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/sp-existential-products-20261022.md) · 10-24 v2 supplement; no patch. |
| Finite compression | Tame Rigidity + Rigid Power without Weakly Rigid Power at et, also without ☐Tame Rigidity. **Lean certified.** | [Proof](../classicism-results-2026-10-24-v2/proofs/finite-compression.md) · 10-24 v2; new model record. |
| Recurrent finite colour approximations | **☐BF + ☐Rigid Power + ☐Boolean Completeness + Tame Rigidity**, without Weakly Rigid Power or ☐Tame Rigidity at et. Atomlessness holds and Actuality and Rigid Comprehension fail at every world; Weak Rigid Comprehension also fails at et at the evaluation point. | [Proof](proofs/recurrent-colour-countermodel.md) · Ordinary construction; distinct from the certified finite-compression model. |
| Rigid Power propagation | **☐BF + Rigid Power ⇒ ☐Rigid Power**. More generally, Rigid Rigidity + Rigid Power suffices; instancewise, a rigid universal relation plus Rigid Power suffices. | [Proof, §11](proofs/recurrent-colour-countermodel.md#11-a-general-propagation-lemma-rp-over-a-rigid-universe-is-boxed-rp) · Retain the Rigid Power premise. |
| Supported products | Logical Necessity + ☐BF + ☐Tame Rigidity + ☐Countable Boolean Completeness + ☐RC, without Actuality, Vicinity, Weak Inextensible Comprehension, Boolean Completeness or Rigid Power. Retain the separate moving-individual variant with both quantified infinities. | [Proof](proofs/logical-necessity-supported-products.md) · 10-24 v2; narrower one-predicate result Lean certified. |
| Symmetric-surjection/free-word gluing | Logical Necessity + ☐Boolean Completeness + ☐BF + ☐Tame Rigidity + ☐Weakly Rigid Power + Atomlessness, without Actuality, Vicinity or RC. Its moving-individual variant also has both quantified infinities. Distinct from the preceding Choice model. | [Proof](../classicism-results-2026-10-24-v2/source/research/2026-10-22/followup/central-map-complete-gluing.md) · 10-24 v2 supplement; new construction. |
| Fixed-point entrance | Atomicity + Boolean Completeness + Rigid Comprehension + RC + Tame Rigidity + Rigid Power + Weakly Rigid Power + ☐Strong Actuality, without ☐Tame Rigidity. Also fails relational BF, NDₜ and Strong Leibniz. **Lean certified.** | [Proof](../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/fixed-point-entrance-cone.md) · 10-24 v2; preserve root/tail distinction. |
| Stitched forcing with a coalesced middle world | ☐Strong Leibnizₜ + Rigid Comprehension + ☐BFₜ + ☐RC + ☐Actuality + ☐BCₜ, without ☐Rigid Comprehension or all-type ☐Boolean Completeness. The missing BF is at et. | [Proof](../classicism-results-2026-10-24-v2/source/research/2026-10-22/followup/propagation-without-barcan-countermodel.md) · 10-24 v2 supplement; preserve forcing scope. |
| Signature Independence | Two extensional models for Σ={c:et}: one with two individuals, one with natural-number individuals. Both satisfy Independence and ☐Functional Choice; the first fails both Infinity schemata and axioms, the second fails the propositional ones. **Lean certified.** | [Proof](../classicism-results-2026-10-24-v2/source/research/2026-10-22/central-questions-audit.md) · 10-24 v2; two scoped models, not twelve discoveries. |
| Coalesced CH components | ☐Atomicity + ☐BF + ☐Strong Leibniz + ☐Tame Rigidity + Modal Well-Ordering without Non-contingency of CH. Preserve Con(ZFC) in the ordinary construction. **Lean certified for the stated CH/☐BF construction;** the additional rigidity verdicts have their own proofs. | [Proof](../classicism-results-2026-10-24-v2/proofs/coalesced-ch.md) · 10-24 v2; distinct from the incorporated Boolean-valued CH model. |
| Strict FP with Choice | Strict FP + ☐Functional Choice + quantified Infinity at e and t is compatible, via countable-world full S5. The negative FP direction is already recorded. | [Proof](../classicism-results-2026-10-24-v2/proofs/forcing-possibilism.md) · 10-24 v2; specialize the construction rather than all infinite S5 models. |
| Strict FP without Intensional Choice | Strict FP + both quantified Infinity axioms need not imply Intensional Choice. | [Proof](../classicism-results-2026-10-24-v2/proofs/forcing-possibilism.md) · 10-24 v2; free-root construction. |
| Infinity schemata versus axioms | ☐Functional Choice + both Infinity schemata with both quantified axioms necessarily false. A separate model retains ☐FP and necessary quantified Infinityₜ, plus the individual schema, while quantified Infinityₑ necessarily fails. | [Proof](../classicism-results-2026-10-24-v2/proofs/forcing-possibilism.md) · 10-24 v2; two Henkin compactness constructions. |
| Current versus necessary Relational Choice | At W₁ of qualitative contrast, C5 + RC holds while ☐RC fails. OS/SplitMono strengthen this same example but require extension definitions. | [Proof](../next-update/proofs/observer-choice-transport.md) · PR item 13; retain the W₁ evaluation. |
| Complete-algebra predecessor | ☐BCₜ + ☐BF + RC + Actuality without ☐Actuality. | [Proof](proofs/complete-boolean-root.md) · Later follow-up; new model argument. |
| Cofinite predecessor | BCₜ + BF + RC + Actuality without ☐BFₜ. | [Proof](proofs/complete-boolean-root.md) · Later follow-up; variant of the preceding family. |
| Modified interior | ND at every type + Atomlessness without BFₜ or ☐NDₜ; also without BCₜ. The BCₜ separation alone is already recorded. | [Proof](proofs/complete-boolean-root.md) · Later follow-up; same-evaluation verdicts. |
| Isolated interpretation root | Pure Max + BF + RC + Zorn + Actuality without BCₜ. Preserve the whole Choice/BF package; Max + Actuality alone was already covered. | [Proof](proofs/unrestricted-roots-fail-propositional-completeness.md) · Later follow-up; missing-supremum argument. |

## New verdicts for existing constructions

The singleton-individual audit proves that **nine symmetric constructions fail RC_(tt,t)**, while the old/new singleton variant satisfies **☐RC and ☐TC**. Three negative verdicts already follow upstream; **seven construction families still need updates**. The [construction audit](../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/rc-symmetric-singleton-applications.md) supplies a shared argument; `model_argument_updates` lists every affected native variant and only its missing verdicts.

The generic Boolean and countable-support models also retain their exact construction and metatheory in the register. Their projections to existing principle nodes already have recorded witnesses; their evaluator, restricted-choice and ZFC refinements remain separate contributions.

## Already covered connections; retain the additional proof content

- ND + Boolean Completeness already makes Inextensible Comprehension, Rigid Comprehension, Tame Rigidity and Weakly Rigid Power equivalent by proved closure.
- The old/new-individuals completeness/rigidity separation is incorporated. Preserve the sharper typed proofs and certificate references.
- Atomicityₜ + BF + Functional Choice ⇒ ☐Functional Choice is already derivable. Item 17 supplies the sharper finite list of BF instances and a shorter proof.
- Pure SP already excludes BF and Functionality. The finite-signature statement above has a separate scope and must not be silently generalized to all signatures.
- The two Strong Leibniz/Rigid Comprehension records added on the PR branch, for necessary relational BF and necessary Boolean Completeness, are already consequences of upstream proofs. They need record/proof reconciliation rather than duplicate arrows.
- RC + Boolean Completeness ⇒ TC already follows upstream through Actuality; preserve the independent direct proof and the weaker chain-completeness/type requirements.

The register separately retains formalizations of **C5 + Atomicityₜ ⇒ No Pure Contingency**, the existing **analytic rigidification theorem**, and the **old/new construction**, together with the simplified **Max–Atomicity certificate**. Original attribution and research-certificate scope remain separate from native verification flags.

## Scoped extensions and coverage

The machine-readable intake retains every one of the earlier **61 main entries and 176 supplementary claims**, all **23** next-update entries, and the **9** later follow-ups, with statements, source locators and proposed treatment. Thus operator equivalences, typed restrictions, new observer principles, infinitary results, arithmetic conservativity and model-theoretic comparisons remain findable without being forced into inaccurate native arrows.

Observer connections require the relevant definitions first. The follow-up includes the Mahlo-dependent contingent-CH model, complete-Henkin covers, classical cores and truth-preserving automorphisms. Their stated metatheory and additional hypotheses remain attached; dropping them does not create new native separations. SP consistency and bare-C RC ⇒ TC remain unresolved. The recurrent-colour model resolves BF + Tame Rigidity + Rigid Power ⇒ Weakly Rigid Power negatively. The strengthening BF + Rigid Power + Rigid Comprehension ⇒ Weakly Rigid Power (or ☐Tame Rigidity) remains unresolved; Rigid Comprehension is not Relational Choice.

This reconciliation checks the indexed sources and proved database closure; it does not independently re-prove the research. The native-connection proofs are included or linked to the earlier submissions. Broader extension intake marks supporting sources that are not part of this package. Native database records and verification flags are unchanged.
