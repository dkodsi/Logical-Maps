# Classicism research, 22 October 2026

For the evolving collection of results, prose proofs, Lean sources and contribution summaries, start with the [research collection](consolidation/README.md). The overview below preserves the original research summary; the collection links the subsequent formalization status and corrections.

This directory contains ordinary mathematical proofs and model constructions developed during the research session. The database and its published or human-authored proofs have not been changed. Several main arguments received independent checks by other research agents; none is labelled human-checked or Lean-verified. “New” here means a new argument or formulation in this session, not verified novelty in the literature.

For a broader statement-by-statement overview, use the [consolidated result catalog](RESULT-CATALOG.md).

The subsequent [counting audit and summary index](COUNT-AUDIT.md) identifies 134 distinct result families under conservative grouping and links the saved summaries from all eight research chats.

For the explanation and synthesis chat, start with the [synthesis handoff](SYNTHESIS-HANDOFF.md), which adds the latest conjecture accounting, reading order, and corrections to preserve.

The fixed framework is C in the database's relational type system. Write **B = C + □Plenitude = C5 + Atomicity** and **F = C + □Functional Choice**. C5 includes necessary distinctness, not merely current ND. Relational Choice and Rigid Comprehension are different principles; the notes sometimes abbreviate both as RC, so consult each note's definitions.

## Main positive results

1. **A short evaluator axiom for B.** If `Eval(E)` says that E sends each currently true proposition to top and each currently false proposition to bottom, then **B is equivalent to `□∃E Eval(E)`**. Each world may have its own evaluator. Requiring one evaluator to remain correct everywhere instead gives Extensionality. The six distinct positions are Actuality, ND + Actuality, Gallin Comprehension, C5 + Actuality, B, and Extensionality. [Evaluator hierarchy](notes/actual-truth-evaluator-ladder.md).

2. **Choice as splitting surjections.** Over C, Functional Choice is exactly Actuality plus the existence of right inverses for surjective operations between relational types. Boxed Functional Choice is exactly boxed Actuality plus strong right inverses for actual surjections. Plenitude has the parallel characterization by left inverses for injections between relational types. The type scope and modal placement are essential. [Proofs and separating models](notes/functional-choice-by-sections.md).

3. **Ordinary mathematics already has a local home under Actuality.** A true world atom w gives an extensional relational Henkin higher-order core, with inherited identity, over all current individuals. Core truth values are bottom and w. Relational Choice transfers to ordinary Choice, and the database's quantified Infinity axiom transfers exactly. This local interpretation can collapse later; Gallin Comprehension separately gives globally two-valued canonical representatives. [World-slice construction](notes/actuality-world-slice-core.md); [Gallin core](notes/gallin-extensional-core.md).

4. **Local completeness needs only Actuality.** Every represented family in a Boolean interval supported by the actual atom has a supremum obtained by cutting its current existential union by that support. This supplies algebraic completeness inside the local core without assuming ambient Boolean Completeness. The support projection is the unique representative of each admitted current extension. [World-slice construction, §7](notes/actuality-world-slice-core.md).

5. **ND + Inextensible Comprehension implies Weakly Rigid Power.** More precisely, `ND_t + IC_(τt) ⇒ WRP_τ`. The proof also gives Tame Rigidity and Rigid Power at the relevant types, and characterizes rigid relations as persistent, necessarily internally separated relations. No optional premise is silently boxed. [Complete proof](notes/nd-inextensible-comprehension-implies-weak-power.md).

6. **Several rigidity laws have exact algebraic definitions.** Tame Rigidity is closure of rigid relations under every existing represented join. ND is equivalent to closure of rigid relations under binary intersections; full rigid-complement closure corresponds to C5. Weakly rigid relations are already closed under existing represented joins in C. [Join laws](notes/rigidity-by-joins-and-boolean-closure.md); [Boolean closure laws](notes/rigid-boolean-closure.md).

7. **Concrete consistent strengthenings of F.** Full Gallin models support both quantified Infinity axioms. World-profile principles are independently calibrated by full models with worlds N or P(N), and by restricted Henkin models. Unique realization of all individual profiles and supported higher-core profile principles are consistent; unrestricted profile realization at a relational input type is blocked by a diagonal. [Infinity and world-richness guide](notes/infinity-world-richness-consolidation-20261022.md); [detailed world constructions](notes/world-cardinality-ucp-20261022.md).

8. **World richness does not hide Choice.** Explicit nominal Henkin models satisfy B, both Infinity axioms, and substantial world-profile principles while failing Functional Choice. One realizes profiles at every finite supported core rank. These constructions separate the positive axioms' mathematical roles. [Construction guide](notes/infinity-world-richness-consolidation-20261022.md); [model comparison](notes/gallin-comparison.md).

9. **Faithful probability is an exact, independent strengthening.** Over F plus quantified individual Infinity, a strictly positive finitely additive probability on propositions exists exactly when the atomic worlds are internally countable, equivalently when the internal countable chain condition holds. A countably additive such probability then exists as well. Full Gallin models with worlds N and P(N) separate the principle. It is compatible with every finite binary pattern but incompatible with realizing every infinite binary profile. The higher-type variants and symmetry restrictions are sharper. [Proof and explicit scope](notes/faithful-probability-countable-worlds.md).

## Progress on existing conjectures

**Relational Choice + Boolean Completeness ⇒ Transversal Choice.** The complete proof uses guarded partial selectors, preservation of represented joins by evaluation, and a fixed-point argument in bare C. The sharper choice instance selects points rather than whole predicates. Internally well-ordered chain completeness suffices in place of full BC. [Main proof](notes/relational-choice-boolean-completeness-transversal-proof.md); [sharper operation](notes/rc-guarded-progressive-operation.md); [independent audit](notes/INDEPENDENT-AUDIT-REPORT-01a164ea.md).

**Strong Leibniz + Rigid Comprehension ⇒ necessary Strong Leibniz and necessary relational BF.** The rigid family of strong worlds must include bottom. Its rigid cuts supply the required future witnesses without necessitating an unboxed comprehension assumption. This proves the existing conjecture from weaker unboxed premises. The type-e Barcan claim is not included. [Proof](strong-leibniz-rigid-bottom-cut.md); [scope refinements and independent audit](notes/INDEPENDENT-AUDIT-REPORT-01a164ea.md).

A further bridge is **Relational Choice + countable Boolean completeness + the matching countable chain condition ⇒ Boolean Completeness**, hence the corresponding transversal conclusion. [Proof](notes/relational-choice-countable-completeness-ccc.md).

**A corrected model separates ND + BC from Rigid Comprehension.** The existing old/new-individual construction satisfies full Boolean Completeness at its evaluation point E, while failing Inextensible Comprehension and Rigid Comprehension already at et. Boolean Completeness fails at the accessible point O, so it is not necessary. The recorded failure at E used an external even-haecceity family that cannot be an admitted property. The new all-type proof classifies each relation by two symmetry-invariant profiles and forms joins componentwise. Four research agents independently checked the central argument. [Clean separation proof](notes/old-new-boolean-completeness-and-rigidity-separation.md); [source audit](notes/old-new-boolean-completeness-source-caveat.md); [future failure](notes/old-new-necessary-bc-failure.md). The existing model record has deliberately not been edited, so its BC-failure verdict should not be relied on pending integration of this correction.

Relational Choice alone ⇒ Transversal Choice and unrestricted Tame Rigidity + Rigid Power ⇒ Weakly Rigid Power remain unresolved. The notes contain audited partial results and failed-countermodel obstructions, not purported settlements.

## Comparison with Maximalism

The results do **not** prove that original finitary Maximalist Classicism is inconsistent. It has models. Several natural-looking extra principles are consistent with it, including Actuality in suitable constructions. Nor has the consistency or inconsistency of Strong Possibility been settled.

The concrete negative evidence is more precise:

- **Maximalism forbids a numerical predecessor operation.** At each counting type σ it refutes `∃f ∀n∈Nσ [f(Sucσ n)=n]`, even though the ordinary predecessor relation is a total functional graph on the numbers. Necessary Identity transports any proposed operation's values into a possible finite Fregean world, where two successive inputs collapse but their required outputs differ. Plenitude represents the padded predecessor graph. Max similarly blocks operations representing the canonical arithmetic correspondence between counting types. [Exact argument and scope](notes/infinity-world-richness-consolidation-20261022.md).
- Maximalism fails an explicit guarded numerical join, not merely an unspecified completeness schema. [Infinity/arithmetic guide, §3](notes/infinity-world-richness-consolidation-20261022.md).
- Pure Strong Possibility and signature Strong Possibility are incompatible when the signature contains a relational constant. Consequently the proposed implication from signature Strong Possibility to pure Strong Possibility is equivalent to inconsistency of the signature theory. With finitely many individual names, signature Strong Possibility also imposes an exact bound on the actual individual domain. [Signature audit](notes/audit-signature-to-pure-sp-20261022.md).
- With the stated infinity and coding qualifications, positive theoremhood is Σ₁-complete, Maximalist theoremhood is Σ₂-complete, and Strong-Possibility theoremhood is Σ₃-complete **if that theory is consistent**. Adequate countable-model oracle requirements rise correspondingly. Demanding externally standard natural numbers changes this comparison substantially. [Precise comparison and qualifications](notes/comparison-handoff-20261022.md).
- Genuine infinitary lambda comprehension can contradict original Maximalism. This is an explicitly enlarged logic, not a contradiction derived in the original C framework. [Structural handoff](notes/structural-lane-handoff.md).

## Reading the evidence

Start with the short proof files above and the three lane guides: [structural](notes/structural-lane-handoff.md), [Infinity/world richness](notes/infinity-world-richness-consolidation-20261022.md), and [computability/model theory](notes/comparison-handoff-20261022.md). The archived `notes/` directory preserves longer research reports, audits, corrections, and unresolved attempts. Later corrections in a long report supersede earlier speculative passages; a heading alone is not a theorem certificate.

The archive contains 136 mathematical notes and two small checking scripts. `archive-manifest.json` records the snapshot hashes. These counts measure saved research material, not distinct theorems or independent verification. The main database still contains 132 principles, 447 results and 162 models, and its validation passes.

No aesthetic judgment has been converted into a mathematical inconsistency claim. The positive case consists of explicit interpretations, exact characterizations, relative-consistency constructions, and separations.
