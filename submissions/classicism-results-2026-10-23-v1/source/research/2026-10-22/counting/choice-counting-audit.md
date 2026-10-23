# Conservative count: choice, evaluators, probability and actual/Gallin cores

Counting audit, 22 October 2026. Scope: canonical archived reports under `research/2026-10-22/notes/`, compared with RESULT-CATALOG. This counts **grouped, independently stated proved conclusions**, not individual arrows, lemmas, proof versions, audits, files, or literature-novel theorems. A multiway equivalence counts once; tightly related type/corollary versions are grouped. All premises stated in the source remain in force.

**Defensible subtotal: 26 result families = 22 theorem/reformulation families + 4 separation/construction families.** There is also one shared corrected-model family (old/new), listed separately to prevent duplication with the principles/rigidity totals. If allocated to this lane, the subtotal is 27. This is deliberately below the number of separately provable propositions in these files.

## Proved theorem and equivalence families: 22

1. FC iff Actuality + pointwise sections of actual surjections. Mirrored type-fragment reduction included, not separately counted. (`functional-choice-by-sections.md`)
2. Boxed FC iff boxed Actuality + strong sections; fully boxed ordinary-section formulation included. (same)
3. Plenitude iff Actuality + pointwise retractions of actual injections. (same; `choice-uniformization.md`)
4. C5 iff persistence of actual injectivity iff strong retractions of actual injections. (`choice-uniformization.md`)
5. BF_rel persistence/splitting calculus: persistence of surjectivity, idempotence or involutivity characterizes BF_rel; strong sections iff ordinary sections + BF_rel. These related law formulations are one family. (`functional-choice-by-sections.md`; `reversible-comprehension-and-algebraic-laws.md`)
6. Per-map categorical/strong-splitting classification: Epi(f) iff necessary surjectivity; strong left invertibility iff necessary injectivity, at the stated relational types. (`choice-uniformization.md`)
7. Plenitude iff representation of all total symmetric single-valued graphs (involution representation). (`reversible-comprehension-and-algebraic-laws.md`)
8. The six evaluator equivalences, grouped as ONE hierarchy/classification: Actuality truth-fiber, ordinary BE, globally bivalent evaluator, unique ordinary BE, necessary local BE, fixed necessarily correct BE. Strictness counted separately below. (`actual-truth-evaluator-ladder.md`)
9. GC canonical evaluator/extensionalization theorem: unique globally bivalent evaluator, selected-world normal form, unique TwoVal representatives, idempotent Boolean normalization and pullback naturality. Grouped rather than counting each operator law. (`gallin-bivalent-evaluator.md`)
10. GC quantifier-law family: current-predicate commutation, safe boxed absorption, and exact selected-world-relative-BF characterization of the stronger law. No proof of the unrestricted stronger law is counted. (same)
11. Ordinary BE plus modal commutation forces Extensionality (and converse). (same)
12. Actuality iff localized extensionality; the supported current extensional relational Henkin HOL interpretation over all current individuals. (`actuality-world-slice-core.md`)
13. Ambient Relational Choice transfers to ordinary Choice in the local core; GC-core version included as the same transfer family. (`actuality-world-slice-core.md`; `gallin-extensional-core.md`)
14. Exact quantified Infinity transfer to the local/GC cores for the stated original base sort. Two constructions, one transfer family. (same two files)
15. Complete atomic local intervals and their unique supported projection representatives; existing-join preservation included. (`actuality-world-slice-core.md`, §§7–8)
16. Globally TwoVal GC core and its canonical isomorphism with the Actuality slice as current structures. (`gallin-extensional-core.md`)
17. Exact preservation of represented individual relations, well-orders, cardinal comparisons and induction under the local projection, with extensional relation equality. (`actuality-world-slice-core.md`, §8)
18. Faithful probability iff internally countable atomic worlds iff internal ccc; existence of a countably additive replacement. (`faithful-probability-countable-worlds.md`)
19. Probability type classification and ceiling: atom-product criterion, et/all finite individual arities, tt iff finite worlds, and all-type incompatibility with quantified Infinity_e. Grouped as ONE classification. (same, §§7–8)
20. Faithful probability versus full N-profile realization: incompatibility, despite compatibility with every finite binary pattern. (same, §5)
21. Permutation-invariant faithful probability iff internally finitely many worlds, with unique uniform state. (`probability-and-world-symmetry.md`)
22. Finite-parameter pure-term definability of faithful probability forces finite worlds, with the precise parameter/output-core restrictions. (same)

Items 12–17 and 21–22 are cross-lane work with rigidity. Count them once globally. Item 8 overlaps root's BE proof note. None should be recounted for appearing in both README and RESULT-CATALOG.

## Strict separations and constructions: 4 grouped families

23. Strict six-level evaluator hierarchy: five adjacent nonimplications, realized by the chain, double-retract, retract, atom-plus-atomless, and involution-group models. Counted as ONE separation family, not five new model constructions. (`actual-truth-evaluator-ladder.md`)
24. Independence of the two section-decomposition conjuncts and the strong/modal scopes: four stated witness configurations. Existing chain/retract constructions overlap item 23, but the additional splitting verdicts are different claims. Counted as ONE independence family. (`functional-choice-by-sections.md`, §5)
25. Probability model calibration: full (E,W)=(N,N), (N,P(N)), (P(N),N) separates propositional probability and individual-state probability while retaining the stated Infinity and F background. Counted as ONE family. (`faithful-probability-countable-worlds.md`)
26. Finite torsor models plus Henkin compactness give endomorphism splitting + necessary all-type Infinity SCHEMA without ND. This is a RELATIVE CONSISTENCY construction, not a quantified-Infinity model claim. (`endomorphism-splitting-infinity-separator.md`)

All constructions are conditional on the stated ordinary metatheory/model semantics. Those qualifications do not make them unproved conjectures. They are not proofs of absolute consistency or philosophical truth.

## One shared corrected model, excluded from subtotal to avoid duplication

27. Existing old/new construction: full BC at E, with ND and failure of IC/Rigid Comprehension; BC_et fails at O, hence BC is not necessary at E. The inadmissible old witness and both replacement proofs are ONE corrected-model family. (`old-new-boolean-completeness-and-rigidity-separation.md`; `old-new-boolean-completeness-source-caveat.md`; `old-new-necessary-bc-failure.md`)

The resulting equivalence of IC/rigidity/tame rigidity/WRP over ND+BC belongs with the principles/root consolidation, not added again here.

## Open or unproved: excluded from counts

* Bare pointwise RInv ⇒ ND.
* Whether categorical epimorphism splitting supplies the missing BF hypotheses.
* Universally boxed unrestricted quantifier commutation for a globally bivalent evaluator (the exact relative-BF characterization is proved, its universal validity is not).
* Any stronger full external-powerset interpretation, or quantified-Infinity upgrade of item 26.

## Summaries and source list

This lane DID produce a final summary: `notes/choice-lane-final-handoff.md`. The principal clean proof summaries are `functional-choice-by-sections.md`, `actual-truth-evaluator-ladder.md`, and `faithful-probability-countable-worlds.md`; the core and symmetry files above carry their own theorem statements and audit qualifications. This audit verifies THIS lane's summaries, not that every other task wrote one.

Canonical files inspected or matched to the saved handoff/catalog: RESULT-CATALOG.md; choice-lane-final-handoff.md; functional-choice-by-sections.md; actual-truth-evaluator-ladder.md; gallin-bivalent-evaluator.md; actuality-world-slice-core.md; gallin-extensional-core.md; faithful-probability-countable-worlds.md; probability-and-world-symmetry.md; reversible-comprehension-and-algebraic-laws.md; endomorphism-splitting-infinity-separator.md; the three old/new files. The rolling choice-uniformization.md supplies the explicitly referenced supplementary categorical/persistence proofs and is not itself an extra counted result.
