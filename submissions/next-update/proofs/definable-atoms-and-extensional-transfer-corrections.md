# Corrections to model explanations and question status

25 October 2026. Connecting arguments and audit by OpenAI Codex, prompted by Daniel Kodsi. Direct source: this note, §§1–4 (unpaginated), `misc`.

## 1. The definable root has infinitely many atoms

Use `coalesced-definable-root` without changing its construction. Its propositions are pairs `(b,[T])`, with a freely chosen current truth bit and a profile of a pure term with one individual marker. For each external n ≥ 1 let A_n be the Fregean Axiom conjoined with exactly n individuals.

At a point satisfying A_n, Fregean entails Extensionality. Every admitted type is then finite and full: finite equality tests define every relation, and Extensionality identifies coextensive entities. The resulting pointed hierarchy is unique up to isomorphism; permutations of individuals act transitively. Each marker-dependent sentence consequently has one fixed truth value throughout these pointed A_n structures. The same holds at all transported targets. Thus the whole profile of A_n ∧ T is either that of A_n or bottom. A_n is nonzero by the finite full extensional model, and has false current truth bit at the infinite root. Hence A_n is an atom of the root proposition algebra. These atoms are pairwise disjoint.

The root is countably infinite because its profiles are finite terms. If every subfamily of the A_n had a join, taking joins would inject the powerset of the natural numbers into that countable algebra. Distinct subfamilies have distinct joins by disjointness and complementation. Therefore some subfamily has no join. Every external subfamily is an admitted current property, by the free identity coordinate; taking complements gives failure of the meet formulation of Boolean Completeness at t.

For Countable Boolean Completeness use the counting type t. Its standard numeral terms are distinct because current root properties with exactly n members distinguish them. Each numeral belongs to the least inductive cardinality family. The graph assigning each A_n its numeral is an admitted current relation. The missing-join family is therefore internally countable in the native schema. This repairs the completeness failures without the incorrect atomlessness claim. Atomicity's failure separately follows from the established pure Maximalism verdict and `maximalist-distinctness-incompatible-with-atomicity-t`.

## 2. Restrict Boolean-valued transfer to extensional structure formulas

In `full-boolean-valued-atom-and-atomless`, write B = 2 × A, a = (1,0), b = (0,1). Identity of ground entities is crisp. With singleton individuals, take F(*) = 0 and G(*) = a. Coextension has value b, equality has value 0, and the implication from coextension to equality has value a. Replacing a by b gives value b. The universal box-free Extensionality sentence thus has value at most a ∧ b = 0, whereas extensional predicate semantics validates it. Blanket transfer for every box-free typed formula is false.

The transfer used for analytical structures is narrower. Relations on finite powers of a fixed ground carrier are interpreted by Boolean-valued subset names. Use them only by application to carrier elements, with equality only on those elements; exclude literal equality of relation intensions and predicates applied to those intensions. Quantification over full relation domains covers every subset name, and formula induction yields the forcing interpretation in this fragment. A separate capacity argument places the real field on the chosen carrier. This correction leaves the CH and Transversal Choice verdicts intact.

## 3. Bare-C5 analytical contingency is source-reported

Bacon, *Could the truths of mathematics have been different?*, draft of 9 October 2025, pp. 22–23, note 55, already reports failure of Necessity of Analysis under C5, using a nonconstructible real. The absence of an encoded countermodel was not literature openness. The new constructible-ground model adds a native-language transfer and an audit of its stronger premises.

## 4. The strict Forcing Possibilism / CH conjecture is already refuted

The upstream proved-only closure already supplies `full-free-monoid-glued-constants-singleton` as a countermodel to the recorded four-premise incompatibility. Its full proposition algebra is the powerset of a countably infinite monoid, of size continuum. An infinite complete Boolean algebra has at least continuum many elements, so the strict eligibility condition asks only for finite algebras; finite proper intervals realize them. The model also satisfies the recorded necessary Rigid Comprehension, Intensional Choice and Non-contingency of CH premises.

The conjectured record status is historical metadata. Preserve the record and source attribution; the strict condition does not itself supply eligible infinite forcing algebras. The non-strict appendix formulation remains a separate question. No false proved-result verdict is asserted here.
