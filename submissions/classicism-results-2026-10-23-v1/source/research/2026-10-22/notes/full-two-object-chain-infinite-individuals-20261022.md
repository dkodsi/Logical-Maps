# Full action model: two-object chain, one individual becoming infinitely many

Research scratch, 22 October 2026. Proposed new construction variant, not a database edit and not a newly settled conjecture. The proved-only Engine already separates `possible-infinity-e` from `axiom-of-infinity-e` using `coalesced-single-individual-root` and `finite-support-two-object-all-maps-at-singleton`. The conjectured result record has stale explanatory notes. The value of this variant is its simple category and its preservation of BF at every relational type.

## Sources and provenance

The immediate construction template is Cian Dorr's suggestion of 11 October 2026, recorded in `topics/classicism/models/full-two-object-chain-new-individual.yaml`: a full action model with one individual becoming two. The underlying full-action construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61 and Appendix D, pp. 73–74. The extension of the terminal individual set to the natural numbers and the infinity verdicts below are the current Codex research team's argument, not an assertion attributed to Dorr. A future new record's direct `certificate.source_id` should be `misc`. There is no Lean claim or named human check.

## 1. Construction

Let the category have objects 0,1 and arrows id₀,id₁,f:0→1, with no other arrows. Set D_e(0)={a}, D_e(1)=ℕ and f(a)=0. Evaluate at id₀. At every relational type, take every intension, exactly as in the source's full-action construction.

Concretely, recursively in the type τ=σ₁…σₙt, an intension at w specifies an arbitrary subset of D_{σ₁}(v)×…×D_{σₙ}(v) for each arrow h:w→v. At object 0 this is a pair of subsets, one for id₀ and one for f; at object 1 it is just one subset, for id₁. Transport along f forgets the id₀ component and retains the f component. For the empty tuple, these are subsets of the outgoing-arrow set. The source's full-action theorem therefore supplies a model of the fixed relational theory C. No e→e operation type is introduced; the map f on individuals is part of the external model data.

The construction works in the ordinary set-theoretic metatheory. The particular infinity separation and surjectivity claims below do not use a choice of elements from an arbitrary family.

## 2. Actual individual finiteness

Write 0_e and Suc_e for the map's Frege cardinal terms and 1_e:=Suc_e(0_e). C proves N_e(1_e), by successor closure and N_e(0_e).

At object 0 the universal individual property has precisely the member a. After removing a its current extension is empty. Thus, directly from the definitions,

    1_e(⊤_e)

is true at id₀. Consequently AxiomOfInfinity_e is false there. The Infinity Schema at e also fails, already at its two-distinct-individuals instance. This argument does not confuse a current empty extension with the necessarily empty relation: the zero-cardinality predicate tests the current universal quantifier, as its definition specifies.

## 3. Possible individual infinity

At object 1 there is only the identity arrow. Thus its higher-order structure is the ordinary full extensional relational hierarchy over ℕ. Its Frege finite cardinals are exactly the standard finite cardinality properties:

- Every standard numeral belongs to N_e, by finite induction.
- The property of being a standard numeral is an admitted property at object 1, because the model is full; it contains zero and is successor-closed. The impredicative definition therefore puts every N_e-member in that property.
- No standard finite cardinal counts the universal property of ℕ.

Hence AxiomOfInfinity_e is true at id₁. Transporting the root proposition expressing that sentence along f gives the true terminal proposition, so that root proposition is nonbottom. Equivalently, PossibleInfinity_e holds at id₀.

Together §§2–3 verify the desired separation. This is an alternative simple witness for an already recorded nonimplication, not evidence that the conjecture was previously unresolved.

## 4. BF at relational types, but not individuals

For every relational type τ, transport D_τ(0)→D_τ(1) is the projection onto the f component and is onto. An arbitrary terminal intension is lifted by taking it as that component and taking the empty id₀ component. At the terminal object all transports are identities. The ordinary full-action BF criterion therefore gives □BF_τ at every relational τ. This is also exactly the argument `full-epic-barcan-relational`: f is epic, since object 1 has only its identity outgoing arrow.

At type e, let H:=λx(x=a) be the haecceity of the sole root individual. It contains a at id₀, and its transported extension is {0} at object 1. At the root every individual necessarily has H, since the only individual a transports to 0. But necessarily every individual has H is false, since 1∈ℕ at the terminal object does not have H. Thus BF_e, and therefore the full BF schema, fails at the root.

The individual ND instance nevertheless holds necessarily: it is vacuous among distinct individuals at the singleton root and true at the terminal object with only its identity arrow. The failure of BF_e is domain growth, not merging of existing individuals.

## 5. Additional directly checked features

At type t the root domain is P({id₀,f}), with four elements, and the terminal domain is P({id₁}), with two. The root's fourth Frege numeral counts all propositions, and the terminal's second does; hence propositional Axiom of Infinity and its possible form both fail. In particular possible individual infinity does not imply even actual propositional infinity in this model.

Each relational domain, with its algebraic Boolean order, is the full powerset of its disjoint collection of world–tuple points. Therefore it is a complete atomic Boolean algebra: unions supply joins of every admitted family, and singleton world–tuple points are atoms below every nonzero element. This holds at both objects. Consequently □BooleanCompleteness and □Atomicity hold at every relational type.

The singleton id_w is an actual-world proposition at each object w, so □Actuality also holds. No claim of ND at relational types is made: for example the distinct root propositions {id₀,f} and {f} both transport to terminal truth. The pure sentence AxiomOfInfinity_e changes truth along f, so No Pure Contingency fails.

A particularly useful cardinal check is D_et(0)=P({a})×P(ℕ), which is infinite despite the finite root e and t domains. This does not contradict the finite-type dichotomy under full BF: precisely its e-input Functionality/BF instance fails here.

## 6. Small candidate verdict set

If a separate model record is desired later, a suitable construction-based id/title is `full-two-object-chain-infinite-individuals` / “Full action model: two-object chain, one individual becoming infinitely many.” The minimal distinctive assertions needed for the main use are:

- satisfies `possible-infinity-e` and `necessary-barcan-relational`;
- violates `axiom-of-infinity-e` and `barcan-r`.

The further directly verified Boolean/atomic/actuality and propositional-finiteness facts in §5 may be recorded only after integration checks against the current engine. Do not add the construction to the database merely because this scratch exists.
