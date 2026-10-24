# Endomorphism splitting does not recover cross-type splitting, even with schema Infinity

Scratch construction, 22 October 2026. New model argument in the fixed C framework, using standard full action models and ordinary many-sorted Henkin compactness. Independently checked by the rigidity lane on 22 October; no record edits. This concerns the **Infinity Schema** (arbitrarily many distinct entities, one axiom for each external natural n), not the stronger quantified Axiom of Infinity.

For each relational A consider the endomorphism sentence

    EndSplit_A := ∀f^(AA)[(Inj(f)∨Surj(f)) →
                     ∃g^(AA)(g∘f=id_A ∧ f∘g=id_A)].

Both conclusions are literal operation identities, hence strong inverse equations. This implies the more customary separate statements that injective endomorphisms have strong left inverses and surjective endomorphisms have strong right inverses. The theorem below establishes considerably less strength than the corresponding schemata for arbitrary source and target types.

**Theorem.** Relative to the standard full action constructions and ordinary first-order compactness for the Henkin presentation, the following theory is consistent:

    C + □Actuality + BF + {□EndSplit_A : A relational}
      + {□∃x₁^σ...xₙ^σ ⋀_(i<j) x_i≠x_j : every type σ and every external n≥1}
      + ¬ND_t.

Thus even necessary schema Infinity does not make endomorphism splitting an adequate substitute for cross-type splitting. In particular it does not yield C5 or Functional Choice. The latter follows because FC→ND.

## Finite approximating models

Fix a finite nonempty individual set I and a finite cyclic group G. Use a two-object category with objects 0,1:

    Hom(0,0)={id₀},    Hom(1,1)=G,
    Hom(0,1)=G,        Hom(1,0)=∅.

The group acts on Hom(0,1) by left multiplication, so the latter is a regular left G-torsor. Composition otherwise uses identities and the group law. The individual action is constant I with every arrow acting as identity. Form the standard full relational intension hierarchy and evaluate at object 0.

Every type domain at either object is a nonempty finite set, by induction on types. At type t the cardinalities are

    |D_t(0)|=2^(1+|G|),    |D_t(1)|=2^|G|.

Every transition on every type is surjective. At e it is identity. At a relational type, transport along h:0→1 restricts an intension to the arrows gh. The map g↦gh is injective, so any target intension can be extended arbitrarily to all remaining source-arrow coordinates. Fullness admits the extension. Group arrows are invertible. This verifies BF at every type and every world directly through its usual surjective-transport semantics.

Actuality holds at every object: the singleton identity-arrow proposition is present in the full propositional domain. At the root p={id₀} is true, but after any arrow to 1 it becomes bottom, since there is no return arrow. Thus p≠⊥ now while that inequality fails later; ND_t fails.

Let f:A→A at either object be actually injective or actually surjective. Its current domain is finite, so it is bijective. Along every later arrow its transported map is surjective: choose an actual antecedent for a target using surjectivity of transport, and then a preimage under the root bijection. The transported endomap is again on a finite set, so is bijective. Its componentwise inverses commute with transport by the naturality equation for f and cancellation of the bijections. These components are indexed by arrows/intension components, not just by target objects: different arrows to the same object can transport f differently. A natural family of maps with relational output is an admitted operation in the full model: take its extensions on the trailing relational arguments at each arrow. The resulting g satisfies both inverse equations at every later object. Hence EndSplit_A holds necessarily, for every relational A.

## Passing to necessary schema Infinity

For any bound N, choose |I|≥N and 2^|G|≥N. Then at every object e and t have at least N distinct elements. Every other relational type has at least as many entities as t: embed propositions as constant relations and evaluate at any fixed tuple to see injectivity. Thus all types at all worlds have at least N elements.

Any finite subset of the proposed infinite theory mentions only finitely many external numbers n; choose N at least their maximum. The corresponding finite full action model satisfies the whole finite subset, including all C axioms, □Actuality, BF, all EndSplit schemata, and ¬ND_t. Ordinary compactness in the many-sorted first-order presentation, with application and lambda-template symbols and the C axiom schemes, now gives a Henkin model of the entire theory.

This compactness step asserts no full standard-domain model with these infinite properties. It also does not promote the Infinity Schema to the quantified Axiom of Infinity. Indeed the finite approximations satisfy even `∀f^(AA)(Inj(f)↔Surj(f))`, so the compactness model can be required to satisfy that for every relational A as well. The apparent infinity of every domain is therefore compatible with strong internal finiteness properties of the admitted endomorphisms.

## Relation to the exact section theorems

The same theory cannot satisfy all cross-type strong injection retractions, because that schema is equivalent to C5 and entails ND. It cannot satisfy all cross-type ordinary right inverses either, since □Actuality supplies Actuality and Actuality+RInv is equivalent to FC, which entails ND. The missing maps therefore occur between different types, despite every endomorphism satisfying the displayed strong splitting condition.

A compact mirrored family still suffices for the full characterizations: injections A→tA for the Plenitude/C5 side, and surjections tA→A for the Functional Choice/□FC side. See `.reproduction/classicism-research/functional-choice-by-sections.md` and `.reproduction/classicism-research/choice-uniformization.md`, §18.

Source discipline: the construction uses the database's full action model semantics from Bacon–Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp.58–61, as cited in the existing full-action-model records. The particular torsor category, endomorphism verdict, and compactness separation are arguments produced in this session and would be recorded under source `misc`, not attributed to that paper.
