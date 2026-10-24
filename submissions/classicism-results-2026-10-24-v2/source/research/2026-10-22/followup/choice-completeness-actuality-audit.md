# Audit of the proposed RC + BC implication to Actuality

22 October 2026. Further adversarial self-audit by OpenAI Codex, not an independent review or formal verification. Direct source: `misc`, this note. The original proof, frozen archive, and database records are preserved.

## Scope and novelty check

The proposed local theorem is C + RC_(t,t) + BC_(tt) ⇒ Actuality, with actual unboxed premises. Its proof is in `choice-completeness-actuality.md`, §§1–2 and 7. This audit concerns the use of the canonical-chain lemma and the represented disjoint refinement.

A fresh proved-only `scripts.pmap.load_topic` / `Engine` query for premises `[relational-choice-r, boolean-completeness-r]` and conclusion `actuality` returned no derivation, no exclusion, and no recorded separator. The only proved direct record combining BC with a conclusion of Actuality adds C5. This is a statement about the map, not a literature-wide novelty verdict.

The public Classicism drafts give evidence that the new interaction was not known there. In §2.3, printed p. 32, Bacon and Dorr say that, so far as they know, both Relational Choice and its negation are compatible with every consistent combination of their listed principles. The 16 May 2023 draft is indexed at <https://philpapers.org/archive/BACC-8.pdf>; its text was available in the search index, while direct retrieval returned HTTP 403. The author's directly accessible 1 July 2022 draft contains the same statement on printed p. 32: <https://andrew-bacon.github.io/papers/Classicism.pdf>. A targeted web search found no later proof of the exact implication. That limited search cannot exclude unpublished or differently formulated work. The appropriate description remains **a proposed new result, with priority and independent correctness checks outstanding**.

## The exact canonical-chain input

Fix a represented X:tt with algebraic join j. Let P(b) mean b≤j. Its least element is ⊥. RC_(t,t) supplies an actually total entity-functional graph S which chooses x with Xx and x≰b when b<j, and chooses ⊥ otherwise. Seriality below j uses the least-upper-bound clause for j; elsewhere the specified default is available.

Define the graph

    f(b,c) := ∃x[S(b,x) ∧ c=(b∨x)].

On P it is total, entity-functional and progressive; it is strict below j and fixes j. These are actual claims about a represented graph. No operation representing S, Plenitude, or future functionality is used.

An f-chain C:tt is a represented internally well-ordered subset of P such that each b∈C is the supremum **within P** of

    I(C,b)(c) := ∃a[Ca ∧ a<b ∧ f(a,c)].

These predicates have admitted types. In particular, the definition asks that a given b satisfy a supremum formula; it does not use a choice operation on predecessor families or assume an external ordinal sequence.

The comparison proof from `../notes/relational-choice-boolean-completeness-transversal-proof.md`, §5, survives direct checking. The common part consists of common points with coextensive predecessor families. It is an initial segment of both chains. If both complements have least members, those members have precisely the same actual predecessor extension. Entity-functionality of f gives the same image extension, and antisymmetry of the algebraic order gives the same supremum **entity**. That contradicts their being outside the common part. No equality of coextensive predicate codes is inferred.

Consequently

    A(b) := ∃C[C is an f-chain ∧ Cb]

is a represented internally well-ordered chain. A nonempty represented subproperty has a least member by intersecting it with a chain containing one of its members and using initial-segment comparison. For any b∈A, its predecessors are exactly those in any constituent f-chain containing b, so its supremum equation transfers to A.

Only now is completeness called upon: A has a supremum u in P. If u∉A, A has no greatest point, and u is also the supremum of f[A]. Adjoining u therefore gives another f-chain, contradiction. If f(u)>u, adjoining f(u) similarly gives another f-chain, contradiction. Thus f(u)=u. Since f is strict below j and u≤j, u=j. Hence j belongs to A and is its greatest point.

## The interval-to-ambient supremum step

One detail in the original short disjoint-refinement proof deserves explicit justification. Suprema in the canonical-chain definition are computed within P=[⊥,j], whereas a proposed upper bound k of the increments can be an arbitrary proposition.

For any represented family Y contained in P, its supremum b within P is also its ambient Boolean supremum. Indeed, if k is any ambient upper bound of Y, then k∧j is an upper bound lying in P. Thus b≤k∧j≤k. Conversely an ambient supremum belonging to P is plainly the interval supremum. This uses only binary meet, not additional completeness.

This justifies using the predecessor supremum equation against arbitrary k in the spanning argument below. It is an omitted explanation, not a new premise.

## Representedness, disjointness, and spanning

The increment family is the admitted property

    Δ(d) := ∃b c[A(b) ∧ b<j ∧ f(b,c) ∧ d=(c∧¬b)].

No function assembling an externally indexed family is needed. Entity-functionality of f guarantees a unique increment for each b<j in A. Its selected x satisfies x≰b, so d=(b∨x)∧¬b=x∧¬b is nonzero and d≤x with Xx. If b<c belong to A, the predecessor equation at c gives f(b)≤c. Hence d_b≤c and d_c≤¬c, proving disjointness. Distinct increments cannot accidentally coincide: nonzero disjoint propositions are distinct.

Every Δ-member is below j. Let k be an arbitrary upper bound of Δ. If some b∈A fails b≤k, the admitted property λb[A(b)∧¬(b≤k)] has a least member b. Every a<b in A satisfies a≤k and a<j. Its increment is below k, and

    f(a)=a∨(f(a)∧¬a)≤k.

Thus k bounds the entire predecessor image at b. By the interval-to-ambient argument, b≤k, contradiction. This proves j=∨Δ, including when Δ is empty and j=⊥.

Finally the haecceity family needed in the reflection lemma is itself represented:

    H(K) := ∃d[Δ(d) ∧ K=(λz.z=d)].

It is a property of entities of type tt; BC_(tt) applies to it. Its join is not asserted to be a material union. Evaluation's right adjoint and positive Necessity of Identity, as proved in the original note, are the exact bridges used in the reflection argument.

## Current verdict

No failure of the canonical-chain argument, representedness, or supremum claim was found in this audit. The disjoint refinement needs BC_t only for the particular represented chain A; BC_(tt) supplies BC_t and the particular haecceity join. The proof remains a self-audited proposed theorem, not an independently checked result.
