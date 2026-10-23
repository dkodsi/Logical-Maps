# Relational Choice, countable completeness, and the countable chain condition

22 October 2026. New ordinary mathematical argument by OpenAI Codex, independently checked by the quotient-lane agent. No human check, Lean formalization, or database edit is claimed. This is a further consequence of the graph Bourbaki–Witt argument in `relational-choice-boolean-completeness-transversal-proof.md`, §5; it is not attributed to a published source.

## Exact statement

Fix a relational type τ and a counting type κ. All statements below are actual, unboxed, in the original language and fixed framework C.

* RC_(τ,τ): Relational Choice for relations whose input and output types are both τ.
* CBC_(κ,τ): every represented κ-countable family of τ-entities has an algebraic Boolean supremum.
* CCC_(κ,τ): every represented family of pairwise disjoint, nonbottom τ-entities is κ-countable.

Here κ-countable has the existing Frege-countability definition: a represented label relation L(x,n) with n in N_κ such that, for members x,y of the family, they share an N_κ-label if and only if x=y. A point can have more than one label; no single-valued choice of labels is assumed.

**Theorem.** Over C,

    RC_(τ,τ) + CBC_(κ,τ) + CCC_(κ,τ)  ⇒  BC_τ.

Consequently, with τ=σt, these premises imply Transversal Choice at σ by the separately proved BC_(σt)+RC_(σt,σt) theorem. This is type-local. No all-type CCC assumption is needed, and no necessity of distinctness, Actuality, BF, operation representing a chosen graph, or well-order on N_κ is used.

## 1. The cut and the strict progressive graph

Fix a represented family X of τ-entities. For a Boolean element b put

    P(b) := ∀u (UpperBound_X(u) → b≤u).

Bottom belongs to P. Any existing Boolean supremum of a represented family contained in P belongs to P: each upper bound u of X bounds the whole family, so its supremum is below u.

Suppose, for contradiction, that X has no supremum. Then no b in P is an upper bound of X, since such a b would be below every upper bound and hence be the supremum. For each b in P there is x in X with x≰b. The element c=b∨x belongs to P and satisfies b<c. Relational Choice gives an actual total single-valued graph f, taking each b in P to a strictly larger member of P; outside P use the input itself to make the relation on the whole type serial. The notation f(b) below denotes its unique graph value, not a represented operation.

## 2. The union of all f-chains needs no completeness premise

Call C⊆P an f-chain if the inherited Boolean order internally well-orders C and every a in C is the supremum within P of the represented image

    { f(b) : b∈C and b<a }.

This is a formula asserting the relevant supremum properties, not an assumption that every arbitrary family has a supremum. The singleton consisting of bottom is an f-chain. If a<b in an f-chain, then f(a)≤b.

The comparison argument in the cited §5 uses only these asserted supremum properties and their uniqueness as entities: any two f-chains agree on their common predecessor segment, and two least divergent elements would be suprema of coextensive predecessor images, hence equal. Thus the chains are comparable by initial segments. Their represented union

    A(a) := ∃C (C is an f-chain and Ca)

is internally well-ordered and is itself an f-chain. To see the least-element assertion, intersect a nonempty represented subproperty of A with one f-chain containing one of its members; its least member is least in the whole subproperty by initial-segment comparison. For a∈A, comparison makes its predecessor extension the same as in any f-chain containing a, so the defining supremum condition transfers. None of this invokes chain completeness, countable completeness, choice on predicate codes, external ordinals, or equality of coextensive predicate entities.

## 3. Disjoint increments make A countable

For a in A define the Boolean increment

    d_a := f(a)∧¬a.

It is nonbottom because a<f(a). Its graph is represented by existentially binding the unique f-value. If a<b in A, the f-chain property gives f(a)≤b, while d_b≤¬b. Consequently d_a∧d_b=0. Since A is a chain, distinct members have disjoint increments; since increments are nonzero, a↦d_a is injective.

The represented image D of these increments is therefore a pairwise disjoint nonbottom family. CCC gives a κ-countability label relation L_D(d,n) for D. Define

    L_A(a,n) := ∃c (f(a,c) ∧ L_D(c∧¬a,n)).

For a,b in A, functionality of f and the countability property of L_D show that a,b share a label exactly when d_a=d_b, and injectivity makes this equivalent to a=b. Thus A is κ-countable. This is direct composition of represented relations; it uses no selected enumeration, arithmetic recursion, or externally countable family.

## 4. The one required supremum supplies the contradiction

CBC gives an ambient Boolean supremum u of A. By §1, u∈P. It is also the supremum within P.

If u∉A, A has no greatest member. For each a∈A choose some b∈A with a<b; then f(a)≤b≤u. Conversely every upper bound of f[A] bounds A because a≤f(a). Hence u is the supremum of f[A]. Adjoining u at the end of A gives another f-chain, contrary to A's definition as the union of all such chains. Therefore u∈A.

But f(u)>u. For each a<u in A, f(a)≤u≤f(u), while f(u) itself is a member of f[A]. Thus f(u) is the greatest element of f[A], and adjoining f(u) at the end again gives an f-chain. Its membership in A contradicts u being an upper bound of A.

The supposition that X lacks a supremum is false. X was arbitrary, so BC_τ holds.

## Scope and provenance

The only completeness invocation in this proof is the supremum of the represented f-chain A, whose countability has already been established by its disjoint increments. This explains why CBC+CCC can replace the chain-completeness premise in the earlier local upgrade under Relational Choice. The result does not identify algebraic joins with arbitrary pointwise infinitary disjunctions.

Relevant local source conventions are `topics/classicism/background.md`, the Frege countability and Boolean-order definitions; `principles/relational-choice-r.yaml`; and `principles/countable-boolean-completeness-r.yaml`. The CCC definition also occurs in the concurrent infinity lane's `/tmp/classicism-research/frege-infinity-20261022-1726.md`, §10.3. If recorded later, this new proof's direct source is `misc`; source definitions and previously recorded theorems retain their own attribution.
