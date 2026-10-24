# The countable chain condition at a finite numerical index

Original scratch argument, OpenAI Codex, 22 October 2026. Framework C; all finiteness is internal Frege finiteness. No database edit, human check, Lean verification, or literature-novelty claim is made. If integrated, the direct source is `misc`.

## Statement

For any counting type κ and relational Boolean type τ,

    C + ¬I_κ + CCC_(κ,τ) ⊢ Fin_τ(top_(τt)) ⊢ Actuality.

Here CCC_(κ,τ) says that every represented family of pairwise disjoint nonbottom τ-entities is countable relative to N_κ, using the repository's labeling-relation definition. No Relational Choice, Boolean Completeness, Countable Boolean Completeness, ND, BF, or Plenitude is assumed.

The numerical input is the infinity lane's bare-C theorem that ¬I_κ implies internal finiteness of N_κ. See `frege-infinity-20261022-1726.md`, §§27–28. The following finite-bound argument is separate from that input.

## Finite-bound lemma

Let A be an internally finite represented property of a label type λ. For b in the Boolean algebra B_τ, write H(A,b) when every represented family J of pairwise disjoint nonzero elements below b has an admitted labeling relation L into A satisfying

    for all x,y in J:
      (there exists a in A with L(x,a) and L(y,a)) iff x=y.

Then H(A,b) implies internal finiteness of the principal ideal [0,b].

Prove this by Frege finite-set induction on A, uniformly in b. Equivalently, induct on its finite cardinality with the property that every set having that cardinality satisfies the displayed assertion. The induction uses actual relational graphs, never a conditional operation.

If A is empty and b is nonzero, the singleton family {b} has no required label. Thus H(A,b) forces b=0, and [0,b]={0} is finite.

For the successor step, let A'=A∪{a}, where a is outside A, and assume the result for A. Suppose H(A',b). If b=0 or b is an atom, its ideal has at most two members and is finite. Otherwise choose c with 0<c<b and put d=b∧¬c. Both c and d are nonzero and disjoint, and b=c∨d.

Take any disjoint nonzero family J below c. The family J∪{d} is disjoint and nonzero, so H(A',b) supplies a label relation L into A'. The reflexive case of the label condition supplies some label ℓ of d. No J-member uses ℓ, because each is different from d and labels cannot be shared between distinct members.

There is an admitted actual bijection graph from A'\{ℓ} onto A, given on that domain by

    Π(m,k) := (m=a ∧ k=ℓ) ∨ (m≠a ∧ k=m).

If ℓ=a, this is the identity on A. If ℓ≠a, then ℓ belongs to A, and the graph replaces the additional point a by the removed point ℓ. In either case it is total, single-valued, and injective on its indicated domain. Compose the restriction of L to J and A'\{ℓ} with Π. Every J-member retains a label, and the shared-label condition is preserved. Thus J has the required A-labeling.

As J was arbitrary, H(A,c) holds. The same argument, interchanging c and d, proves H(A,d). This does not select labels or labeling relations uniformly over all J; each use proves an existential statement inside a universal argument. The induction hypothesis gives finite ideals [0,c] and [0,d].

Every x≤b is the join of x∧c and x∧d. Hence [0,b] is the union, over u≤c, of the admitted finite images {u∨v:v≤d}. Frege induction proves closure under admitted functional images and finite unions, so [0,b] is finite. This completes the induction.

## Application and Actuality

Under ¬I_κ, the infinity-lane theorem makes N_κ an internally finite label property. CCC_(κ,τ) is exactly H(N_κ,top_τ). Apply the finite-bound lemma to conclude that the whole Boolean type B_τ is internally finite.

Its represented ideal Null_τ of relations with currently empty extension is a finite subset. Its finite Boolean join is still null: bottom is null, and a binary join of null relations is null. That join is the greatest null relation. The bare-C criterion in `quotient-abstraction-lane.md`, §18, then gives Actuality at this single relational type. No modal scope is changed in this reasoning.

## Evidence and audit

The extension lane independently checked the finite-set induction and the explicit label-compression graph. Its audit found no hidden Choice or graph-to-operation conversion. The inherited countability notation follows Goodsell, *Arithmetic is Necessary*, draft of 5 June 2024, Definition 6, p. 13, as transcribed in the repository's Background; this new theorem is not attributed to that paper. The finite-index numerical theorem and the null-ideal criterion are new research-lane arguments in the files and sections identified above.
