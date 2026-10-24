# Unary signatures: exact finite-world atom counts under Strong Possibility

22 October 2026. Original consequence of the audited profile construction, developed by an OpenAI Codex audit agent. Ordinary mathematics, not human checked or Lean formalized; no literature-novelty claim. No database edits.

## 1. Statement

Fix a finite relational-only signature Σ consisting of r unary individual predicates c₁,…,c_r:et and s propositional constants b₁,…,b_s:t. Put q=2^r. For each positive external integer m, write A_m:=F∧E_m, as in the profile construction.

**Theorem.** Strong Possibility for this exact signature Σ forces the Boolean interval below A_m to have exactly

    2^s · q · binomial(m+q−2, q−1)

atoms. For r=1,s=0 this is **2m**. For r=s=0 the expression is 1 and recovers pure Strong Possibility's Atom(A_m).

This is an ordinary finite-cardinality theorem schema, one formula for each fixed m,r,s. It is not an infinitary counting axiom. The metalinguistic Strong Possibility consistency condition continues to use Max(C(Σ)), with the fixed original finitary C.

## 2. The finite pointed diagrams

The q colors are the finite Boolean combinations

    C_ε(x) := ⋀_(i=1)^r (c_i(x) if ε_i=1, otherwise ¬c_i(x)),

with the empty combination top when r=0. They partition the individuals in every model.

Let n=(n₁,…,n_q) be any tuple of nonnegative external integers summing to m, and let j satisfy n_j>0. Let β be any assignment of truth values to the s propositional constants. Define the closed Σ-sentence D_(n,β) by conjoining:

- A_m;
- the assertion that exactly n_i individuals have color C_i, for every i;
- the s literals specifying the values β of the propositional constants.

For one free individual variable z define

    Δ_(n,j,β)(z) := D_(n,β) ∧ C_j(z).

Each Δ is C(Σ)-consistent: take a full extensional m-individual model, give its individuals the required color multiplicities, give z one of the n_j individuals in its designated color, and interpret the propositional constants by β.

At any pointed model satisfying Δ, F and E_m force the full finite extensional hierarchy, by the original profile audit. Two such pointed Σ-structures are isomorphic: match the color classes by arbitrary bijections, requiring the designated j-colored individual to map to the designated individual, and extend recursively through all types. The specified propositional constants agree. Thus every Σ-proposition term T(z), with z its only possible free variable, has the same truth value at all Δ-points.

The marker condition is essential. The closed D_(n,β) alone may have several individual orbits when several n_i are positive. It need not be pointed-complete and need not itself be an atom under signature Max. The Δ formulas explicitly resolve this issue.

## 3. One profile root verifies all atomhood assertions

Use the singleton profile-root construction with Σ-term profiles T(z) and components complete for C(Σ). Every constant has its own term profile; the root individual's profile is z. Arbitrary root actual extensions and the audited closure argument give a C(Σ)-model of signature Maximalism.

For its sole root individual a and any root proposition p, pointed uniformity on Δ-points shows that the profile of p∧Δ(a) is either bottom or the profile of Δ(a). The actual root proposition domain is infinite, so F is false and Δ(a) has actual truth bit zero. Thus p∧Δ(a) is literally bottom or Δ(a), and consistency supplies a nonbottom component witness. Hence Atom(Δ(a)).

There is only one root individual, so for every diagram index the sentence

    U_(n,j,β) := ∀z Atom_t(Δ_(n,j,β)(z))

holds. It is therefore consistent with Max(C(Σ)). The same root verifies all these sentences, for all positive m, simultaneously. Its proposition profiles remain countable, so the previous internal-countability witness remains available.

## 4. Strong Possibility makes the atoms actual

Each U is a universally quantified finite Boolean combination of typed identities, after expanding Boolean order in Atom. The universal-identity reflection argument works for Σ-formulas just as for pure formulas:

    C(Σ) ⊢ ◇ne U→U.

Signature Strong Possibility applies because Section 3 verified Max(C(Σ))+U consistency. Hence it proves every U.

For any actual individual a, the Δ_(n,j,β)(a), over all displayed indices, form a finite pairwise-disjoint partition of A_m. This is a C theorem: at a Fregean m-individual point, the q colors have one uniquely determined count vector, a has one of its positive colors, and the s propositions have one truth assignment. The corresponding material equivalence and incompatibilities are C-theorems, so their necessitation and Intensionality give the Boolean identities

    A_m = ⋁_(n,j,β) Δ_(n,j,β)(a),
    Δ_i(a)∧Δ_j(a)=bottom        for i≠j.

Every part is an atom by the preceding paragraph. Every nonzero atom below their finite join equals one of them, by finite distributivity and atomhood. Therefore the number of atoms below A_m is exactly the number of diagram indices. This argument needs only the standing nonemptiness of the individual type; it does not silently assume an extra individual name in Σ.

## 5. Counting the indices

For a fixed selected color j, subtract one from n_j. The resulting tuple is a weak composition of m−1 into q parts. There are

    binomial(m+q−2,q−1)

such tuples. There are q choices for j and 2^s choices for β. Multiplying gives the claimed number.

For one unary predicate c and no proposition constants, write D_r for A_m together with “exactly r individuals satisfy c.” The atoms are exactly

    D_r∧c(a),      1≤r≤m,
    D_r∧¬c(a),     0≤r≤m−1.

There are m atoms of each displayed kind. When m=2 the two closed extreme diagrams D_0,D_2 are atoms, while D_1 splits into its c(a) and ¬c(a) atoms. When m=1 the answer is 2, matching the earlier singleton finite-signature theorem.

## 6. Scope

The theorem concerns the exact finite signature specified above, with no individual constants and no additional unlisted relation symbols. Additional parameters can refine the profile diagrams and alter the count. A signature with individual constants has a different root/profile construction and requires its own count.

The result is a consequence of signature Strong Possibility if that theory is consistent; it does not establish its consistency. The profile root verifies the simultaneous atomhood sentences with signature Max, but its arbitrary actual truth bit still supplies Actuality and distinctness-preserving collapse, so it is not itself a Strong Possibility model.

For more general finite signatures, finite structures and pointed automorphism orbits suggest an analogous count. No general counting formula or universal orbit theorem is claimed here without checking the relevant complete diagrams and their type scopes.
