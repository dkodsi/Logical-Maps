# Coextension codes and the Actuality boundary

Original mathematical argument, direct source misc; unpaginated.

## 1. Coextension-class coding has a literal left inverse

Let τ = σ₁…σₖt be any admitted relational type, including τ=t when k=0. Write A≈B for actual pointwise coextension, with the displayed tuple of variables universally closed. Define admitted operations

    c_τ(A)(B) := B≈A,                  c_τ : τ → (τt),

    d_τ(Z)(x̄) := ∃B^τ(ZB ∧ Bx̄),      d_τ : (τt) → τ.

There is no arrow ending in e. For k=0 the latter formula is ∃B^t(ZB ∧ B).

**Lemma. C proves d_τ(c_τ(A))=A as an entity identity.**

Expand the left-hand side at x̄:

    ∃B[(∀ȳ(Bȳ↔Aȳ)) ∧ Bx̄].

This is H-theorematically equivalent to Ax̄. Left to right, instantiate the universal equivalence at x̄. Right to left, use B=A. The equivalence is unconditional, with A and x̄ free; it does not depend on an optional extensionality premise. C's Logical Equivalence therefore identifies the abstractions. At the nullary propositional type, the corresponding identity follows from the same unconditional equivalence and C's propositional intensionality. QED.

Consequently c_τ is injective on entities. It also preserves and reflects actual coextension:

    c_τ(A)≈c_τ(B)  iff  A≈B.

Preservation uses transitivity of actual coextension. For reflection, evaluate the equivalence of the two class predicates at A, using A≈A. The union operation d_τ preserves actual coextension of its input families, by its displayed existential definition.

Thus a coextension-class predicate represents a quotient class in its **actual extension**, while its entity still retains all the intensional information of the original code. These statements are compatible: the source of the distinction is precisely actual coextension versus identity.

## 2. Finite towers preserve entire ambiguity ranges

Define externally, for any fixed natural number n, the finite type sequence τ₀=τ and τᵢ₊₁=τᵢt. Compose the preceding operations to obtain admitted terms

    C_n : τ → τ_n,       D_n : τ_n → τ.

The types and finite terms are specified in the metalanguage; no object-language type quantifier or infinite composition is introduced. Repeated substitution in §1 gives

    D_n(C_n(A))=A.

Both composites preserve actual coextension, and C_n reflects it. Functionality is not assumed to infer equality of arbitrary operations; the needed displayed equalities are equations of these specified terms at their arguments.

Let U(A,a) be any actually serial relation from τ to a type σ, possibly σ=e. A total functional graph K contained in U lifts to

    U_n(Z,a) := U(D_n(Z),a),
    J(Z,a)   := K(D_n(Z),a).

J is an actual total functional subrelation of U_n. Its pullback through C_n is exactly K, by the literal left-inverse identity. Conversely, pulling any selector of U_n back through C_n gives a selector of U. Thus arbitrary original selectors can survive any fixed finite number of these higher-type recodings.

There is an exact strengthening. Define the ambiguity across all codes in a coextension class by

    Amb_K(A,a) := ∃B(B≈A ∧ K(B,a)).

For the lifted J above, C proves

    Amb_J(C_n(A),a)  iff  Amb_K(A,a).                 (1)

For the forward direction, a witness Z≈C_n(A) gives D_n(Z)≈D_n(C_n(A))=A, and J(Z,a) is K(D_n(Z),a). For the reverse direction, take a witness B≈A and use Z=C_n(B); then Z≈C_n(A) and J(Z,a) is K(B,a). This checks the whole high-level coextension fibre, not merely the coded image or one diagonal value.

Apply this to τ=θ, the type of batch-history graphs, and to a padded missed-point relation U. A chooser with infinite ambiguity in a missed R-cell can be lifted to a higher class-code level with **exactly the same ambiguity**. Replacing the input by its class predicate, even repeatedly, imposes no improvement on an arbitrary RC witness.

This is a mechanism-specific limitation. It does not show that every carefully designed higher-type relation or selector is useless. It establishes that these recodings alone do not force the desired finite ambiguity, since every old bad chooser has a bad lifted realization.

## 3. Internal orbit averaging identifies its whole internal orbit

Generalize the operation in `continuation-obstructions.md`, §1, from unary property type σt to any relational type τ above. For an admitted operation g:τ→τ put

    Closed_g(P) := ∀C^τ(PC ↔ P(gC)),

    O_g(A,B) := ∀P^(τt)[(PA ∧ Closed_g(P)) → PB],

    J_g(A)(x̄) := ∃B^τ(O_g(A,B) ∧ Bx̄).

The completed averaging argument proves, unconditionally in C,

    J_g(gA)=J_g(A).                                  (2)

Its proof is H-theoretical: any Closed_g(P) has PA↔P(gA), so the definitions of O_g(A,−) and O_g(gA,−) are unconditionally equivalent. No actual premise about g is used to obtain the entity identity.

**Lemma. O_g(A,B) implies J_g(A)=J_g(B).**

Consider the admitted predicate H_A(C):=(J_g(C)=J_g(A)). It contains A by reflexivity. Identity (2) gives H_A(C)↔H_A(gC), so H_A is actually Closed_g. Instantiate O_g(A,B) with H_A to obtain J_g(B)=J_g(A). Symmetry gives the stated order. The optional orbit premise is used by ordinary instantiation, not by an illicit invocation of Logical Equivalence.

If g preserves every actual extension,

    ∀A(gA≈A),                                        (3)

then O_g(A,B) implies A≈B and J_g(A)≈A. Indeed, the predicate C≈A is g-biinvariant by (3), contains A, and therefore contains every O_g(A,−)-member. O_g(A,A) holds, so its material union has exactly A's extension. This is the argument of the earlier averaging lemma, applied at τ.

## 4. Exhausting coextension classes by an internal generator is exactly Actuality

**Theorem. At any fixed relational τ, over C with the standing nonempty argument domains, Actuality is equivalent to existence of g:τ→τ such that**

    ∀A(gA≈A),
    ∀A B(A≈B → O_g(A,B)).                            (4)

Under the first clause the reverse implication O_g(A,B)→A≈B already holds. Thus (4) says that the internally generated bidirectional orbit relation is exactly actual coextension. No equality with an externally finite-step orbit is assumed.

**Forward from (4) to Actuality.** By §3, J_g(A)≈A. If A≈B, the second clause of (4) and the orbit-identification lemma give J_g(A)=J_g(B). Hence J_g is an operation-valued extensional canonicalizer of τ.

For completeness, the reduction of such a canonicalizer j to Actuality uses only constant relations and NI. For a proposition p let A_p(x̄):=p. Standing nonemptiness of the argument sorts gives A_p≈A_q iff p↔q; the nullary case has the same conclusion directly. Let

    T(p) := (j(A_p)=j(A_⊤)).

Extension preservation and canonicalization give T(p)↔p actually. Necessity of Identity makes every true T(p) necessary. Put a:=∀p(T(p)→p); it is actually true. For every actually true p, □T(p), while the necessary universal-instantiation theorem gives □(a→(T(p)→p)). Hence □(a→p). Thus a entails every actual truth and witnesses Actuality. No optional hypothesis was necessitated.

**Converse.** Let u witness Actuality. Define k(A)(x̄):=u∧Ax̄. It preserves actual extension. If A≈B, Actuality applied to that actual equivalence gives the guarded necessary pointwise equivalence, so k(A)=k(B). This is the established operation-canonicalizer construction in `research/2026-10-22/notes/quotient-abstraction-lane.md`, §1.

Take g=k. If A≈B and P is g-biinvariant, then

    PA ↔ P(gA) ↔ P(gB) ↔ PB,

where the middle equivalence uses the entity equality gA=gB. Therefore every invariant P containing A contains B, exactly O_g(A,B). This proves (4). QED.

The same implication to Actuality holds for any fixed finite list of admitted extension-preserving generators whose joint internal invariant closure exhausts each coextension class. Replace Closed_g by a finite conjunction, use the unconditional identity along each displayed generator, and repeat the predicate H_A argument. The single-generator converse already suffices for an equivalence.

## 5. Consequence for the current RC route

The orbit averaging operation supplies useful coherence along any specified admitted extension-preserving generator. It cannot be promoted to a global operation normalizer of all coextensive codes from RC alone: the exact global generation hypothesis above already implies Actuality. The recorded RC-and-not-Actuality examples therefore block that attempted general implication. This is stronger information about the proposed mechanism than merely observing that the averaging proof has an unproved hypothesis.

This does not settle RC to TC. TC asks for a relational or property-based transversal, and the completed finite-cell batching criterion is weaker than an operation canonicalizing every code. A useful next construction must exploit that weaker requirement. The operation barrier does not establish impossibility of a coherent **relational** choice graph, or of a more local construction on selected history fibres.
