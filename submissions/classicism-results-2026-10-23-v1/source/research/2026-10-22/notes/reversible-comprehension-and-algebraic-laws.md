# Two optional simpler structural presentations

Scratch note, 22 October 2026. These are equivalent presentations of known principles, not additional independent axioms. Ordinary arguments over C; no record edits or Lean claim.

## 1. Plenitude needs only the representation of involutions

For a relational type A, call a relation R:A×A→t a **pairing** when it is total, single-valued, and symmetric:

    ∀a∃!b Rab,     ∀a,b(Rab→Rba).

Its components are singletons and two-element pairs. Pairing Representation says that every such R is represented by an operation f:A→A satisfying ∀a R(a,fa).

**Theorem.** The all-relational-type Pairing Representation schema is equivalent over C to Plenitude.

Plenitude immediately supplies the representing operation. Conversely let U:σ×τ→t be any total single-valued relation, with τ relational and σ arbitrary, including e. Set A=στt. Let H_(x,z):=λu,v(u=x∧v=z) be the injective pair code. The relational type τ has pointwise Boolean symmetric difference △ and zero 0_τ. Define a relation R on A as follows:

    R(H_(x,z), H_(x,z△y)) whenever Uxy;
    R(k,k) when k is not any pair code.

This is a native relation definition using existential quantifiers over x,z,y and the indicated identity tests. It is total and single-valued because U is, and it is symmetric because `(z△y)△y=z`. Pair-code injectivity prevents interference between different x or z. These are current graph properties; no unproved future uniqueness is required.

By Pairing Representation choose f:A→A. If Uxy, the graph property at H_(x,0_τ) gives the literal identity

    f(H_(x,0_τ))=H_(x,y).

Decode the output by the admitted lambda term

    h(x)[v̄] := ∃y(f(H_(x,0_τ))(x,y)∧y[v̄]).

The literal pair-code identity makes h(x)=y, by necessary evaluation and Intensionality. Therefore ∀x U(x,hx), proving Plenitude. No individual-valued operation is used, even when σ=e.

One may equivalently say that every total relational involution is realized by an operation. This reveals that failure of general unique-choice representation is already visible among the simplest reversible correspondences, consisting only of swaps and fixed points. It is stronger than merely realizing a prescribed finite list of swaps; finite interpolation is equivalent to ND, while the present unrestricted matching schema is Plenitude.

## 2. Barcan is persistence of a single elementary algebraic law

For relational A define the pointwise predicate

    Idem(f) := ∀x^A f(fx)=fx.

**Theorem.** The schema `∀f^(AA)(Idem(f)→□Idem(f))`, at all relational A, is equivalent over C to BF_rel. It suffices in the reverse direction to use A=tσ for each relational σ.

BF_A proves the forward persistence: every current equation f(fx)=fx is necessary by NI, and BF_A boxes the universal quantifier.

Conversely fix relational σ and P:σ→t with ∀q□Pq. Write A=tσ, and for H:A define F(H):A by

    (FH)(r) := H(r) △ [(r=⊤ ∧ ¬P(H⊥)) · ⊤_σ].

The product with top_σ means the constant σ-entity whose every trailing instance has the displayed propositional value. Boolean operations on σ are pointwise. At every future point F preserves the bottom slot, and toggles the top slot by the same coefficient each time. Thus `F∘F=id_A` is a C-provable operation identity, using only Boolean symmetric-difference identities and ⊥≠⊤.

For each current H, the premise □P(H⊥) makes the toggle identically zero; hence FH=H. F is therefore actually idempotent. Assumed persistence of idempotence gives □∀H F(FH)=FH. Combining this with F²=id gives □∀H FH=H.

At any future point and any q:σ there, take the two-slot H with H⊥=q and H⊤=0_σ. Evaluating FH=H at top gives `(¬Pq)·⊤_σ=0_σ`. Evaluate at any tuple of trailing arguments (or directly when σ=t) to conclude Pq. Therefore □∀qPq, which is BF_σ.

The dual presentation using persistence of **involutivity**, `∀x f(fx)=x`, is also equivalent to BF_rel. For the reverse use the idempotent mask

    (FH)(r)[v̄] := H(r)[v̄] ∧ (r=⊤→P(H⊥)).

This mask is always idempotent and actually identity under ∀q□Pq. If its actual involutivity persists, idempotence and involutivity force it necessarily identity; the same top-slot argument yields BF_σ.

Thus familiar algebraic laws can fail on newly available inputs even though each old input continues to satisfy its equation. Barcan is exactly what rules out that phenomenon, and a single law—idempotence or involutivity—already detects the full relational schema. This complements the surjectivity-persistence characterization, rather than introducing a separate strengthening.
