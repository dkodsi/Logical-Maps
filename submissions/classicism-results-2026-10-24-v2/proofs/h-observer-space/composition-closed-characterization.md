# Pointwise separation as separation by a monoid of material observers

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated.

For any finite preservation signature, pointwise identity can be replaced by an algebraic condition on the observer family: its members preserve the operations materially, it separates propositions, and it is closed under composition. The family may also be required to contain identity. Thus a condition on how observations combine exactly recovers identities of outputs. Full relational separation then recovers identities of the whole operations.

## 1. Signature, family and qualification

Fix a finite external signature Σ of preservation clauses chosen from M,V,N,Qσ,Pσ at specified types. One may also list fixed proposition constants c. Preserve the fixed H language and the usual Top/Bottom abbreviations. No C, modal rule, Choice, Functionality or finiteness premise is assumed.

For example the material and pointwise M clauses are respectively

```math
\begin{aligned}\forall p,q\,[E(p\land q)&\leftrightarrow(Ep\land Eq)],\\\forall p,q\,[E(p\land q)&=(Ep\land Eq)]\end{aligned}
```

The analogous clauses use the other Boolean truth operations or the listed quantifiers. A fixed-constant clause is E(c)↔c materially, and E(c)=c pointwise. The constant may be a fixed parameter of the instance. MatΣ(E) and PtΣ(E) are the finite conjunctions of the corresponding clauses.

An observer family is an admitted predicate X:(tt)t. Its membership is ordinary truth X(E). Define

```math
\begin{aligned}I&:=\lambda p.p,&F\circ E&:=\lambda p.F(Ep),\\
\mathrm{Closed}(X)&:=\forall E,F\,[(X(E)\land X(F))\to X(F\circ E)],\\
\mathrm{Monoid}(X)&:=X(I)\land\mathrm{Closed}(X),\\
\mathrm{Material}_\Sigma(X)&:=\forall E\,[X(E)\to\mathrm{Mat}_\Sigma(E)],\\
\mathrm{Sep}(X)&:=\forall p,q\,[p=q\leftrightarrow\forall E\,(X(E)\to(Ep\leftrightarrow Eq))]\end{aligned}
```

All these formulas and the predicate λE.PtΣ(E) are admitted lambda terms. There is no external quantification over arbitrary sets of observers, and no object-language quantification over types.

## 2. Exact propositional characterization

**Theorem.** Over H,

```math
\begin{aligned}S[\mathrm{Pt}_\Sigma]
&\leftrightarrow\exists X\,[\mathrm{Sep}(X)\land\mathrm{Closed}(X)\land\mathrm{Material}_\Sigma(X)]\\
&\leftrightarrow\exists X\,[\mathrm{Sep}(X)\land\mathrm{Monoid}(X)\land\mathrm{Material}_\Sigma(X)]\end{aligned}
```

### From pointwise identities to a material monoid

Take the admitted predicate X(E):=PtΣ(E). Identity belongs to X, by conversion and reflexivity. Each pointwise clause implies its material version by substitution and H's truth rules.

Pointwise preservation is closed under composition. For conjunction, if E and F have the pointwise law then

```math
F(E(p\land q))=F(Ep\land Eq)=F(Ep)\land F(Eq)
```

Negation, disjunction and constants are the same equality-substitution argument. For a universal clause,

```math
F(E(\forall x\,Gx))=F(\forall x\,E(Gx))=\forall x\,F(E(Gx))
```

The family λx.E(Gx) is admitted. The existential case is dual. These are equalities of outputs; no conditional equivalence is abstracted into a whole-operation identity. Thus X is a monoid of material observers. Its separation is the assumed S[PtΣ].

### From a composition-closed material family to pointwise identities

Assume Sep(X), Closed(X) and MaterialΣ(X). Fix E with X(E). We prove that E has every pointwise law.

For conjunction, compare E(p∧q) and Ep∧Eq using any F with X(F). Closure puts F∘E in X, so its material M law gives

```math
F(E(p\land q))\leftrightarrow(F(Ep)\land F(Eq))
```

The material M law for F gives

```math
F(Ep\land Eq)\leftrightarrow(F(Ep)\land F(Eq))
```

Therefore all X-observers agree on the two proposed outputs. Sep(X) identifies them. The same argument replaces conjunction by disjunction or negation.

For a universal quantifier, the material Qσ laws for F∘E and F yield respectively

```math
\begin{aligned}F(E(\forall x\,Gx))&\leftrightarrow\forall x\,F(E(Gx)),\\F(\forall x\,E(Gx))&\leftrightarrow\forall x\,F(E(Gx))\end{aligned}
```

Again Sep(X) yields E(∀x Gx)=∀x E(Gx). The existential proof is identical with ∃. No Barcan inference is involved: both sides are compared using the same admitted family and ordinary H truth conditions.

For a listed constant c, material fixedness for F∘E and F gives F(Ec)↔c and Fc↔c. Hence separation gives Ec=c.

We have shown that **every X-member is PtΣ**. Separation by X therefore implies separation by the larger class of all PtΣ observers. This proves the first converse. A monoid is composition-closed, so the same proof applies to the third assertion. The first direction already produced a monoid, proving all equivalences. ∎

## 3. Fixed endpoints versus endpoint truth conditions

If Σ lists Top or Bottom as a fixed constant, the right-hand material family condition says respectively that every member accepts Top or rejects Bottom. Composition closure plus separation upgrades that condition to actual fixing of the corresponding endpoint by every family member.

Thus, for example,

```math
\begin{aligned}&S[\mathrm{Pt}_\Sigma\land E\top=\top\land E\bot=\bot]\\
&\quad\leftrightarrow\exists X\,[\mathrm{Sep}(X)\land\mathrm{Monoid}(X)\land
\forall E\,(X(E)\to(\mathrm{Mat}_\Sigma(E)\land A(E)\land Z(E)))]\end{aligned}
```

This is an exact bridge from truth conditions on a **closed separating family** to endpoint fixing. It does not say that the entire A,Z-qualified pointwise class is composition-closed: a map accepting Top can send it to a different true proposition which another map rejects. Nor does the theorem identify ordinary S[A Z PtΣ] with the displayed fixed-endpoint principle.

The family X is existentially quantified. Requiring the entire material-qualified class to be closed is a different, generally stronger condition. The theorem needs only one admitted closed family that separates.

## 4. Full relational scope and whole-operation identities

For a fixed relational type ρ, Sep_ρ(X) means separation by X of values after every admitted argument tuple. The same X must be used in the following statement for that instance.

For any ρ, over H,

```math
\begin{aligned}&S_t[\mathrm{Pt}_\Sigma]+S_\rho[\mathrm{Pt}_\Sigma]\\
&\quad\leftrightarrow\exists X\,[\mathrm{Sep}_t(X)\land\mathrm{Sep}_\rho(X)\land\mathrm{Monoid}(X)\land\mathrm{Material}_\Sigma(X)]\end{aligned}
```

Forward use X=PtΣ. Reverse the propositional instance makes every X-member pointwise preserving by §2, and enlarging the class gives the ρ-instance too. No Functionality is needed for this paired statement.

For full relational separation, avoid quantifying over a schema in the object language. Use the schema, indexed externally by ρ, asserting the existence of such an X separating both t and ρ. The displayed equivalence gives exactly FullSep[PtΣ]. This is also equivalent to FullSep[OpΣ], where OpΣ asserts equality of the whole composite operations: FullSep supplies Functionality, which lifts each pointwise clause to its operation identity.

One may equivalently use the separate existence formula of §2 together with the full Functionality schema. The [typed factorization theorem](typed-separation-and-classicism.md), §2, then upgrades propositional separation to every relation type. In either presentation no single object-language infinitary conjunction of all type instances is introduced.

At propositional scope, the full-operation version requires the appropriate local Functionality instances: two binary stages for M,V, the unary stage for N, and Fun(σt,t) for Qσ/Pσ. Fixed-constant output equations need no lifting. Without those premises, the exact unconditional theorem is about pointwise identity.

## 5. Relation to the tier distinctions

The theorem applies equally to a one-operation signature and a mixed finite signature. It uses the same observer family for all listed clauses; separately closed separating families for different operations do not automatically combine.

The [four-proposition negation model](relational-clone-model.md) has material negation separation but lacks pointwise negation separation. The theorem therefore proves that it has no admitted composition-closed separating family of material negation observers, despite its many material observers and all Functionality instances.

The [finite semilattice normalization](finite-semilattice-normalization.md) supplies pointwise M or V separators under internal finiteness, and hence supplies the closed families of this theorem in those cases. It does not prove the entire original material class composition-closed.

This characterization changes the form of the general admission question: an arbitrary separating material family must be replaceable by one stable under composition to recover pointwise identities. It does not settle whether such a replacement always exists for conjunction or disjunction in the remaining infinite nonprincipal case.

## 6. Sources

The direct source is this original argument, `misc`, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, §§2–5, unpaginated. The testing argument generalizes the composition-closed-core proof in [Quantifier-generated lattices](quantifier-generated-lattices.md), §3. The full typed lifting uses the linked [typed separation theorem](typed-separation-and-classicism.md). The language and H rule discipline are unchanged. No active database records, generated state or Lean files are changed.
