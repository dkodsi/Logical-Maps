# Zorn selects global transversals from local support

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§2–5, unpaginated. The pre-existing Boolean Completeness and Zorn premises are identified in §1.

The local-transversal support of a logical observer gives an exact test for a qualified left inverse once Boolean Completeness at t and Zorn at t are added to C5. The test also controls the inverse's kernel: it determines whether an inverse can send a prescribed proposition to Bottom. Neither a finite generating family nor an atomicity premise is required.

The two additional principles have different jobs. Boolean Completeness supplies actual upper bounds for the current members of an admitted chain. Zorn selects a maximal local transversal. Treating the weighted formula ∃b(Xb∧b) as the join of X's current extension would not justify this argument.

## 1. Exact premises and the support

Work over C5, with the two additional unboxed instances

```math
\mathrm{BC}_t,
\qquad \mathrm{Zorn}_t.
\tag{1}
```

$`\mathrm{BC}_t`$ is [Boolean Completeness at t](../../source/topics/classicism/principles/boolean-completeness-t.yaml), in its equivalent least-upper-bound form: every admitted predicate X:tt has a proposition u such that, for every q,

```math
u\le q\quad\longleftrightarrow\quad
\forall b\,(Xb\to b\le q).
\tag{2}
```

Membership Xb in (2) means current truth. It need not be an endpoint-valued predicate. The order is p≤q iff p∧q=p.

$`\mathrm{Zorn}_t`$ is the single σ=t instance of the database's [preorder Zorn principle](../../source/topics/classicism/principles/zorn-r.yaml):

```math
\begin{aligned}
\forall P^{ttt}\bigl[&\mathrm{Preorder}(P)\land
\forall X^{tt}\bigl(\mathrm{TotalOrder}(P,X)
 \to\exists u^t\,\forall b^t(Xb\to P(b,u))\bigr)\\
&\to\exists m^t\,\forall y^t(P(m,y)\to P(y,m))\bigr].
\end{aligned}
\tag{3}
```

TotalOrder includes actual antisymmetry on the current X-members, exactly as in that record. The proof below gives upper bounds even for comparable current families. No all-type Zorn schema, Functional Choice, Actuality or necessitation of (1) is assumed.

Fix a finite external list Δ containing t and an admitted $`\mathrm{Good}_\Delta`$ observer E. Initially E need not be injective. Good retains all whole Boolean and listed quantifier identities. Its canonical adjoints satisfy L⊣E⊣R. Write

```math
C_E:=EL,\qquad j_E:=ER,
\qquad
\mathrm{Loc}_E(b):\longleftrightarrow
\forall q\,[b\land C_E(b\land q)=b\land q].
\tag{4}
```

As in [Local-transversal support](local-transversal-support.md), §1, the locality guard may be defined by equality of the two complete unary operations in (4). It is endpoint-valued under C5. The admitted support is

```math
s_E:=\exists b\,[\mathrm{Loc}_E(b)\land b].
\tag{5}
```

We use the support note's heredity and density theorem: every local b lies below $`s_E`$, and every nonzero q≤$`s_E`$ contains a nonzero local subproposition. The adjoint facts include $`q\le C_E q`$, L0=0 and Frobenius

```math
L(q\land Ep)=Lq\land p.
\tag{6}
```

All operators and predicates used below are admitted terms in E and the displayed parameters.

## 2. Actual current joins of compatible local elements

We first justify the chain-bound step for arbitrary proposition-valued membership predicates. The stronger $`\mathrm{BC}_t`$ premise is used here, not hidden in the notation for an existential quantifier.

Composition of the two adjunctions gives

```math
C_E\dashv j_E.
\tag{7}
```

Indeed $`C_E q\le p`$ iff Lq≤Rp iff q≤E(Rp). Therefore $`C_E`$ preserves any existing least upper bound of a current admitted family. This assertion follows directly from the universal property: $`C_E u\le z`$ iff u≤j_Ez iff every current family member b satisfies b≤j_Ez iff every $`C_E b\le z`$. The image family is admitted by the predicate $`\exists b(Xb\land y=C_E b)`$.

Likewise meet with a fixed q preserves every existing current least upper bound, because x∧q≤z iff x≤¬q∨z. This uses Boolean residuation, not a truth assumption about the membership predicate. $`\mathrm{BC}_t`$ supplies the image joins whenever needed.

**Compatible-current-join lemma.** Let X:tt be admitted. Suppose its current members are local, and any two current members b,c have local union b∨c. If u is their $`\mathrm{BC}_t`$ least upper bound, then u is local.

To prove this, fix q. For any current members b,c, locality of b∨c yields

```math
b\land C_E(c\land q)\le q.
\tag{8}
```

Hold b fixed. The join-preservation facts show that $`b\land C_E(u\land q)`$ is the least upper bound of the values $`b\land C_E(c\land q)`$ for current c. Hence it is at most q. Now vary b: $`u\land C_E(u\land q)`$ is the least upper bound of these $`b\land C_E(u\land q)`$, so it too is at most q. It is also at most u. The adjunction unit supplies the reverse inequality $`u\land q\le u\land C_E(u\land q)`$, proving locality. An empty family has u=0 and satisfies the same conclusion.

In particular this applies to a current chain of local elements: the union of two comparable members is the larger, hence local. No claim that X itself, or its chain property, persists is used.

## 3. A maximal local transversal fills exactly the available support

**Theorem 1.** For every proposition r, there exists an admitted local u≤r such that

```math
\boxed{Lu=L(s_E\land r).}
\tag{9}
```

Every maximal local element below r satisfies (9). This theorem holds for arbitrary Good E; injectivity is not needed.

**Proof.** On all propositions define

```math
V(b):=\mathrm{Loc}_E(b)\land b\le r,
\qquad
P(b,c):=\neg V(b)\lor(V(c)\land b\le c).
\tag{10}
```

Zero is valid. P is a preorder: invalid elements lie below everything, while valid elements are ordered by ≤ and are never below invalid elements.

Let X be an admitted current P-chain. Apply $`\mathrm{BC}_t`$ to the admitted predicate Y(b):=Xb∧V(b). Its least upper bound u lies below r, since every current Y-member does. Those members are comparable under ≤, so §2 makes u local. Thus Vu. Invalid X-members are automatically P-below u; valid ones belong to Y and are ≤u. This proves the exact upper-bound premise of (3), including empty chains and chains containing no valid member.

$`\mathrm{Zorn}_t`$ supplies a maximal element u. It is valid: if not, P(u,0) and maximality would give P(0,u), contradicting validity of 0 and invalidity of u. Its maximality is therefore ordinary maximality among local elements below r.

Put a=L($`s_E`$∧r). Since u is local and u≤r, u≤$`s_E`$∧r and Lu≤a. Suppose

```math
w:=a\land\neg Lu\ne0,
\qquad x:=(s_E\land r)\land Ew.
\tag{11}
```

Frobenius gives Lx=a∧w=w, so x≠0. Since x≤$`s_E`$, the support-density theorem supplies a nonzero local v≤x. In particular v≤r and Lv≤w. Hence

```math
C_Ev\le Ew,
\qquad C_Eu=E(Lu)\le E(\neg w),
\qquad C_Eu\land C_Ev=0.
\tag{12}
```

The two local elements u,v have disjoint image ceilings. The finite cross-term expansion therefore gives locality of u∨v: its diagonal terms are u∧q and v∧q, while $`u\land C_E(v\land q)`$ and $`v\land C_E(u\land q)`$ are zero by (12). Also u∧v=0 because each lies below its ceiling. Thus u∨v is a valid strict extension of u, contrary to maximality. So w=0 and Lu=a, proving (9). ∎

The domain part a=L($`s_E`$∧r) is canonical, even though a selected maximal u need not be unique. The relative maps p↦u∧Ep and q↦Lq give an admitted logical isomorphism between [0,a] and [0,u]. This is the local interval theorem, with Lu=a; it does not introduce an interval type or assert a uniform choice of u as r or E varies.

## 4. Exact qualified-inverse and kernel criteria

Now assume E is injective. The [Boolean-transversal theorem](injective-observers-and-boolean-transversals.md), §§2–3, identifies its qualified left inverses with local u satisfying $`C_E u=1`$. Injectivity makes this last condition equivalent to Lu=1.

Theorem 1 therefore gives, for every r,

```math
\boxed{
\exists u\,[\mathrm{Loc}_E(u)\land u\le r\land C_Eu=1]
\quad\longleftrightarrow\quad L(s_E\land r)=1.}
\tag{13}
```

Necessity does not need $`\mathrm{BC}_t`$ or $`\mathrm{Zorn}_t`$: any such u lies below $`s_E`$∧r, and Lu=1. Sufficiency is exactly (9).

For a global transversal u the corresponding $`\mathrm{Good}_\Delta`$ inverse is the admitted term

```math
F_u(q):=L(u\land q),
\qquad F_uE=I,
\qquad F_uq=0\longleftrightarrow u\land q=0.
\tag{14}
```

The equalities of operations here are whole identities. The established transversal theorem checks every Boolean and listed quantifier law and proves that every qualified left inverse arises in this way. Taking r=1 or r=¬c in (13) yields the exact tests

```math
\boxed{
\begin{aligned}
\exists F\,[\mathrm{Good}_\Delta(F)\land FE=I]
&\quad\longleftrightarrow\quad Ls_E=1,\\
\exists F\,[\mathrm{Good}_\Delta(F)\land FE=I\land Fc=0]
&\quad\longleftrightarrow\quad L(s_E\land\neg c)=1.
\end{aligned}}
\tag{15}
```

The displayed c is arbitrary; it need not be true for this individual-observer theorem. No inverse parameter occurs on the right.

In particular, an injective observer with $`s_E=1`$ has a qualified left inverse under the present premises. If also Rc=0, then L¬c=¬Rc=1, and (15) supplies an inverse killing that same c. Full support alone is not silently substituted for injectivity. Nor is it claimed to yield an inverse over C5 without the additional admission premises.

## 5. The J/K comparison and exact limits

Under C5+$`\mathrm{BC}_t`$+$`\mathrm{Zorn}_t`$, the true-kernel sentence K_Δ has the following one-observer form:

```math
\boxed{
K_\Delta\quad\longleftrightarrow\quad
\exists E,c\,[\mathrm{Good}_\Delta(E)\land\mathrm{Inj}(E)
\land c\land L_E(s_E\land\neg c)=1].}
\tag{16}
```

This follows directly from (15). The right side already implies the J condition Rc=0, since L($`s_E`$∧¬c)≤L¬c=¬Rc. Conversely a J witness supplies L¬c=1, but need not supply L($`s_E`$∧¬c)=1. The new criterion identifies the exact additional support coverage needed under these two pre-existing principles.

Thus a J witness with full support yields K under the stated premises. Finite relative generation is a separate sufficient condition: its finite construction gives the controlled inverse over C5 alone, without $`\mathrm{BC}_t`$ or $`\mathrm{Zorn}_t`$. The present proof extends selection to admitted current chains, rather than replacing that finite argument.

Over C5, the unrestricted OS+J⇒Rev∨K comparison is refuted by the [rigid Souslin model](rigid-souslin-injective-separation.md). With both BCₜ and Zornₜ, the [Actuality theorem](../../../next-update/proofs/c5-zorn-and-propositional-completeness-imply-actuality.md) gives Actuality, so OS gives endpoint separation and hence Rev. The support-coverage premise in (16) remains substantive. The [regular-open image-gap model](injective-gap-without-split-kernel.md) already shows why having a qualified inverse for E is not enough to ensure an inverse killing a prescribed true c. No new verdict about these optional principles in that model is needed here.

## 6. Sources

The actual-current-join argument, maximal-support selection theorem and qualified-inverse criteria are new ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§2–5, unpaginated.

The canonical local-support and density facts are [Local-transversal support](local-transversal-support.md), §§1–3. Admitted adjoints and Frobenius are in [Canonical adjoints and image factorization](canonical-adjoints-and-image-factorization.md), §§2–4, and [Boolean transversals](injective-observers-and-boolean-transversals.md), §§1–3. The finite selection comparison is [Finite generation over an observer's image](finite-relative-image-generation.md), §§1–5.

The $`\mathrm{BC}_t`$ premise is the recorded formulation from Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.2, pp. 23–26; Appendix D, note 92, p. 74. The exact preorder Zorn premise is the recorded `zorn-r` formula, introduced following Cian Dorr's suggestion of 8 October 2026; its background source is Jonathan Lewin, “A Simple Proof of Zorn's Lemma,” *American Mathematical Monthly* 98 (1991), pp. 353–354. Those sources supply the premises and formulations, not the new observer theorem.

All type indices and qualification lists retain their stated external scope.
