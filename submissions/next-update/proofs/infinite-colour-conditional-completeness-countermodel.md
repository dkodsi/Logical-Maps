# Infinite colour symmetry and failure of conditional completeness persistence

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated.

## 1 The countermodel and its consequence

There is a model of C with

```math
BC_t+\Box OS+\Box BF_{\mathrm{all}}
+\Diamond\bigl(\Box ND_t\land\neg BC_t\bigr)
\tag{1}
```

Here OS is the full schema of logical separation at every relational output type and every finite qualification list. Each box on a schema means its separately boxed, object-variable-closed instances. At the single target evaluation witnessing the possibility in (1), the model satisfies C5 at every type, not merely the displayed proposition instance.

Consequently

```math
C+OS+BC_t
\ \not\Rightarrow\
\Box(\Box ND_t\to BC_t)
\tag{2}
```

The model has two objects. At the source, infinitely many infinite colour classes restrict which current predicates are admitted. Every admitted family of propositions has a least upper bound, obtained by forgetting finitely many coordinates and taking a union of colour patterns. At the target the symmetry restriction disappears. The target is the familiar finitely pinned permutation model, where some admitted families have no least upper bound.

The source nevertheless has enough admitted observers to inspect every finite pattern at either object. The crucial arrows agree with the colour projection except at finitely many points. They are still surjective, so their induced actions are onto at every type. This provides whole logical observers, including their quantifier laws.

All constructions are in the ordinary ZFC metatheory. No infinitary comprehension principle is added to the object language.

## 2 The category and the admitted domains

Let

```math
Y=\mathbb N,\qquad
X=\mathbb N\times\mathbb N,\qquad
C_y=\{y\}\times\mathbb N,\qquad
\beta(y,n)=y
\tag{3}
```

The arrows are

```math
\begin{aligned}
 \mathrm{Hom}(X,X)&=\mathrm{Sym}(X),\\
 \mathrm{Hom}(Y,Y)&=\mathrm{Sym}(Y),\\
 \mathrm{Hom}(X,Y)&=
 \{b:X\to Y:\text{every fibre }b^{-1}\{y\}\text{ is infinite}\},\\
 \mathrm{Hom}(Y,X)&=\varnothing
\end{aligned}
 \tag{4}
```

Composition is composition of functions. These classes are closed under composition. In particular, composing an infinite-fibre surjection on either side with a permutation preserves the defining property.

Give both objects the ideal of finite subsets and designate the symmetry groups

```math
G_X=\prod_{y\in Y}\mathrm{Sym}(C_y),
\qquad G_Y=\{1_Y\}
\tag{5}
```

Individuals at an object are its underlying set, acted on by the arrows. Relational domains are exactly the symmetric finitely pinned intensions of the [symmetric ideally-full framework](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/groups/symmetric-ideally-full.yaml).

Here are the profile conventions used in the proof. If $`\tau=\bar\sigma t`$, an entity A at W has a Boolean profile

```math
A(h,\bar z)\in\{0,1\},
\qquad h:W\to V,\quad
\bar z\in\prod_i D_{\sigma_i}(V)
\tag{6}
```

A finite $`P\subseteq W`$ pins A when arrows h,k with the same target and the same restriction to P have identical profiles on every target argument tuple. Symmetry means

```math
A(\mu h,\rho_\mu\bar z)=A(h,\bar z)
\qquad(\mu\in G_V)
\tag{7}
```

Transport and application are

```math
(\rho_f A)(h,\bar z)=A(hf,\bar z),
\qquad
(A[\bar x])(h)=A(h,\rho_h\bar x)
\tag{8}
```

For propositions, the argument tuple is empty. Equality of admitted entities is equality of their entire profiles, rather than equality of their current extensions.

The usual recursive profile construction supplies the relational types and currying. To spell out the relevant landing point: if A is pinned by P and some arguments at its source have finite pins $`P_1,\ldots,P_m`$, the section obtained by application is pinned by $`P\cup P_1\cup\cdots\cup P_m`$. After transport along h, the corresponding finite images pin the transported section. Equation (7) is preserved by these sections. Boolean operations and quantification preserve symmetry and finite pinning. The standard interpretation of lambda abstraction therefore remains in these domains. The framework theorem gives C, with its original H-theoremhood gate for Logical Equivalence.

The colour classes are external construction data specifying the symmetry group. No extra nonlogical colour predicates or constants are added. Pure-language assertions suffice; if constants are required, relational constants can be interpreted by Top.

## 3 Every typed transport is onto

All individual transports are surjective. The self-arrows are permutations, so their actions are bijections at every type, with inverse transport along the inverse permutation. It remains to check an arbitrary arrow $`b:X\to Y`$.

Let $`A\in D_\tau(Y)`$ have a finite pin $`T\subseteq Y`$. Choose a finite $`S\subseteq X`$ such that $`b|_S:S\to T`$ is a bijection. This is just a finite selection of preimages. Define a source profile $`\widetilde A`$ as follows.

On X-target arrows put its value constantly zero. On an arrow $`l:X\to Y`$, if $`l|_S`$ is injective, choose any permutation k of Y satisfying

```math
k|_T=l|_S\,(b|_S)^{-1}
```

and put

```math
\widetilde A(l,\bar z)=A(k,\bar z)
\tag{9}
```

If $`l|_S`$ is not injective, put the value zero.

The finite partial injection extends to a permutation of Y. Different choices of k agree on T, so (9) is independent of the choice. The profile is S-pinned. Its X-target part is zero and hence symmetric; its Y-target part has no further symmetry condition because $`G_Y`$ is trivial. Thus it is an admitted source entity. The definition works on arbitrary target arguments, at every relational type.

For every permutation $`k:Y\to Y`$ and every appropriate argument tuple,

```math
(\rho_b\widetilde A)(k,\bar z)
=\widetilde A(kb,\bar z)
=A(k,\bar z)
\tag{10}
```

This is equality of full future profiles. Therefore $`\rho_b\widetilde A=A`$. In particular it is not merely a lift on the image of source argument tuples.

Every typed action of every arrow is consequently onto. The usual semantic Barcan argument now gives $`BF_\sigma`$ at both objects for every allowed type $`\sigma`$: any future entity can be lifted to a current entity. Thus the model satisfies separately boxed all-type BF. It also has the corresponding current Functionality instances.

## 4 Source propositional completeness

Write $`B=D_t(X)`$. For finite $`P\subseteq X`$, let $`B_P`$ be its subalgebra of P-pinned propositions.

On a self-arrow $`h:X\to X`$, a P-pinned symmetric proposition depends exactly on the colour pattern $`\beta h|_P:P\to Y`$. Two finite restrictions with the same colour pattern are related by a member of $`G_X`$: within each colour class, extend the finite bijection between their distinct images. Conversely every prescribed finite colour pattern is realized by a permutation of X, by choosing distinct images in the required infinite colour classes.

On a target arrow $`l:X\to Y`$, a P-pinned proposition depends exactly on $`l|_P:P\to Y`$. Every such finite map, with collisions permitted, extends to an infinite-fibre surjection. The remaining countably infinite source can be partitioned into infinitely many infinite sets and sent onto the respective target points.

The self and target branches are independent. Hence

```math
B_P\cong\mathcal P(Y^P)\times\mathcal P(Y^P)
\tag{11}
```

These are externally complete algebras of already admitted propositions. The entire algebra B is the union of these finite-pin subalgebras; its external completeness is neither assumed nor needed.

Fix P and let p have a finite pin T. Define $`\pi_Pp`$ by existentially forgetting the coordinates in $`T\setminus P`$ in each of its two pattern descriptions. Thus a pattern on P is accepted exactly when it extends to a pattern on $`P\cup T`$ accepted by p on that branch. This defines a member of $`B_P`$, the least P-pinned upper bound of p.

Let $`G_{X,(P)}`$ be the pointwise stabilizer of P inside $`G_X`$. Then

```math
p\le\pi_Pp,\qquad
\pi_P(\rho_g p)=\pi_Pp
\quad(g\in G_{X,(P)})
\tag{12}
```

**Orbit envelope lemma.** In the whole algebra B, $`\pi_Pp`$ is the least upper bound of the orbit
$`\{\rho_g p:g\in G_{X,(P)}\}`$.

It is an upper bound by (12). To prove leastness, suppose u bounds this orbit, choose a finite pin R for u, and suppose $`\pi_Pp\not\le u`$. On one of the two branches there is a pattern on $`P\cup R`$ making $`\pi_Pp`$ true and u false. Extend its restriction to P to a pattern on $`P\cup T`$ making p true.

Choose $`g\in G_{X,(P)}`$ moving every member of $`T\setminus P`$ outside $`P\cup R`$. This uses fresh points within the same original colour classes; every such class is infinite. Combine the first pattern on $`P\cup R`$ with the second pattern moved onto $`g(T\setminus P)`$. There is no conflict on the remaining overlap, which lies in P.

At the self branch, the combined colour pattern is realized by choosing distinct images in each indicated target colour class and extending to a permutation. Thus no collision between prescribed target individuals is being assumed away. At the target branch, the combined value pattern is realized by an infinite-fibre surjection. The resulting arrow makes $`\rho_g p`$ true and u false, contrary to the upper-bound assumption. This proves the lemma. It concerns the least admitted envelope of the orbit; its raw set-theoretic union need not itself be P-pinned.

Now let $`R:tt`$ be any admitted predicate at X, pinned by P, and let

```math
\mathcal F=\{p\in B:R(1_X,p)=1\}
```

be its actual current extension. It is invariant under $`G_{X,(P)}`$. Indeed symmetry gives
$`R(g,\rho_g p)=R(1_X,p)`$, while P-pinning gives
$`R(g,\rho_g p)=R(1_X,\rho_g p)`$.

Using the complete algebra in (11), form

```math
u=\bigvee_{p\in\mathcal F}\pi_Pp\quad\text{in }B_P
\tag{13}
```

This is an ordinary union of pattern sets, hence an admitted P-pinned proposition. Every p in the family lies below u. If z is any admitted upper bound of the actual family, invariance makes it an upper bound of the full stabilizer orbit of each p. The orbit envelope lemma gives $`\pi_Pp\le z`$ for each p, so $`u\le z`$.

Thus u is the actual Boolean least upper bound of the current extension of R. This proves $`BC_t`$ at X. No weighted existential is substituted for the actual join, and no admitted operation selecting these joins is constructed.

## 5 Admitted whole logical readers

For an arrow $`a:W\to V`$, let $`\chi_a(q)=q(a)`$ be its evaluation character on source propositions. This is external notation used to define profiles.

Two kinds of arrows out of X will suffice.

1. A finitely supported permutation $`s:X\to X`$. Choose P containing its support. For $`v\in G_{X,(P)}`$, s and v commute. Since propositions are target-symmetric,

```math
\chi_s(\rho_vq)=q(sv)=q(vs)=q(s)=\chi_s(q)
```

2. An arrow $`b':X\to Y`$ which agrees with $`\beta`$ outside a finite P. It still has every fibre infinite, and $`b'v=b'`$ for $`v\in G_{X,(P)}`$. Consequently $`\chi_{b'}`$ has the same stabilizer invariance.

Fix either selected arrow b and its finite P. The self-arrow colour chart is

```math
\mathcal U_P=
\{h\in\mathrm{Sym}(X):\beta h|_P=\beta|_P\}
\tag{14}
```

For $`h\in\mathcal U_P`$, choose $`g_h\in G_X`$ with $`g_h|_P=h|_P`$. Such an extension exists separately in each colour class. Define the observer's complete profile by

```math
O(h,q)=
\begin{cases}
q(b g_h^{-1}), &h:X\to X,\ h\in\mathcal U_P,\\
q(\beta), &h:X\to X,\ h\notin\mathcal U_P,\\
q(1_Y), &h:X\to Y
\end{cases}
\tag{15}
```

The proposition q is always in the domain at the target of h. Thus every expression in (15) is typed.

If $`g_h'=g_hv`$ for $`v\in G_{X,(P)}`$, stabilizer invariance gives
$`\chi_b\circ\rho_{(g_h')^{-1}}=\chi_b\circ\rho_{g_h^{-1}}`$. So the row is independent of the extension. The definition is P-pinned.

To check symmetry, let $`\mu\in G_X`$. The chart is preserved by left multiplication by $`\mu`$, and one may choose $`g_{\mu h}=\mu g_h`$. Therefore, on the chart,

```math
O(\mu h,\rho_\mu q)
=q\bigl(b g_h^{-1}\mu^{-1}\mu\bigr)
=O(h,q)
\tag{16}
```

Off the chart, $`\beta\mu=\beta`$ gives the same conclusion. At Y there is no nontrivial designated symmetry. This proves admission of $`O:tt`$. At the actual row its character is precisely $`\chi_b`$.

Every row of O evaluates at an arrow with onto transports at every type: $`b g_h^{-1}`$, $`\beta`$, or $`1_Y`$. This gives the whole logical laws directly. More explicitly, at any future row $`h:X\to W`$, let $`a_h:W\to V`$ be the evaluation arrow in (15). For an arbitrary future predicate $`F\in D_{\sigma t}(W)`$,

```math
\begin{aligned}
 O(h,\forall x^\sigma Fx)
 &=\bigwedge_{z\in D_\sigma(V)}F(a_h,z),\\
 (\forall x^\sigma O(Fx))(h)
 &=\bigwedge_{x\in D_\sigma(W)}
       F(a_h,\rho_{a_h}x)
\end{aligned}
 \tag{17}
```

The two are equal by onto transport. The corresponding joins prove the existential law. Boolean preservation is immediate at each row. Since h and the future input F were arbitrary, these are identities of the entire displayed operations, not merely current material equivalences. Over C the equality clauses of Good follow from the Boolean laws, as in the [observer definition](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1.

Hence each O is Good for every finite list simultaneously. No finite guard normalization is needed.

## 6 Full typed separation at both objects

Let p,q be different source propositions and choose an arrow h distinguishing their profiles. Let P pin both.

If $`h:X\to X`$, extend the finite partial injection $`h|_P`$ to a finitely supported permutation s of X. The reader for s has the same current values on p and q as h, and therefore separates them.

If $`h:X\to Y`$, define $`b'`$ to agree with h on P and with $`\beta`$ outside P. Finite modification leaves every fibre infinite. Its reader again has the required current values. Thus logical observers separate all source propositions.

For relations $`A\ne B`$ of type $`\bar\sigma t`$, choose a future arrow h and a target tuple $`\bar z`$ where their profiles differ. By §3 lift that tuple to a source tuple $`\bar x`$. Then $`A[\bar x]`$ and $`B[\bar x]`$ are distinct propositions, distinguished at h. The preceding reader separates them currently and satisfies any prescribed finite qualification list. This proves full typed OS at X without replacing tuple identity by current coextension.

At Y, for every permutation b define an observer with constant profile $`O(h,q)=q(b)`$. There is no target symmetry restriction, so this profile is empty-pinned. Every row is a permutation evaluation; the same onto calculation proves all whole logical laws. These readers separate propositions and, by tuple lifting, all relations at Y.

Each closed OS instance therefore holds at both objects. Its evaluation after any arrow is its value at the target object. This proves $`\Box OS`$, instance by instance, as asserted in (1).

## 7 The target is C5 and fails propositional completeness

The future category of Y contains only its permutations. Its relational domains have no symmetry restriction and contain exactly the finitely pinned profiles. Thus it is exactly the recorded [finite-support permutation model](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/finite-support-permutations.yaml).

All transports there are invertible, so inequality at every type is persistent. The model satisfies C5 at Y, including $`\Box ND_t`$.

For a direct proof that $`BC_t`$ fails, let $`A_m`$, for $`m\ge1`$, be the proposition on $`\mathrm{Sym}(\mathbb N)`$ saying that the permutation interchanges 0 and m. It is pinned by $`\{0,m\}`$. The external family
$`\mathcal A=\{A_m:m\ge1\}`$ is the current extension of an admitted predicate: use the same row $`\mathcal A`$ at every permutation. This is empty-pinned, and $`G_Y`$ is trivial.

Suppose u were its least admitted upper bound. Choose a finite pin S for u, enlarged to contain 0, and choose distinct m,n outside S. Let $`\alpha=(0\ m\ n)`$ be the three-cycle. It agrees on S with the transposition $`(0\ m)`$. The latter belongs to $`A_m`$, so S-pinning of u gives $`\alpha\in u`$.

But the finitely pinned proposition

```math
v=\{h:h(0)\ne m\ \text{or}\ h(m)=0\}
\tag{18}
```

contains every $`A_j`$, while $`\alpha\notin v`$. Thus u is not below the upper bound v, a contradiction. The actual family has no least upper bound.

Every arrow X→Y therefore reaches an evaluation satisfying $`\Box ND_t\land\neg BC_t`$, completing the proof of (1) and (2).

## 8 The dense observed ideal is realized

The same model gives an idempotent logical observer whose observed zero ideal is proper and dense in the region satisfying ☐ND at t.

Let c be the proposition consisting of all X→Y arrows and no self-arrows. It equals $`\Box ND_t`$. At Y, ND_t and its box hold. At X, the nonzero proposition of self-arrows becomes Bottom after transport to Y, so ND_t fails; the same holds at every self-arrow.

Use the baseline reader E whose self rows are all evaluation at $`\beta`$ and whose Y-target rows are identity evaluation. This is (15) with $`P=\varnothing`$ and $`b=\beta`$. It is whole Good at every type. It is also a whole idempotent: every self row first moves to the target branch, where the observer acts identically.

For its observed zero ideal,

```math
I_E=\{p:E(p=0)\text{ is currently true}\},
\qquad
p\in I_E
\ \Longleftrightarrow\
p(k\beta)=0\text{ for every }k\in\mathrm{Sym}(Y)
\tag{19}
```

Thus $`E(c)`$ is true and $`c\notin I_E`$. Nevertheless $`I_E\cap[0,c]`$ is order-dense. If $`0<p\le c`$ and T pins p, choose distinct x,x' in one colour class outside T. Intersect p with the additional condition $`h(x)\ne h(x')`$ on X→Y arrows. This gives a nonzero finitely pinned proposition: any finite pattern witnessing p can be extended with distinct values at x,x' and then to an infinite-fibre surjection. It vanishes at every $`k\beta`$, because $`\beta(x)=\beta(x')`$. It is therefore a nonzero member of $`I_E`$ below p.

In particular, even an idempotent whole logical observer can accept the boxed ND premise and reject $`BC_t`$ at a source satisfying $`BC_t`$. This observer does not commute with native Box; the positive completeness reflection theorem for [native-Box observers](box-observer-completeness.md) is unaffected.

The countermodel refutes conditional completeness persistence. It does not by itself settle the separate consistency question $`C+\mathrm{Max}(C)+OS+BC_t`$.

## 9 Sources and verification scope

- **New construction and arguments:** `misc`, this note, §§1–8; OpenAI Codex, 25 October 2026, unpaginated.
- **Symmetric finite-pinning semantics:** Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8, §3.1, p. 9, Lemma 21, p. 10, and Proposition 22, p. 11; through the linked symmetric model group. These supply the general framework and the finite-pin transport method, not the new two-object construction.
- **Underlying action semantics and target:** Andrew Bacon and Cian Dorr, *Classicism*, draft of 16 May 2023, Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74; Proposition D.5(1), pp. 75–76. The target completeness failure is reproved in §7.
- **Orbit envelope precedent:** [Finite colour patterns and propositional Boolean completeness](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/finite-colour-propositional-completeness.md), §§2–3. The new source uses infinitely many colours and externally complete pattern algebras, together with a separate target branch.

