# The canonical support of local Boolean transversals

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated.

Every logical observer over C5 has an admitted proposition measuring where its image admits local Boolean transversals. This support has exact composition and Boolean-patching laws. Local transversals glue over an admitted cover precisely when every pair glues; directed covers therefore suffice, while unrestricted covers need not.

The support also gives a canonical normalization onto a composition-closed class of observers. Separation by that class is exactly reversible separation, although individual members need not be invertible or even injective. This extends finite relative generation without treating an infinite admitted join as a finite truth disjunction.

## 1. Local transversals and the canonical support

Work over C5. Fix a finite external qualification list Δ containing t. All observers below are admitted $`\mathrm{Good}_\Delta`$ operations unless stated otherwise. Good means whole Boolean and listed quantifier composite identities. No injectivity, Choice or external completeness is assumed.

For E, let $`L_E`$⊣E⊣R_E be its [canonical admitted adjoints](canonical-adjoints-and-image-factorization.md), and put $`C_E`$=E∘$`L_E`$. We use

```math
q\le C_Eq,\qquad
L_E(q\land Ep)=L_Eq\land p
\tag{1}
```

$`L_E`$ and $`C_E`$ preserve all admitted joins. $`C_E`$ is the image closure, not the original modal possibility operator. These laws hold without injectivity.

Use the local-transversal predicate from [Finite generation over an observer's image](finite-relative-image-generation.md), §2:

```math
\mathrm{Loc}_E(b):=
\forall q\,[b\land C_E(b\land q)=b\land q]
\tag{2}
```

By Functionality, (2) is equivalent to equality of the two displayed complete unary operations. We may use that identity as the definition of its guard. C5 makes the guard an endpoint: 1 when (2) holds, 0 when it fails. Define the admitted support

```math
s_E:=\exists b^t\,[\mathrm{Loc}_E(b)\land b]
\tag{3}
```

Thus (3) is the join of the admitted local transversals. It is an actual proposition, not a set of external points. Three different conditions must be kept distinct: $`s_E`$ is currently true; $`s_E=1`$; and $`s_E`$ is itself local.

## 2. The maximal region covered by local intervals

For any b, $`L_E`$ maps [0,b] onto $`[0,L_E b]`$. An explicit preimage of $`p\le L_E b`$ is b∧Ep, by (1). Moreover

```math
\boxed{\mathrm{Loc}_E(b)
\quad\longleftrightarrow\quad
L_E\text{ is injective on }[0,b]}
\tag{4}
```

If b is local, $`q=b\land E(L_E q)`$ for q≤b, proving injection. Conversely suppose the restriction is injective. For q≤b, the element $`q'=b\land E(L_E q)`$ lies in [0,b], contains q, and satisfies $`L_E q'=L_E q`$ by (1). Therefore q′=q. This proves locality. All interval statements use guards in the existing proposition type; no interval type or choice of inverse values is introduced.

Locality is hereditary. If v≤b and b is local, monotonicity gives

```math
v\land C_E(v\land q)
\le v\land C_E(b\land q)=v\land q,
\tag{5}
```

with the reverse inequality from (1). In particular 0 is local and every local b satisfies b≤$`s_E`$.

The support has the following exact maximal-region characterization:

```math
\boxed{
r\le s_E\quad\longleftrightarrow\quad
\forall q\,[0\ne q\le r\ \to\
\exists b\,(0\ne b\le q\land\mathrm{Loc}_E(b))]}
\tag{6}
```

For the forward direction, distribute q over (3). If every q∧b with local b were zero, q∧$`s_E`$ would be zero, contradicting q≠0. A nonzero such intersection is local by heredity and lies below q. Conversely, if r is not below $`s_E`$, apply the right side to q=r∧¬$`s_E`$. The resulting nonzero local b lies both below $`s_E`$ and below its complement, a contradiction.

Consequently ¬$`s_E`$ contains no nonzero local transversal, and $`s_E`$ is the largest region with the local-density property in (6). This does not say that $`s_E`$ is local. The distinction is essential in §6.

## 3. Exact gluing for admitted families

Let b:σt be any admitted family and write u=∃i^σ b_i. Then

```math
\boxed{
\mathrm{Loc}_E(u)
\quad\longleftrightarrow\quad
\forall i,j\,\mathrm{Loc}_E(b_i\lor b_j)}
\tag{7}
```

The forward direction is heredity. Conversely use admitted-join preservation and fixed-meet distributivity to expand

```math
u\land C_E(u\land q)
=\exists i\,\exists j\,[b_i\land C_E(b_j\land q)]
\tag{8}
```

For each i,j, locality of b_i∨b_j bounds the displayed joinand by q. Thus the left side is at most u∧q, and the opposite inequality follows from the unit in (1). This proves (7), including an empty index domain if one were permitted.

In particular, an admitted directed family of local transversals has a local join: if each pair lies below a family member, its binary union is local by heredity, and (7) applies. More generally, pairwise compatibility in the exact sense Loc_E(b_i∨b_j) is necessary and sufficient.

The same proof applied to the endpoint-guarded family Loc_E(b)∧b shows that $`s_E`$ itself is local exactly when any two local transversals have a local union. Equivalently, the family of all local transversals is directed. This gives a greatest local transversal precisely in that case.

These statements concern admitted families with the displayed identity conditions. They do not turn the current extension of an arbitrary proposition-valued predicate into a uniformly admitted family of its members. No general chain-upper-bound or selection principle is inferred here.

## 4. Composition, iteration and Boolean patching

For G=F∘E, adjunction gives $`L_G=L_E\circ L_F`$. The interval-surjection observation before (4) proves

```math
\boxed{
\mathrm{Loc}_{F\circ E}(b)
\quad\longleftrightarrow\quad
\mathrm{Loc}_F(b)\land
\mathrm{Loc}_E(L_Fb)}
\tag{9}
```

Indeed, injection of the composite on [0,b] forces injection of L_F there. To obtain injection of $`L_E`$ on [0,L_Fb], use the explicit L_F-preimages b∧Fp; no selected preimage family is needed. The reverse implication is injection of the composite of those two restrictions. Equation (4) converts this into (9).

The supports therefore obey the exact formula

```math
\boxed{s_{F\circ E}=s_F\land F(s_E)}
\tag{10}
```

If b is local for the composite, (9) gives b≤s_F and L_Fb≤$`s_E`$. Adjunction gives b≤F($`s_E`$), proving one inequality after taking the join of all such b.

For the other inequality, expand s_F∧F($`s_E`$) as the admitted double join of b∧Fc, with b local for F and c local for E. This uses F's existential preservation and its fixing of the endpoint-valued locality guards. The element b∧Fc is local for F by heredity, and

```math
L_F(b\land Fc)=L_Fb\land c
\tag{11}
```

is local for E, again by heredity. Equation (9) makes every joinand local for F∘E, so each lies below its support. This proves (10).

In particular s_I=1, the class $`s_E=1`$ is closed under composition, and for every fixed external n≥1,

```math
s_{E^n}=\bigwedge_{i=0}^{n-1}E^i(s_E)
\tag{12}
```

Every onto Good observer has support 1, because $`C_E`$=I. Precomposition by such an observer preserves support; postcomposition by an onto F sends the support to F($`s_E`$). Equations (10)–(12) are identities of proposition outputs; the Good qualifications used throughout remain whole-operation identities.

There is also a precise finite-patching law. For an arbitrary proposition d, put

```math
G(p):=(d\land Ep)\lor(\neg d\land Fp)
\tag{13}
```

Boolean partition patching makes G Good with full identities. Its left adjoint is

```math
L_Gq=L_E(d\land q)\lor L_F(\neg d\land q),
\tag{14}
```

as follows directly by testing whether q≤Gp. On [0,d] this is $`L_E`$, and on [0,¬d] it is L_F. Using (4), heredity and the definition of support yields

```math
\boxed{s_G=(d\land s_E)\lor(\neg d\land s_F)}
\tag{15}
```

For example, a local G-element restricted to d is local for E, giving one inequality; every local E-element restricted to d is local for G, giving the other. The complementary part is identical.

## 5. A canonical normalization and its separation strength

Define the admitted normalization

```math
\mathcal N(E)(p):=(s_E\land Ep)\lor(\neg s_E\land p)
\tag{16}
```

It is Good by (13). Equation (15) gives

```math
s_{\mathcal N(E)}=1
\tag{17}
```

If $`s_E=1`$ then N(E)=E, so N(N(E))=N(E) on the Good class. Thus N is an admitted retraction from that class onto its subclass with support 1. This is not a claim that the individual N(E) is injective, involutive or has a qualified inverse.

If $`s_E`$ is currently true, (3) gives an actually true local transversal by the ordinary existential truth rule. The [local-profile theorem](finite-relative-image-generation.md), §4, then supplies a qualified involution T with

```math
\forall p\,(Tp\leftrightarrow Ep)
\tag{18}
```

No infinite join has been treated as a finite disjunction: the witness comes from the admitted existential in (3). If $`s_E`$ is false, N(E) instead has identity's current truth profile; if $`s_E`$ is true, N(E) has E's profile. In all cases N(E) has a profile represented by a qualified involution, by (17).

Consequently, over C5 and at each fixed relational output type τ and finite Δ containing t,

```math
\boxed{
S_{\tau,\Delta}[\mathrm{Rev}]
\ \longleftrightarrow\ S_{\tau,\Delta}[s_E=1]
\ \longleftrightarrow\ S_{\tau,\Delta}[s_E]
\ \longleftrightarrow\ S_{\tau,\Delta}[\mathcal N(\mathrm{Good}_\Delta)]}
\tag{19}
```

All classes in (19) consist of $`\mathrm{Good}_\Delta`$ observers. The middle $`s_E`$ qualification means current truth, while $`s_E=1`$ means identity. The final class is the admitted range predicate $`\exists E(\mathrm{Good}_\Delta(E)\land H=N(E))`$. Every reversible observer is onto and hence has support 1; the other directions follow by (18). These arguments preserve every observed current truth value, so also give the full relational schemas. They do not select a family of involutions uniformly over E or introduce an infinitary type qualification.

## 6. Relation to finite generation and the limits of gluing

$`\mathrm{FG}_n(E)`$ implies $`s_E=1`$ for every fixed external n: the finitely many cells from the finite-generation theorem are local and join to 1. This does not require E injective. The support criterion can apply where every fixed finite-generation bound fails.

For a concrete example, use the full-function C5 interpretation with proposition algebra P(N), current truth membership of 0, complete Boolean meets and joins for the quantifiers, and crisp equality. The full-function Boolean-valued construction is the one verified in [Injective observers and Boolean transversals](injective-observers-and-boolean-transversals.md), §§4–6, with this complete atomic algebra in place of 2×RO(Cantor²). Current truth preserves all the interpreted meets and joins.

The admitted principal endpoint observer

```math
E(p)=
\begin{cases}
\mathbb N,&0\in p,\\
\varnothing,&0\notin p
\end{cases}
\tag{20}
```

is a complete Boolean homomorphism and therefore Good at every type. Every singleton is local: its only subparts are itself and 0. Hence $`s_E`$=N. But the image has only two elements, and adjoining any fixed finite number of Boolean generators gives a finite algebra, not P(N). Thus $`\mathrm{FG}_n(E)`$ fails for each external finite n. This distinguishes individual qualification classes; their separating power is still the same by (19).

Finally, full support need not itself be local. On the four-element Boolean algebra 2×2, take E(ε,δ)=(ε,ε). Both atoms are local, so $`s_E=1`$, but $`C_E(1,0)=(1,1)`$; therefore 1 is not local. This example explains why an arbitrary local cover cannot simply be joined into one transversal. The controlled inverse theorem still requires its stated hypotheses, and no qualified global inverse is asserted from support 1 alone.

## 7. Sources

The canonical support, its maximal-region characterization, compatible gluing, composition and patching laws, normalization and exact separation comparison are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The admitted adjunction and family-preservation facts are proved in [Canonical adjoints and image factorization](canonical-adjoints-and-image-factorization.md), §§2–4. Frobenius and the relative inverse calculations are in [Injective observers and Boolean transversals](injective-observers-and-boolean-transversals.md), §§1–3; the Frobenius calculation there already applies without injectivity. The hereditary local predicate and same-profile involution are in [Finite generation over an observer's image](finite-relative-image-generation.md), §§2 and 4. The present note extends those arguments to canonical supports and admitted covers, while retaining their whole-operation scope.
