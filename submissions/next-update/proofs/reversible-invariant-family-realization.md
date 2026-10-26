# Reversible separation and realization of invariant families

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi. Direct source: `misc`, this note, §§1–6, unpaginated.

The endpoint-parameter schema controls a particular algebra of definable invariant propositions. Reversible separation controls the entire admitted invariant algebra. This distinction gives a precise additional density hypothesis under which the schema would suffice. There is also an exact modal completion: an admitted endpoint-valued family of propositions, closed under reversible logical observers, has a true member whenever it has a possible member. This completion requires just one family type and one formula. Allowing arbitrary endpoint-valued higher-type parameters without the closure restriction would instead force Extensionality.

## 1. Scope and established ingredients

Work over exact C5 in the fixed relational language. In particular C5 means boxed ND, not merely unboxed ND. Let 0 and 1 denote Bottom and Top, so that $`\Box p`$ is $`p=1`$, and $`\Diamond p`$ is $`p\ne0`$.

Use $`B(E)`$ and $`A(E)`$ from [Reversible separation and fixed propositions](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/reversible-fixed-proposition-characterization.md), §1:

```math
A(E):=B(E)\land\exists F^{tt}
\bigl(B(F)\land E\circ F=I\land F\circ E=I\bigr).
```

Here $`B`$ consists of the whole-operation Boolean and type-t quantifier identities. The inverse is admitted and qualified. Over C5, qualification at t gives qualification at every fixed quantifier type; propositional separation by these observers gives full relational Rev. The guard $`A(E)`$ is an endpoint. The qualified observers contain identity and are closed under composition and admitted inverses.

Put

```math
\mathrm{Inv}(p):=\forall E^{tt}(A(E)\to Ep=p),
\qquad
O(p):=\exists E^{tt}(A(E)\land Ep).
```

The cited note, §§2–4, proves that $`O(p)`$ is the least admitted invariant proposition above p, and

```math
\mathrm{Rev}\ \Longleftrightarrow\
\forall p\bigl(\mathrm{Inv}(p)\to(p=0\lor p=1)\bigr).
\tag{1}
```

Let **EPNC** denote the original schema from [Component-shift symmetry](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/component-shift-symmetry-reversible-gap.md), §6: for each pure formula $`P(\bar R,\bar x)`$, whose free parameters are individual variables and first-order relations $`R_i:e^{n_i}t`$, $`n_i\ge1`$, universally close

```math
\mathrm{End}(\bar R)\to
\bigl(P(\bar R,\bar x)\leftrightarrow\Box P(\bar R,\bar x)\bigr).
\tag{2}
```

All higher-type bound variables are permitted. Arbitrary higher-type free parameters are excluded. The endpoint condition concerns the proposition objects $`R_i[\bar y]`$, not merely their current truth values.

## 2. General reversible conjugation

The prior pure-truth argument is written for involutions. The following version shows that every EPNC-definable proposition is fixed by **all** admitted reversible observers, without assuming Rev.

Fix qualified mutual inverses E and F. Define their typewise lifts simultaneously. At e, use only the metalevel convention $`E_e^*x=F_e^*x=x`$. At t, put $`E_t^*=E`$ and $`F_t^*=F`$. At every admitted arrow type $`\sigma\rho`$, define

```math
\begin{aligned}
E_{\sigma\rho}^*X
 &:=\lambda y^\sigma.\ E_\rho^*\bigl(X(F_\sigma^*y)\bigr),\\
F_{\sigma\rho}^*X
 &:=\lambda y^\sigma.\ F_\rho^*\bigl(X(E_\sigma^*y)\bigr).
\end{aligned}
\tag{3}
```

No object of forbidden type ee is formed. Every transformation actually abstracted in (3) has relational output.

Induction on types, beta reduction and C5 Functionality prove that the two lifts are mutually inverse. The same calculation proves application compatibility:

```math
(E_{\sigma\rho}^*X)(E_\sigma^*y)=E_\rho^*(Xy).
\tag{4}
```

The lifts fix every pure logical constant. For the Boolean constants this is Boolean preservation and cancellation of E with F. For equality, the lifted arguments are equal exactly when the original arguments are equal; both equality judgments are endpoints under C5, and E fixes those endpoints. Functionality then identifies the whole equality operations.

For a quantifier, the calculation is

```math
\begin{aligned}
E_{(\sigma t)t}^*(\forall_\sigma)(G)
 &=E\bigl(\forall y^\sigma\,F(G(E_\sigma^*y))\bigr)\\
 &=\forall y^\sigma\,G(E_\sigma^*y)\\
 &=\forall y^\sigma\,Gy.
\end{aligned}
\tag{5}
```

The middle step uses E's whole quantifier identity and $`E\circ F=I`$. The final step is bijective reindexing. To obtain its identity rather than merely current equivalence, Functionality first collects the typewise inverse laws into whole-operation identities. NI makes those identities necessary. The universally closed conditional reindexing theorem can then be necessitated and instantiated using CBF; Intensionality yields the displayed identity. At e the change of variable is the identity substitution. This is the same licensed reindexing argument as [Reversible separation and pure truth](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/reversible-separation-and-pure-truth.md), §3; no optional qualification premise is necessitated.

Pure-term induction now gives

```math
E_\tau^*\bigl(Q(\bar a)\bigr)
   =Q(E_{\sigma_1}^*a_1,\ldots,E_{\sigma_k}^*a_k).
\tag{6}
```

There are only finitely many types in any application of this argument. For endpoint first-order relations, the lifted individual arguments remain unchanged and E fixes every output, so

```math
E_{e^nt}^*R=R.
\tag{7}
```

Functionality supplies the whole identity in (7). Thus every value of an eligible EPNC formula is invariant under every A-member. This conclusion holds over C5 alone; it does not require reversible separation.

More generally, any finite tuple of higher-type parameters fixed by these typewise lifts gives invariant values for all pure formulas in that tuple. Under Rev, those values are endpoints. The restriction is **conjugation stability**, not endpoint-valuedness alone.

## 3. An exact modal witness principle for invariant families

For one admitted family $`X:tt`$, define

```math
\begin{aligned}
\mathrm{End}_t(X)
 &:=\forall p^t(Xp=0\lor Xp=1),\\
\mathrm{Closed}_A(X)
 &:=\forall E^{tt}\forall p^t
       \bigl((A(E)\land Xp)\to X(Ep)\bigr),\\
J(X)&:=\exists p^t(Xp\land p),\\
K(X)&:=\mathrm{End}_t(X)\land\mathrm{Closed}_A(X).
\end{aligned}
\tag{8}
```

**Theorem.** Over C5, full Rev is equivalent to the single sentence

```math
\boxed{
\forall X^{tt}\left[
K(X)\to
\left(
\exists p^t(Xp\land\Diamond p)
\ \longrightarrow\
\exists p^t(Xp\land p)
\right)\right].}
\tag{9}
```

In words: an endpoint-valued admitted family closed under reversible logical observers has a true member whenever it has a possible member. The family quantifier ranges over admitted objects. There is no external powerset, orbit set, or choice function in (9).

**Closure really is conjugation stability.** Suppose K(X). If E has qualified inverse F, closure gives $`Xp\to X(Ep)`$. Apply closure for F to Ep to obtain the converse. Since X is endpoint-valued,

```math
X(Ep)=Xp.
\tag{10}
```

For this type, $`E_{tt}^*X=E\circ X\circ F`$. E fixes X's endpoint outputs, while (10) for F gives $`X\circ F=X`$. Functionality therefore proves $`E_{tt}^*X=X`$. Conversely, this conjugation identity and endpoint-valuedness imply (10), hence closure. Thus the guard in (9) expresses the exact parameter stability needed by §2.

**The join J(X) is invariant.** E preserves the type-t existential and fixes each Xp, so

```math
E(J(X))=\exists p^t\bigl(Xp\land Ep\bigr).
\tag{11}
```

When Xp is Top, closure makes Ep an X-member, so Ep is below J(X). When Xp is Bottom the joinand is Bottom. The admitted join's upper-bound law gives $`E(J(X))\le J(X)`$. Apply the same argument to F and then E to obtain the reverse inequality. Hence J(X) is invariant.

The endpoint guard also gives

```math
\Diamond J(X)
\quad\longleftrightarrow\quad
\exists p^t(Xp\land\Diamond p).
\tag{12}
```

A nonzero selected p lies below J(X), proving one direction. If no selected p is nonzero, every joinand $`Xp\land p`$ is Bottom, so the admitted join is Bottom. This proves the other direction. Only an admitted quantifier join is used.

**Rev implies (9).** Choose a nonzero X-member p. Reversible separation supplies a qualified E with Ep true. Closure makes Ep an X-member, which witnesses the conclusion. Equivalently, J(X) is a nonzero invariant and (1) makes it Top.

**(9) implies Rev.** For arbitrary r define the admitted orbit predicate

```math
X_r(q):=\exists E^{tt}\bigl(A(E)\land q=Er\bigr).
\tag{13}
```

Its atomic guards are identities, so C5 makes it endpoint-valued. Composition shows A-closure. Identity gives $`X_r(r)`$. If r is nonzero, (9) supplies a true q with $`X_r(q)`$; the latter existential supplies an admitted qualified E with $`q=Er`$. Thus every nonzero r is accepted by a reversible observer. Apply this to the Boolean symmetric difference of any unequal p and q. The established type compression and Functionality then give full Rev. One can also verify directly from the two join bounds that $`J(X_r)=O(r)`$.

### Equivalent noncontingency form

Sentence (9) is also equivalent, over C5, to

```math
\boxed{
\forall X^{tt}\bigl(K(X)\to
   (J(X)\leftrightarrow\Box J(X))\bigr).}
\tag{14}
```

The point requires care: $`\Diamond q\to q`$ and $`q\to\Box q`$ need not be equivalent at a single q. Here the **uniform family sentence** provides the missing complement instance. Since J(X) is invariant, the admitted singleton family

```math
Y_X(q):=(q=\neg J(X))
\tag{15}
```

is endpoint-valued and A-closed, and $`J(Y_X)=\neg J(X)`$. Applying (14) to Y_X rules out J(X) being nonzero and false, yielding (9) by (12). Conversely, applying (9) to Y_X rules out J(X) being true but different from Top, yielding (14). Thus a single higher-parameter type and a single pure formula suffice, with the precisely stated stability guard.

This is an exact modal completion of EPNC, not a proof of its original converse. Its guard explicitly refers to the reversible action. Its content is the realizability of possible members of invariant admitted families; it does not claim that the original first-order parameter language already represents those families.

## 4. Why endpoint-valuedness alone is too strong at higher types

Consider extending EPNC to arbitrary endpoint-valued parameters X:tt while dropping the action-closure requirement. Already the single formula J(X) forces Extensionality.

For arbitrary p, the admitted singleton predicate

```math
H_p(q):=(q=p)
\tag{16}
```

is endpoint-valued under C5, and the admitted join laws give

```math
J(H_p)=p.
\tag{17}
```

Thus unguarded higher-parameter noncontingency for J gives $`p\to p=1`$ for every p. Applying the same conclusion to $`\neg p`$ shows that every proposition is 0 or 1. Materially equivalent propositions are therefore identical. Repeated C5 Functionality lifts this to Extensionality at every relational type.

The unguarded witness variant of (9) has the same defect: at H_p it gives $`\Diamond p\to p`$ for arbitrary p, and the complement instance again forces every p to be an endpoint.

The collapse already occurs with an endpoint-valued **second-order predicate on individual properties**, without allowing a free parameter of type tt. Use the one pure template

```math
L(X):=\exists F^{et}\bigl(XF\land\forall x^e Fx\bigr),
\qquad X:(et)t.
\tag{18}
```

For arbitrary p put $`c_p:=\lambda x^e.p`$ and $`Z_p(F):=(F=c_p)`$. The predicate Z_p is endpoint-valued under C5. Its singleton join selects precisely $`\forall x\,c_p x`$, which is identical to p by beta reduction and the vacuous-quantifier law in the inhabited individual domain. Thus $`L(Z_p)=p`$. Noncontingency for this one template, uniformly over all endpoint-valued X of type (et)t, again forces every proposition to be an endpoint. First-order endpoint parameters are therefore insufficient for Rev, while unrestricted endpoint second-order parameters are already too strong for a characterization of Rev.

By contrast, H_p is A-closed exactly when p is invariant. The stability restriction therefore blocks this collapse for arbitrary proposition parameters. It is not cosmetic. Rev itself does not imply Extensionality: the existing finite-support permutation model satisfies Rev and has an atomless proposition algebra; see [Reversible separation and pure truth](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/reversible-separation-and-pure-truth.md), §4.

## 5. A precise definability-density bridge for the original schema

In any fixed C5 model, let $`\mathcal I`$ be the Boolean algebra of admitted propositions fixed by all A-members. Let $`\mathcal D`$ be the set of values of all formulas allowed in EPNC, at all admitted individual parameters and endpoint first-order relation parameters. This definition of $`\mathcal D`$ is external: it quantifies over formulas and finite parameter lists. It is not an assertion that $`\mathcal D`$ is the extension of an admitted predicate.

Section 2 proves $`\mathcal D\subseteq\mathcal I`$. The constants 0 and 1 lie in $`\mathcal D`$, and joining the finite parameter lists shows that $`\mathcal D`$ is a Boolean subalgebra. One must not infer closure under arbitrary admitted families whose members happen individually to be definable: their defining formulas need not be uniform.

The two principles say exactly

```math
\begin{aligned}
\mathrm{EPNC}&\quad\Longleftrightarrow\quad\mathcal D=\{0,1\},\\
\mathrm{Rev}&\quad\Longleftrightarrow\quad\mathcal I=\{0,1\}.
\end{aligned}
\tag{19}
```

For the first equivalence, use EPNC for both P and its negation. The second is (1).

A sufficient representational hypothesis is **order density in the invariant algebra**:

```math
\forall u\in\mathcal I\setminus\{0\}\quad
\exists d\in\mathcal D\setminus\{0\}\quad d\le u.
\tag{20}
```

Under EPNC, any such d must be 1. Thus every nonzero invariant u is 1, and Rev follows. Conversely, Rev makes (20) automatic, choosing the pure definable proposition 1 below the only nonzero invariant. Consequently, among C5 models satisfying EPNC, Rev is equivalent to (20).

Condition (20) is weaker as a general representation requirement than demanding that every invariant be definable: it only asks for a nonzero definable part. It identifies the missing bridge rather than supplying it. C5 and EPNC alone do not establish this density; the countermodel route in this directory retains invariant propositions invisible to the permitted parameter formulas. Neither external definability of an orbit nor an external automorphism is enough: the required subproposition must be admitted and definable in the stated parameter language.

## 6. A finite definability case where EPNC collapses to No Pure Contingency

Here is a precise finite-domain extension of the singleton observation. It does **not** assume that finite cardinality by itself supplies definable names.

Suppose there are finitely many pure formulas $`\delta_1(x),\ldots,\delta_m(x)`$ such that, at the current model, each $`\delta_i`$ is endpoint-valued, each has exactly one satisfying individual $`a_i`$, the individuals $`a_i`$ are pairwise distinct, and these exhaust the individual domain. Then over C5:

```math
\mathrm{EPNC}\quad\Longleftrightarrow\quad
\mathrm{NoPureContingency}.
\tag{21}
```

Only the reverse direction needs proof. Any endpoint first-order relation R on this finite domain has a finite Boolean table. Replace R by the pure lambda term whose body is the disjunction of the tuple predicates

```math
\delta_{i_1}(y_1)\land\cdots\land\delta_{i_n}(y_n)
```

corresponding to the true entries of that table; use Bottom if the list is empty. Endpoint-valuedness gives equality of every output proposition, and Functionality gives identity of R with the replacement term.

After replacing all relation parameters, eliminate each individual parameter $`a_i`$ from P by existentially quantifying a variable guarded by $`\delta_i`$. The admitted join has exactly the original proposition as its one nonzero potentially contributing joinand, so the resulting closed pure sentence Q is identical to the original value of P. This is an identity justified by the endpoint guards and join bounds, not by applying Logical Equivalence to optional assumptions. No Pure Contingency for Q and $`\neg Q`$ makes that value an endpoint, proving EPNC.

For a singleton individual domain, take the sole pure definition $`\delta_1(x):=(x=x)`$. Thus the singleton case needs no individual constant and no forbidden individual-valued function. Without endpoint-valued pure definitions of all individuals, (21) has not been established here merely from the finiteness of the individual domain.
