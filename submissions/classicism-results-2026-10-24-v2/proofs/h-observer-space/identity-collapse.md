# Identity-fixing observers and identity collapse over H

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated. These are ordinary proof arguments, not database records or Lean certificates.

Accepting separation by observers that preserve the truth of propositional identity judgments has an exact H characterization. It collapses true identity judgments to the fixed Top and false identity judgments to one fixed false proposition. That false proposition need not be the fixed Bottom. The converse uses admitted nested-identity terms, without any Boolean-operation identities or assumptions from C.

## 1. Fixed language and three qualifications

Work in H with the fixed relational type system. Put

```math
b:=\forall p^t\,p,\qquad
T:=b\lor\neg b,\qquad B:=b\land\neg b,\qquad
z:=(T=B)
```

H proves T true and B false, hence T distinct from B. Consequently z is false and distinct from T. These truth facts do not identify z with B.

For an observer E of type tt define

```math
\begin{aligned}
A(E)&:=ET,\\
\mathrm{CorrectEq}_t(E)
&:=\forall p,q^t\,[E(p=q)\leftrightarrow p=q],\\
\mathrm{FixEq}^{\rm pt}_t(E)
&:=\forall p,q^t\,[E(p=q)=(p=q)],\\
\mathrm{FixEq}^{\rm op}_t(E)
&:=(\lambda p,q^t.E(p=q))=(\lambda p,q^t.p=q)
\end{aligned}
```

Thus CorrectEq is material correctness, FixEq^pt is pointwise identity, and FixEq^op is identity of the two whole composite operations. None is the condition E(p=q)=(Ep=Eq).

For any qualification K(E), write

```math
S[K]:=\forall p,q^t\left[
p=q\leftrightarrow\forall E^{tt}\bigl(K(E)\to(Ep\leftrightarrow Eq)\bigr)
\right]
```

Define propositional identity collapse by

```math
\mathrm{IC}_t:=\forall p,q^t\left[
\bigl(p=q\to(p=q)=T\bigr)
\land
\bigl(p\ne q\to(p=q)=z\bigr)
\right]
```

The outer implications and conjunction are ordinary truth-level connectives. IC_t says that identity judgments have exactly the appropriate one of the two outputs T,z. It is not the assertion that all propositions belong to that pair.

## 2. Exact propositional characterization

**Theorem 1.** Over H,

```math
\boxed{
S[A\land\mathrm{CorrectEq}_t]
\ \leftrightarrow\
S[A\land\mathrm{FixEq}^{\rm pt}_t]
\ \leftrightarrow\
\mathrm{IC}_t}
```

### Separation forces collapse

Assume S[A and CorrectEq_t]. Fix p,q and abbreviate their identity judgment by j:=(p=q).

If p=q, every eligible observer accepts j by CorrectEq and accepts T by A. Separation identifies j with T.

If p differs from q, every eligible observer rejects j. The proposition z is the false identity judgment T=B, so every eligible observer also rejects z by the same CorrectEq_t clause. Separation identifies j with z. Generalizing p,q gives IC_t.

Pointwise fixing implies material correctness by H equality substitution. The pointwise-qualified class is therefore smaller, so its separation principle implies separation by the material-qualified class. This also proves the necessity of IC_t for the pointwise version.

### Admitted nested-identity tests

Assume IC_t. For every proposition r, its judgment (r=T) is T when r=T and z otherwise. Thus the admitted observer
$`E_0(r):=(r=T)`$
has the exact output table

```math
E_0(r)=
\begin{cases}
T,&r=T,\\
z,&r\ne T
\end{cases}
```

In particular E_0(T)=T and E_0(z)=z.

For any a distinct from both T and z, define the admitted observer

```math
E_a(r):=\bigl((r=T)=((r=a)=z)\bigr)
```

Every parenthesized judgment here is an equality between propositions, so every application of IC is at t. The calculation is entirely in identities:

| Input | r=T | r=a | (r=a)=z | E_a(r) |
| --- | --- | --- | --- | --- |
| r=T | T | z | T | T |
| r=a | z | T | z | T |
| r different from T,a | z | z | T | z |

For example, on the last row the outer judgment is z=T, hence has output z by IC_t. On the first two rows the outer judgments are T=T and z=z, respectively, hence have output T. Therefore

```math
E_a(r)=
\begin{cases}
T,&r=T\text{ or }r=a,\\
z,&\text{otherwise}
\end{cases}
```

In particular E_a fixes T and z. The truth profile of E_a is the indicator of the two-element set {T,a}; E_0 is the indicator of {T}. This description abbreviates the displayed term calculations, not an assumption that arbitrary external set-functions are admitted.

### Qualification and separation

Every propositional identity judgment j is T or z by IC_t. Since each displayed observer fixes both of these outputs, E(j)=j. Thus E_0 and all available E_a satisfy FixEq_t^pt and A; they actually fix T.

Let p,q be distinct. If exactly one is T, E_0 distinguishes them. Otherwise neither is T. At least one of p,q differs from z; choose that proposition as a. Then a differs from both T,z, and E_a accepts a while rejecting the other proposition. These cases show that the displayed admitted tests separate every distinct pair. No choice function or simultaneous selection of witnesses is required.

Consequently S[A and FixEq_t^pt] holds. H equality substitution supplies the converse direction of its biconditional. Since these witnesses are also materially correct, the material separation principle holds as well. This finishes Theorem 1.

## 3. Whole-operation identities and full typed separation

Write Functionality for the schema

```math
\forall F,G^{\sigma\rho}\left[
(\forall x^\sigma\,Fx=Gx)\to F=G
\right],\qquad \rho\ne e
```

Under the two local instances Fun_(t,t) and Fun_(t,tt), pointwise FixEq_t lifts to FixEq_t^op: first identify the q-abstractions for each p, then identify the resulting p-abstractions. Hence

```math
\mathrm H+\mathrm{IC}_t+\mathrm{Fun}_{t,t}
 +\mathrm{Fun}_{t,tt}
\ \vdash\ S[A\land\mathrm{FixEq}^{\rm op}_t]
```

Conversely, strong propositional separation entails IC_t because application gives pointwise fixing and then material correctness. No converse from IC_t alone to strong propositional separation is asserted here.

For a relational type tau=sigma_1...sigma_n t, define Sep_tau[K] by replacing p,q in S with X,Y of type tau and requiring all eligible E to agree on X and Y after every current argument tuple. Let FullSep[K] be the schema of these instances at every relational type, including t.

**Theorem 2.** Over H, the following theories are equivalent:

```math
\boxed{
\begin{aligned}
&\mathrm{FullSep}[A\land\mathrm{CorrectEq}_t],\\
&\mathrm{FullSep}[A\land\mathrm{FixEq}^{\rm pt}_t],\\
&\mathrm{FullSep}[A\land\mathrm{FixEq}^{\rm op}_t],\\
&\mathrm{IC}_t+\mathrm{Functionality}
\end{aligned}}
```

**Proof.** For every qualification K, full typed separation is equivalent over H to S[K] plus Functionality. In one direction, pointwise identity of two relational objects gives observational agreement at all their argument tuples, so typed separation identifies the objects. In the other, propositional separation identifies the outputs at each tuple; successive Functionality instances identify the relational objects. This is the general typed-separation theorem in [Typed separation and the recovery of Classicism over H](typed-separation-and-classicism.md), §2.

Apply that theorem and Theorem 1 to the first two qualifications. For the strong qualification, application and propositional separation give IC_t, and typed separation gives Functionality. Conversely IC_t supplies the explicit pointwise-qualified separating tests above; Functionality upgrades their two composite equality operations, giving strong propositional separation. The general typed theorem then gives every relational separation instance. ∎

This proof never derives or assumes C. The Functionality schema is explicit, and there is no necessitation, NI, Logical Equivalence, or conversion of a conditional pointwise identity into an abstraction identity without the stated Functionality instances.

## 4. The type scope of equality fixing

Fixing equality judgments at t must be distinguished from fixing equality judgments at every admitted type. For a type sigma define

```math
\mathrm{IC}_\sigma:=\forall x,y^\sigma\left[
\bigl(x=y\to(x=y)=T\bigr)
\land
\bigl(x\ne y\to(x=y)=z\bigr)
\right],
```

with the same propositional false anchor z=(T=B). Define CorrectEq_sigma and its two fixing variants by the same changes of input type.

For a finite external list Gamma containing t, Theorem 1 generalizes to

```math
\begin{aligned}
&S[A\land\bigwedge_{\sigma\in\Gamma}\mathrm{CorrectEq}_\sigma]
\ \leftrightarrow\
S[A\land\bigwedge_{\sigma\in\Gamma}\mathrm{FixEq}^{\rm pt}_\sigma]\\
&\hspace{30mm}\leftrightarrow\
\bigwedge_{\sigma\in\Gamma}\mathrm{IC}_\sigma
\end{aligned}
```

Forward, compare each true identity judgment with T and each false one with z; inclusion of t ensures every eligible observer rejects z. Conversely IC_t defines the same admitted tests E_0,E_a, while each IC_sigma makes the sigma-identity judgments outputs T,z fixed by those tests. Thus one common observer family satisfies all clauses in the finite list.

Under full typed separation, all three qualification tiers are equivalent to this finite collapse package plus Functionality. For each sigma, the whole equality-operation identity uses Fun_(sigma,t) and Fun_(sigma,sigma t), both supplied by that schema. Taking the schemas over all finite Gamma containing t yields the corresponding all-type collapse result. This is a collection of finite formulas, not an object-language quantifier over types or an infinitary observer qualification.

## 5. What is and is not being collapsed

IC_t alone leaves room for arbitrarily many propositions outside {T,z}. The nested-identity tests were chosen precisely to distinguish those additional propositions. The result therefore concerns the outputs of the identity operation, not Extensionality or a two-proposition universe.

IC_t also does not say z=B. If this extra identity is added, IC_t is equivalent to the familiar identity-bivalence assertion

```math
\forall p,q\,[(p=q)=T\lor(p=q)=B]
```

Indeed the truth of an identity judgment determines which of the true/false endpoints it can equal. Conversely identity bivalence sends the false judgment T=B to B, so z=B, and then gives both clauses of IC_t.

Primitive negation, conjunction, disjunction and quantifiers have not been assumed to preserve {T,z}, and the constructed observers have not been claimed to preserve those operations. The result is an identity branch of the observer theory, separate from complete logical qualification.

## 6. Adding material negation preservation

Define

```math
N_{\rm mat}(E):=\forall p\,[E(\neg p)\leftrightarrow\neg Ep],
\qquad
\mathrm{DN}:=\forall p\,(\neg\neg p=p)
```

**Theorem 3.** Over H,

```math
\boxed{
S[A\land N_{\rm mat}\land\mathrm{CorrectEq}_t]
\ \leftrightarrow\
\mathrm{DN}+\mathrm{IC}_t+(z=\neg T)}
```

This is a material-preservation theorem. No claim that its hypotheses imply full negation-operation preservation is included.

### Necessity

Every eligible observer agrees on p and its double negation, by two applications of N_mat. Separation gives DN. Enlarging the eligible class to all accepting CorrectEq_t observers preserves separation, so Theorem 1 gives IC_t.

Every eligible observer rejects z by CorrectEq_t. It also rejects the proposition neg T, because it accepts T and preserves negation materially. Separation therefore identifies z with neg T. These arguments require no identity law for primitive negation before they establish one.

### Orbit-flipping tests give sufficiency

Assume DN, IC_t and z=neg T. Double negation makes primitive negation an involution, and H's truth clauses show that it has no fixed point. Its distinguished orbit is {T,z}: the displayed identity gives neg T=z, and DN gives neg z=T.

The identity observer I(r):=r is materially negation-preserving, accepts T, and is materially correct on identity judgments. It distinguishes every pair with different truth values.

For any a outside {T,z}, use the admitted terms

```math
\chi_a(r):=(r=a)\lor(r=\neg a),
```

```math
G_a(r):=(\chi_a(r)\land\neg r)
         \lor(\neg\chi_a(r)\land r)
```

These expressions use only H's truth laws; no identities between Boolean operations are assumed. Their truth calculation says that G_a reverses the truth of r on the orbit {a,neg a} and leaves it unchanged off that orbit.

More explicitly, DN and ordinary equality substitution give

```math
\chi_a(\neg r)\leftrightarrow\chi_a(r)
```

Indeed neg r=a is equivalent to r=neg a, and neg r=neg a is equivalent to r=a. If this common orbit-membership condition is true, G_a(r) has the truth value of neg r while G_a(neg r) has that of r; if it is false, the two truth values are those of r and neg r, respectively. Thus

```math
G_a(\neg r)\leftrightarrow\neg G_a(r),
```

so N_mat(G_a).

The orbit {a,neg a} is disjoint from {T,z}. For example neg a=T would imply a=neg T=z by DN; the other cases are analogous. Therefore G_a accepts T and rejects z. IC_t makes every true identity judgment equal T and every false one equal z, so G_a is materially correct on every propositional identity judgment. Hence every such G_a is eligible.

Finally let p,q be distinct and have the same truth value. They cannot be negation mates, since negation changes truth. At least one lies outside {T,z}, because T and z have opposite truth values; choose such a member as a. The orbit of a contains exactly one of p,q. Consequently G_a reverses that member's truth and leaves the other's truth unchanged, distinguishing them. Together with the identity observer for different-truth pairs, these tests prove separation. This finishes Theorem 3.

The generic typed-separation theorem also gives the exact material full typed variant: add the Functionality schema to the right side of Theorem 3. That observation does not upgrade a material negation truth law to a pointwise output identity, so no strong-negation converse follows from it.

## 7. Sources and scope

The direct source for Theorem 1 and the nested-identity construction is this original argument (`misc`, OpenAI Codex, 24 October 2026, §§1–2, unpaginated). Theorem 2 combines it with the H typed-separation theorem cited in §3. The finite-type extension in §4 is the same proof with its equality scope made explicit. Theorem 3 is the original orbit-flipping argument in §6; its double-negation setting is related to [Truth profiles and connective reducts](truth-profiles-and-connective-reducts.md), §6.

The framework is specified in [Background](../../source/topics/classicism/background.md). The related identity-bivalence representation theorem is [Observer representation under local identity assumptions](representation-under-identity-bivalence.md).
