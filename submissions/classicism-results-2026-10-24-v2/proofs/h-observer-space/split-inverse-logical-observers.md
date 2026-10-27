# Qualified right-inverse separation is reversible separation

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–5, unpaginated. The existing Boolean-patching and full-H recovery results used below are cited in §5.

Requiring a logical observer to have an admitted qualified right inverse does not produce a weaker full separation principle than reversibility. A one-sided inverse supplies a region where the missing inverse equation holds; a Boolean patch turns any distinguishing right-invertible observer into a distinguishing involution.

```math
\boxed{\mathrm{H}+\text{full separation by qualified right-invertible observers}
\quad\Longleftrightarrow\quad\mathrm{H}+\mathrm{Rev}}
\tag{1}
```

The orientation matters: [qualified left-inverse separation is strictly weaker](finite-block-symmetry-left-inverse.md), §§1–6.

## 1. Exact qualifications and finite-list scope

Use Good_Δ and separation by material agreement from [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §1. Good_Δ consists of the full Boolean composite identities, full universal and existential composite identities at the finite external list Δ, and the translated equality clauses. Over C the latter are consequences of the Boolean qualification.

Let I:=λp.p and let composition be the admitted lambda term. Define

```math
\begin{aligned}
\mathrm{SplitEpi}_\Delta(E):={}&
\mathrm{Good}_\Delta(E)\land
\exists F^{tt}\,[\mathrm{Good}_\Delta(F)\land E\circ F=I],\\
\mathrm{SplitMono}_\Delta(E):={}&
\mathrm{Good}_\Delta(E)\land
\exists F^{tt}\,[\mathrm{Good}_\Delta(F)\land F\circ E=I],\\
\mathrm{Invol}_\Delta(E):={}&
\mathrm{Good}_\Delta(E)\land E\circ E=I
\end{aligned}
```

Thus in SplitEpi, F is a **right inverse** of E. Every displayed composition equation is a whole-operation identity. Both E and F are admitted and qualified for the same list. Neither an external section nor current surjectivity alone is the stated hypothesis.

Write S_{τ,Δ}[SplitEpi] for the corresponding separation instance at relational output type τ, and similarly for involutions or reversible observers. The full schema ranges over all such τ and every finite Δ.

The local construction below is over C+BF, with Δ containing t. Here BF denotes the ambient Barcan schema; only finitely many of its instances enter any chosen application. In particular BF_t supplies the final collection of pointwise inverse identities. We do not claim a minimal background for the local lemma.

The full-H characterization (1) adds no Barcan assumption: forgetting the inverse restriction gives full ordinary logical separation, which already recovers C+BF. Requiring Δ to contain t in the construction loses no full-schema consequence, because any requested finite list may first be enlarged by t.

## 2. A right inverse gives a region with the opposite inverse

Assume E,F are Good_Δ, t∈Δ, and E∘F=I. Define the admitted proposition

```math
u:=\forall p^t\,[F(Ep)\leftrightarrow p]
\tag{2}
```

Its defining universal statement is used as a proposition, not assumed true. In general u need not be Top or currently true.

Universal instantiation and C's Boolean identities give, for every p,

```math
u\land F(Ep)=u\land p
\tag{3}
```

To justify the order reading precisely, the universally closed instantiation implication is an unconditional H theorem. C identifies its Boolean consequences, so u lies below each instance of the displayed biconditional. Boolean restriction to u yields (3); no conditional material equivalence is sent through Logical Equivalence.

E's full Q_t and Boolean identities, together with E∘F=I, give

```math
\begin{aligned}
Eu
 &=\forall p\,E(F(Ep)\leftrightarrow p)\\
 &=\forall p\,[E(F(Ep))\leftrightarrow Ep]\\
 &=\forall p\,[Ep\leftrightarrow Ep]
 =\top
\end{aligned}
\tag{4}
```

The last identity is an unconditional C logical identity. Equations (3) and (4) are the needed local substitute for the missing global identity F∘E=I. They use no atoms, Actuality or C5.

## 3. Turning a distinguishing witness into an involution

Let d be currently false and suppose Ed is currently true. Set

```math
c:=\neg d\land Ed,
\qquad b:=u\land Fc,
\qquad r:=\neg(c\lor b),
\tag{5}
```

and define the admitted observer

```math
T(p):=(c\land Ep)\lor(b\land Fp)\lor(r\land p)
\tag{6}
```

All coefficient identities needed below hold without the current-truth assumptions on d and Ed. Those assumptions will be used only to establish that T distinguishes d from Bottom.

First, by (4) and E∘F=I,

```math
Eb=Eu\land E(Fc)=c
\tag{7}
```

Since c≤Ed, monotonicity of the Boolean homomorphism F gives

```math
b\le u\land F(Ed)=u\land d\le d,
\tag{8}
```

where (3) was used at p=d. Hence b∧c=Bottom, and c,b,r form a Boolean partition of Top. The existing full-operation Boolean-patching lemma therefore makes T a Good_Δ observer. The identity observer, E and F all qualify for that same list; fixed propositional guards add no new observer quantifier type.

Here are the cross-term identities used to check the square of T:

```math
c\land Ec=\bot,
\quad Eb=c,
\quad c\land Er=\bot,
\tag{9}
```

```math
b\le Fc,
\quad b\land Fb=\bot,
\quad b\land Fr=\bot,
\quad b\land F(Ep)=b\land p
\tag{10}
```

For the first identity in (9), c contains Ed whereas Ec contains ¬Ed. The third follows from Eb=c and Er=¬(Ec∨Eb). For (10), b≤Fc is immediate. Since c≤¬d, Boolean preservation gives b≤Fc≤¬Fd; since b≤d, monotonicity gives Fb≤Fd. These imply b∧Fb=Bottom. The identity b∧Fr=Bottom follows from b≤Fc. The final identity in (10) follows from b≤u and (3).

Now expand T(Tp) on the partition c,b,r. On c, (9) eliminates the first and third branches inside E(Tp), while the middle branch gives

```math
c\land Eb\land E(Fp)=c\land p
```

On b, (10) eliminates the second and third branches inside F(Tp), while the first gives

```math
b\land Fc\land F(Ep)=b\land p
```

On r, the identity branch gives r∧Tp=r∧p. Thus

```math
\forall p\,[T(Tp)=p]
\tag{11}
```

For the full-operation inverse requirement, apply NI to each identity in (11), then BF_t to collect them under ∀p. The resulting necessary coextension, followed by C's Intensionality at tt, gives

```math
T\circ T=I
\tag{12}
```

This explicitly uses the stated ambient Barcan premise. It does not assert that an optional pointwise inverse premise can simply be necessitated, and no choice of an external inverse function is made.

Finally c is currently true, because d is false and Ed true. Formula (6) therefore makes Td true. Good_Δ qualification makes TBottom false, so T distinguishes d from Bottom. We have proved:

**Local lemma.** Over C+BF, for a finite Δ containing t, any SplitEpi_Δ observer accepting a currently false proposition supplies an admitted Good_Δ involution accepting that same proposition.

The construction preserves the distinguishing Boolean difference of arbitrary input pairs, not necessarily the original observer's truth profile on every proposition.

## 4. Separation equivalences and what they do not say

Over C+BF, for any fixed finite Δ containing t and any relational output type τ,

```math
S_{\tau,\Delta}[\mathrm{SplitEpi}]
\quad\Longleftrightarrow\quad
S_{\tau,\Delta}[\mathrm{Invol}]
\quad\Longleftrightarrow\quad
S_{\tau,\Delta}[\mathrm{Rev}]
\tag{13}
```

For the nontrivial direction, let X≠Y. SplitEpi separation supplies an eligible observer and a tuple at which the two observed values have different truth values. Let d be the Boolean symmetric difference of those two proposition values. Then Ed is true. If d is true already, identity is a qualified involution distinguishing the pair. If d is false, the local lemma gives a qualified involution T with Td true, so its Boolean laws again make the original proposition values differ in truth under T. This separates X,Y at the same tuple. No new output type or qualification list is used. The reverse implications follow because an involution is its own qualified inverse and a two-sided inverse is a right inverse.

For full typed separation over H, first forget the restriction to recover ordinary full logical separation, hence C+BF. Given any finite target list Δ, use the assumed right-inverse separation instance for Δ∪{t}. Apply (13), then forget the extra t qualification if necessary. This proves the forward direction of (1). Conversely Rev supplies right-inverse separation directly, at each original list. The same proof identifies both with full involutive separation.

Accordingly the right-inverse separation principle inherits all established consequences of Rev, including C5, separately necessary ordinary separation and No Pure Contingency. The atomless finite-block countermodel to Rev also refutes this full right-inverse separation principle; it does not refute ordinary necessary separation.

The theorem concerns separation principles, not equality of the individual observer classes. A right-invertible observer need not itself have a left inverse. We replace a distinguishing witness by another observer. Nor does this prove that current or necessary surjectivity alone supplies an admitted **qualified** right inverse. A whole equation E∘F=I does imply necessary surjectivity of E over C, by NI and the necessitated closed implication from a right inverse to surjectivity, but the converse is not claimed here.

The opposite orientation, F∘E=I with both maps qualified, gives a strictly weaker separation principle, as shown in [the left-inverse models](finite-block-symmetry-left-inverse.md). Reversing the roles of E and F gives a right-invertible F, but need not preserve the distinguishing truth values of E. No equivalence for SplitMono separation is established by (1) or (13).

The separate [left-inverse decomposition](left-inverse-separation-decomposition.md), §§2–6, gives its exact fixed-list alternative: reversible separation, or ordinary separation together with one qualified pair having a currently true kernel element. The same pair then converts every ordinary observer to a left-invertible one without changing its current truth profile. The full-H statement is an external schema of local disjunctions.

## 5. Sources

The local proposition u, the modified swap coefficient b=u∧Fc, and the resulting one-sided-inverse separation characterization are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–4, unpaginated.

The qualified Boolean-patching lemma and the earlier two-sided inverse swap are in [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §4, direct source `misc`, unpaginated. Its full-H recovery uses [Typed separation and Classicism](typed-separation-and-classicism.md), §§3–7. The present proof keeps the same finite qualification list through the patch and only adds t when passing between complete schemas.

For the consequences discussed in §4, see [Reversible separation and pure truth](reversible-separation-and-pure-truth.md) and [Finite-block symmetry: even sizes versus powers of two](finite-block-symmetry-reversible-gap.md). The underlying modal rules and Intensionality are those of Bacon and Dorr, *Classicism*, draft of 16 May 2023, §1.5, pp. 16–18.
