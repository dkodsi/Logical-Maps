# Local homogeneous intervals supply split observers

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–4, unpaginated.

Over C5, a currently true homogeneous principal interval supplies either a true atom or a qualified inverse pair with a true kernel element. Ordinary logical separation therefore becomes qualified left-inverse separation under this local homogeneity assumption. The argument does not require the image-gap condition J, global homogeneity, or a choice of isomorphisms for all intervals simultaneously.

## 1. Admitted relative homogeneity

Work over C5. Write 0,1 for Bottom, Top and p≤q for p∧q=p. An interval [0,a] is a guarded range within the existing proposition type, not an additional type.

An **admitted relative isomorphism** from [0,a] to [0,b] consists of admitted terms α,β:tt whose restrictions are inverse order isomorphisms between those intervals. We normalize the ambient terms by replacing them with

```math
 \alpha_a(p):=\alpha(a\land p),
 \qquad \beta_b(q):=\beta(b\land q).
 \tag{1}
```

For normalized witnesses, their ranges lie below b,a respectively, and

```math
 \beta\alpha(p)=a\land p,
 \qquad \alpha\beta(q)=b\land q.
 \tag{2}
```

These are whole identities after Functionality. The order-isomorphism requirement is imposed on the guarded inputs. It implies the relative Boolean laws, including α1=b, α0=0 and α(¬p)=b∧¬αp, with the corresponding laws for β.

The isomorphisms are also relative logical isomorphisms for every requested finite type list. Here admission of the inverse matters. If H:σt is admitted and q≤b, then

```math
\begin{aligned}
 q\le\forall x^\sigma\alpha(a\land Hx)
 &\longleftrightarrow\forall x^\sigma\,[\beta q\le a\land Hx]\\
 &\longleftrightarrow\beta q\le a\land\forall x^\sigma Hx\\
 &\longleftrightarrow q\le\alpha(a\land\forall x^\sigma Hx).
\end{aligned}
\tag{3}
```

C5 supplies the admitted meet bounds and Functionality used here. Every type is inhabited, so the two displayed outputs lie below b. Antisymmetry proves the relative universal law; the join argument or Boolean duality proves the existential law. Normalization (1) then gives α(∀x Hx)=∀x α(Hx), and likewise for ∃ and for β. Functionality collects the full composite identities. No uniform selection of preimages or external completeness is used.

Define Hom(a) to say that a≠0 and, for every b with 0<b≤a, there exist admitted relative isomorphisms between [0,a] and [0,b]. This is a formula quantifying over proposition and tt variables. Its order conditions and inverse equations can all be expressed using the existing equality and Boolean operations. It does not quantify over types: (3) supplies each requested finite logical qualification from the same witnesses.

The local truth premise is

```math
 \mathrm{TrueHom}:=\exists a^t\,[a\land\mathrm{Hom}(a)].
 \tag{4}
```

The first conjunct asserts current truth, not a=1. All homogeneity witnesses are admitted; an external isomorphism of underlying sets would not suffice.

## 2. The atom-or-kernel alternative

Recall the one-pair condition K_Δ from [Left-inverse separation](left-inverse-separation-decomposition.md), §1:

```math
\begin{aligned}
 K_\Delta:=\exists E^{tt}F^{tt}c^t\,[
 &\mathrm{Good}_\Delta(E)\land\mathrm{Good}_\Delta(F)\\
 &\land F\circ E=I\land c\land Fc=0].
\end{aligned}
\tag{5}
```

Both observers have the same full Boolean and finite-list quantifier qualification. The kernel assertion Fc=0 is identity with Bottom, not merely current falsity.

**Theorem.** Over C5, TrueHom implies Actuality∨K_Δ for every finite Δ. In the K case, one pair E,F works at every requested finite list.

**Proof.** Choose a currently true a satisfying Hom(a). If a is an atom, it is a true atom, and hence witnesses Actuality.

Otherwise choose x with 0<x<a. Both x and a∧¬x are nonzero. If x is false, put b=x; if x is true, put b=a∧¬x. In either case

```math
 0<b<a,\qquad \neg b.
 \tag{6}
```

Homogeneity supplies one normalized admitted isomorphism α:[0,a]→[0,b] with inverse β. Set

```math
 d:=\neg a\lor b,
 \qquad c:=\neg d=a\land\neg b.
 \tag{7}
```

The proposition d is currently false and c is currently true. Patch the isomorphism with identity outside a:

```math
 A(p):=(\neg a\land p)\lor\alpha(a\land p),
 \qquad
 D(q):=(\neg a\land q)\lor\beta(b\land q).
 \tag{8}
```

These admitted terms are relative logical isomorphisms between [0,1] and [0,d]. The two disjoint output regions give their relative Boolean laws, and (3) together with fixed-guard distributivity gives every requested quantifier law. The inverse calculations are

```math
 D(Ap)=p,
 \qquad A(Dq)=d\land q.
 \tag{9}
```

For example, masking Ap by b removes its ¬a branch and leaves α(a∧p); applying β recovers a∧p. The other output branch is ¬a∧p. The reverse calculation masks q by ¬a and b and therefore recovers d∧q.

Now define the globally qualified observers

```math
 F(q):=D(q),
 \qquad E(p):=A(p)\lor(c\land p).
 \tag{10}
```

The relative source top of D is d and its target top is 1, so D1=1, D0=0, and its normalization Dq=D(d∧q) makes its relative complement law the ordinary Boolean complement law. Thus F is $`\mathrm{Good}_\Delta`$. The two output regions d,c in E give its global Boolean laws; the same fixed-guard and relative quantifier calculation makes E $`\mathrm{Good}_\Delta`$. Functionality supplies full composite identities.

Since Dc=0 and DA=I, equations (9)–(10) give

```math
 F\circ E=I,\qquad Fc=0.
 \tag{11}
```

The proposition c is true, so E,F,c witness K_Δ. Indeed c is the greatest kernel element of F: Dq=0 iff d∧q=0, by (9). The construction uses only the selected a,b,α,β and lambda terms, with no family of chosen isomorphisms. ∎

The theorem is a current disjunction. Neither optional TrueHom nor its selected witnesses have been necessitated. The atom branch cannot be omitted: a true atom is itself homogeneous, but the finite atomic case need not contain a true-kernel inverse pair.

## 3. Ordinary separation becomes left-inverse separation

Let OS denote full logical separation, and let S_t be its single propositional instance with qualification list {t}. Over C5 that instance already supplies full OS by the established same-observer type reduction and Functionality.

The established local atomic-observer converse gives

```math
 \mathrm{C5}+S_t+\mathrm{Actuality}
 \quad\Longrightarrow\quad
 \mathrm{Atomicity}_t
 \quad\Longrightarrow\quad\mathrm{End}
 \quad\Longrightarrow\quad\mathrm{Rev}.
 \tag{12}
```

The first step uses a correct endpoint evaluator at the true atom, composed with an ordinary distinguishing observer. Its universal diagonal yields an atom below each nonbottom proposition. Only the single separation instance S_t is needed. See [Plenitude and endpoint separation](plenitude-endpoint-bridge.md), §4, and its cited local converse; Plenitude is not a premise in (12).

In the nonatomic case of §2, K_Δ converts each $`\mathrm{Good}_\Delta`$ observer G into

```math
 E_G(p):=(c\land Gp)\lor(\neg c\land Ep).
 \tag{13}
```

Then F∘E_G=I, while E_Gp has the same current truth value as Gp because c is true. This is the same-witness normalization of [Left-inverse separation](left-inverse-separation-decomposition.md), §2. It preserves every observed truth value at every argument tuple.

Consequently

```math
\boxed{
 \mathrm{C5}+\mathrm{OS}+\mathrm{TrueHom}
 \quad\Longrightarrow\quad
 \mathrm{Rev}\lor(\mathrm{OS}\land K_{\{t\}})
 \quad\Longrightarrow\quad\mathrm{SplitMono}.}
\tag{14}
```

The same conclusion follows with S_t in place of full OS, keeping C5. The full-schema disjunction is justified: (12) supplies full Rev in the atom branch, and (8)–(10) supply one qualified pair for every finite list in the other branch. No object-language type quantifier or infinitary disjunction is used.

In particular no J premise is needed. The result is a sufficient structural criterion, not a converse to SplitMono and not a solution to the general question C5+OS+J⇒Rev∨K. A countermodel to that implication cannot admit a currently true homogeneous interval of the stated kind.

## 4. Admitted covers and model scope

One may replace TrueHom in (14) by an explicitly admitted homogeneous cover. For any fixed admitted type σ, suppose H:σt satisfies

```math
 \forall x^\sigma\,[Hx=0\lor\mathrm{Hom}(Hx)],
 \qquad (\exists x^\sigma Hx)=1.
 \tag{15}
```

In the second formula the equality is `(∃x Hx)=1`: it asserts the join of the family is Top. Since that existential proposition is true, ordinary quantifier reasoning supplies x with Hx true. This excludes Hx=0 and gives a true homogeneous interval. Thus (15) implies TrueHom without Choice or finite coverage.

This is useful for evaluating proposed Boolean-algebra models, but admission remains essential. A product of homogeneous components, for example, falls under the cover argument only when the component family, its Top join, and the required relative isomorphisms are admitted in the interpretation. An arbitrary external decomposition, or external homogeneity alone, does not establish (15) in a Henkin model. No generic-ultrafilter model construction or new separating model is asserted in this note.

## 5. Sources

The atom-or-kernel alternative, the explicit patched false-interval isomorphism, and the local-homogeneity separation criterion are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–4, unpaginated.

The admitted interval language and the equivalence of K with an admitted isomorphism onto a false principal interval are in [Finite generation over an observer's image](finite-relative-image-generation.md), §6. The current-truth-profile normalization from K is in [Left-inverse separation](left-inverse-separation-decomposition.md), §2. The local Actuality converse and endpoint/reversible implications retain the sources in [Plenitude and endpoint separation](plenitude-endpoint-bridge.md), §4, and [Logical observer hierarchy](../logical-observer-hierarchy.md), §§3–4.
