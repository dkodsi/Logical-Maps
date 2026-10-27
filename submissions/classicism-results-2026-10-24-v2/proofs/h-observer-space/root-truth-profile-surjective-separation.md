# Root truth-profile extension: surjective separation without persistence

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new persistence comparison and model verdict: `misc`, this note, §§1–6, unpaginated. The existing higher-type predecessor construction and symmetric model framework are identified in §7.

An individual admitted observer's current surjectivity persists over C+BF_t. Surjective observer separation does not: the model below satisfies

```math
\mathrm C+\mathrm{SurjSep}+\Box\mathrm{BF}
+\Box\mathrm{Functionality}+\neg\Box\mathrm{OS}
\tag{1}
```

Consequently it also refutes necessary SurjSep. Here SurjSep has every relational output type and every finite external qualification list. The failed boxed OS instance has output type t and the empty qualification list. This construction retains ☐BF; the separate [integer-shift predecessor](integer-shift-predecessor-contingent-barcan.md) refutes SurjSep ⇒ ☐BF at every admitted type.

## 1. Individual surjectivity is persistent

Write

```math
\mathrm{Onto}(E):=\forall q^t\,\exists p^t\,Ep=q
```

Over C+BF_t, for every admitted E:tt,

```math
\mathrm{Onto}(E)\ \longrightarrow\
\Box\mathrm{Onto}(E)
\tag{2}
```

Fix E and assume Onto(E). For any current q, choose p with Ep=q. Necessity of Identity gives □(Ep=q). The unconditional existential-introduction theorem

```math
Ep=q\ \longrightarrow\ \exists z^t\,Ez=q
```

can be necessitated. Normality therefore gives □∃z(Ez=q). Eliminating the current existential witness p and generalizing q yields

```math
\forall q^t\,\Box\exists z^t\,Ez=q
```

Apply BF_t to the admitted predicate λq.∃z(Ez=q). This gives (2). The parameter E remains free throughout and is transported inside the box. No optional assumption is necessitated; no Choice, C5, or admitted inverse is used.

For each fixed finite Δ, Good_Δ is also persistent over C. Its Boolean and quantifier requirements are a finite conjunction of operation identities, so Necessity of Identity boxes them. The translated equality clauses follow from those Boolean requirements over C, and that unconditional implication can be necessitated. Hence C+BF_t proves

```math
\mathrm{Good}_\Delta(E)\land\mathrm{Onto}(E)
\ \longrightarrow\
\Box\bigl(\mathrm{Good}_\Delta(E)
\land\mathrm{Onto}(E)\bigr)
\tag{3}
```

Full SurjSep over H implies full OS by forgetting the additional onto qualification, and hence recovers C+BF. Thus (3) applies to every current qualifying witness under the full SurjSep theory. It does not say that those witnesses separate at every future point. The distinction is realized below.

## 2. A symmetric tail with true kernels but no separation

Use the symmetric ideally-full finite-pinning framework, with two countably infinite objects X and Y and all bijections between them as arrows. Partition X as a disjoint union U⊔V of two countably infinite sets. Let G_X be the full permutation group of V, acting as the identity on U. Let G_Y be trivial. At every type retain exactly the symmetric finitely pinned intensions, as in the cited framework.

Call this old model B. It is a C model. All its arrows are invertible, so their actions at every type are bijections. It therefore satisfies C5, BF, and Functionality at every object.

### True-kernel pairs at both objects

Both source groups have an infinite sequence of individually fixed points: use U at X and any enumeration at Y. The [fixed-point symmetry theorem](fixed-point-symmetry-left-inverse-separation.md), §§1–4, therefore supplies at each Z∈{X,Y} admitted operators S_Z,R_Z and a proposition c_Z such that

```math
S_Z\circ R_Z=I,\qquad S_Zc_Z=\bot,\qquad c_Z\text{ is true at }Z
\tag{4}
```

Both operators satisfy every finite full logical qualification list. That theorem checks admission of the entire profiles, their whole inverse identity on arbitrary future inputs, and all quantifier types; it does not merely construct maps of the current proposition algebra. The same pair works for every finite Δ in this model.

For any old arrow b:X→Z, transport (4) back along b⁻¹. Denote the resulting operators and proposition at X by S_b,R_b,c_b. Invertible transport preserves the whole identities and qualifications, giving

```math
S_bR_b=I,\qquad S_bc_b=\bot,\qquad b\in c_b
\tag{5}
```

In particular S_b is currently onto at X. The last assertion follows because transport along b sends c_b to c_Z, which is true at Z. No claim that c_b is true at X is needed.

### Boolean separation still fails at X

Let d be the proposition consisting of all arrows X→Y and no arrows X→X. It is empty-pinned, symmetric, nonbottom, and currently false at X.

Fix any admitted Boolean observer E at X, and a finite pin P for E. Choose distinct a,a′ in V outside P. Let μ∈G_X transpose a,a′ and fix every other individual. Then μ fixes P, so ρ_tt(μ)E=E. For every proposition q at X, symmetry under μ gives

```math
v_X(\rho_t(\mu)q)=v_X(q)
```

Naturality of application consequently gives

```math
v_X\bigl(E(\rho_t(\mu)q)\bigr)=v_X(Eq)
\tag{6}
```

Choose an external linear order on Y and let r contain exactly the arrows h:X→Y satisfying h(a)<h(a′). It is pinned by {a,a′}; its Y-target symmetry condition is vacuous and its X-target component is empty. Thus r is admitted. Swapping a,a′ gives the proposition identity

```math
\rho_t(\mu)r=d\land\neg r
\tag{7}
```

If Ed were true, Boolean preservation, (6), and (7) would make Er true exactly when it is false. Hence Ed is false for every admitted Boolean observer. Such an observer also sends Bottom to Bottom. All Good_Δ observers therefore agree in truth on d and Bottom, although these propositions differ. This refutes OS(t,Δ) for every finite Δ, including the empty list.

This is the existing qualitative-contrast obstruction with the transposition explicitly confined to V. The infinitely many fixed points in U enable (4) but do not remove this obstruction.

## 3. The full higher-type predecessor construction

Apply the existing [root truth-profile extension](../observer-lattice-models.md), §2, to B at X. Its construction is recalled here to make the higher-type admission and C soundness explicit.

Adjoin a new predecessor * with an arrow i:*→X. Every arrow from * to an old object Z is b∘i for an old b:X→Z; there are no arrows from old objects to *. Old domains and interpretations are unchanged.

Define the new root domains recursively. Put A_e=B_e(X) with projection π_e the identity. For a relational type τ=σ₁⋯σ_k t, including k=0, set

```math
A_\tau=
\{0,1\}^{A_{\sigma_1}\times\cdots\times A_{\sigma_k}}
\times B_\tau(X),
\qquad \pi_\tau(f,b)=b
\tag{8}
```

In particular A_t={0,1}×B_t(X). Root truth is the first bit. Every π_σ is onto. Transport along b∘i is ρ_σ(b)π_σ, hence onto at every type.

Application sections the first truth function and applies the old second component to the projected argument. For F=(f,g) of type σt and x∈A_σ,

```math
F(x)=\bigl(f(x),g(\pi_\sigma x)\bigr)
\tag{9}
```

At longer curried types the first component becomes the corresponding section of f, while the second component uses old application. Boolean operations use ordinary Boolean operations on root truth functions and the old Boolean operations on tails. Quantifiers and equality have the interpretations

```math
\begin{aligned}
\forall_\sigma(f,g)&=
\bigl(\forall x\in A_\sigma\ f(x),\ \forall_\sigma^B g\bigr),\\
\exists_\sigma(f,g)&=
\bigl(\exists x\in A_\sigma\ f(x),\ \exists_\sigma^B g\bigr),\\
(x=_\sigma y)&=
\bigl(\delta(x,y),\ (\pi_\sigma x=_\sigma\pi_\sigma y)^B\bigr)
\end{aligned}
\tag{10}
```

Lambda abstraction uses the actual root truth function of its body and the old abstraction evaluated under the projected assignment. Both components are allowed by (8). Beta follows by sectioning, and eta by equality of the first truth functions and old eta. All transports commute with application and the logical interpretations, by their definitions on the old components.

The H axioms and rules are sound: the current root truth clauses are classical with actual equality, the old worlds retain H, and the contextual beta/eta identities hold as just checked. For C's Logical Equivalence schema, H-equivalent formula bodies have identical root truth functions for every root assignment. Their old abstractions are identical because B satisfies C. The pairs in (8) are therefore equal. This verifies the abstraction identity with its actual H-theoremhood side condition, rather than identifying arbitrary currently equivalent bodies.

BF holds at the root at every type. If every F(x) is Top, then every root truth value is true and g(π_σx)=Top_B for every x. Surjectivity of π_σ and old BF give ∀_σ^B g=Top_B, so ∀_σ F=Top. The old objects already satisfy all BF. Consequently the root satisfies necessary BF.

Functionality also holds at the root. Equal values at every root argument give equal first truth functions; surjectivity of the argument projections gives equality of all corresponding old values, so old Functionality identifies the tails. Iterating this argument covers every relational output type. It holds at every old object as well, giving necessary Functionality.

## 4. Admitted surjective observers at the root

For each old b:X→Z define a root truth function and observer by

```math
h_b(p):=\bigl[b\in\pi_t p\bigr],
\qquad E_b=(h_b,S_b)\in A_{tt}
\tag{11}
```

Admission follows directly from (8): the first component is an arbitrary root truth function on A_t, and the second is the admitted old S_b. Its action is

```math
E_b(p)=\bigl(h_b(p),S_b(\pi_t p)\bigr)
\tag{12}
```

### Full logical qualification

The root Boolean laws hold because h_b is evaluation of the projected proposition at b. The old components of the composite operations agree by S_b's full qualification.

For the universal law at σ, let F=(f,g) be an arbitrary root predicate. The root truth of E_b(∀_σF) is the truth at Z of ∀_σρ(b)g. The root truth of ∀x E_b(Fx) says that ρ(b)g is true on every argument of the form ρ_σ(b)π_σx. These are all arguments at Z, because ρ_σ(b)π_σ is onto. Thus the root truth functions agree for every F. The old components are the two old composites for S_b and agree by its whole Q_σ identity. Consequently the full λF operations are identical as pairs in (8). The existential argument is the same with ∃. It works at every admitted type, on arbitrary inputs, without an equality-reflection assumption on π.

The translated equality clauses follow from Boolean qualification over C. Hence E_b is Good_Δ for every finite Δ. These witnesses have stronger semantic uniformity than is required by any one finite schema instance.

### Current surjectivity

Fix any desired root output (ε,q)∈{0,1}×B_t(X). Write εc_b for c_b if ε=1 and Bottom_B if ε=0, and put

```math
z=(\neg c_b\land R_bq)\lor\varepsilon c_b
\tag{13}
```

Boolean preservation and (5) give S_bz=q. Also b∈c_b, so membership of b in z is exactly ε. The admitted root proposition p=(0,z) therefore satisfies

```math
E_b(p)=(\varepsilon,q)
\tag{14}
```

Every E_b is currently onto. Formula (13) constructs the required preimage for each current output; it does not assert that the root operator has an admitted inverse.

The identity observer I at the root is also onto and satisfies every Good list. It reads a proposition's root truth bit.

## 5. Full separation and the exact persistence failures

Two distinct root propositions either differ in their first bit, which I distinguishes in truth, or have different old tails. In the latter case the tails disagree at some old arrow b, and E_b distinguishes them by (11). Thus the onto Good observers separate all root propositions.

For relations of type σ₁⋯σ_k t, a difference between the root truth functions is detected at a root tuple, followed by I. If the old tails differ, old Functionality gives an old argument tuple on which their proposition values differ. Lift it through the onto projections π_σi and use an E_b detecting that old proposition difference. Therefore the root satisfies SurjSep at every relational output type and every finite Δ.

The accessible old object X still fails OS(t,∅), by §2. Hence

```math
*\models\mathrm{SurjSep}\land\neg\Box\mathrm{OS}(t,\varnothing)
\tag{15}
```

SurjSep(t,∅) entails OS(t,∅) simply by forgetting the onto restriction. The same old failure therefore gives ¬□SurjSep(t,∅) at the root. This proves (1) and both schema nonimplications.

The individual persistence lemma remains valid in this model. Each E_b stays a surjective Good observer at every future point. At X, however, its future truth profile is governed by S_b, and the collective profiles of all admitted Boolean observers cannot distinguish d from Bottom. The failure concerns their separating power, not survival of the witnesses' qualifications.

The root is outside C5, as required by the existing C5 theorem equating SurjSep and reversible separation. Indeed p=(0,Bottom_B) and q=(1,Bottom_B) are distinct root propositions with equal old tails. Their distinctness proposition is (1,Bottom_B), which is not Top=(1,Top_B). Thus ND_t fails.

## 6. Scope of the comparison

The positive logical result is C+BF_t⊢Onto(E)→□Onto(E), with no inverse premise and no C5. The negative result concerns the full typed SurjSep theory, despite the stronger background □BF+□Functionality. Its failed future instance is already propositional and Boolean.

This separates persistence of a finite qualification from persistence of a separation sentence. The present model retains □BF. The separate [integer-shift predecessor](integer-shift-predecessor-contingent-barcan.md), §§1–7, now refutes SurjSep⇒□BF_σ at every admitted type σ, using a different tail with non-surjective future transports. Neither construction challenges the C5 equivalence SurjSep↔Rev or the established persistence of reversible separation.

## 7. Sources

The individual surjectivity lemma, the modified symmetric tail, its combination with the predecessor construction, and the resulting SurjSep verdict are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The predecessor's recursive higher-type construction and C soundness are from [Two models separating the upper observer principles](../observer-lattice-models.md), §2, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, direct source `misc`, unpaginated. The present proof recalls the complete construction and supplies a different old model and different observer tails; it does not attribute the new verdict to a published source.

The symmetric ideally-full framework is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8; §3.1, p. 9; Lemma 21, p. 10, as recorded in [Symmetric ideally-full models](../../source/topics/classicism/groups/symmetric-ideally-full.yaml). Its qualitative-contrast precursor is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, p. 79. Section 2 adapts the [observer obstruction](../observer-countermodel.md), §§2–4, and applies [Fixed-point symmetry](fixed-point-symmetry-left-inverse-separation.md), §§1–4.

For the remaining logical ingredients see [NI](../../source/topics/classicism/principles/identity-necessary-r.yaml), Classicism §2.1, p. 22; [BF_t](../../source/topics/classicism/principles/barcan-t.yaml), §3.5, p. 59; [typed separation and Classicism](typed-separation-and-classicism.md); and [surjective logical observers](surjective-logical-observers.md), §§1–4.
