# Universal modal selectors and persistence of MRC

26 October 2026. Ordinary mathematical proof by OpenAI Codex.
Direct source: `misc`, this note, §§1–5, unpaginated. No independent
review, human verification, Lean certification, or literature-priority
claim is made. Work in the fixed finitary relational C.

## 1. Statements

For any admitted output type τ, including e, the single instance
MRC_(τt,τ) supplies a necessarily functional selector for membership
in any inhabited property of τ-entities. The same selector works
for every input type σ, yielding

```math
\boxed{C+MRC_{\tau t,\tau}\ \vdash\
\Box MRC_{\sigma,\tau}+\Box RC_{\sigma,\tau}+\Box IC_\tau}
\tag{1}
```

In particular, over bare C, full MRC satisfies

```math
\boxed{MRC\leftrightarrow\Box MRC
\leftrightarrow(\Box RC+IC)
\leftrightarrow(\Box RC+\Box IC)}
\tag{2}
```

No BF, ND, Vicinity, completeness, or observer premise is required.
The strengthening in (1) changes the input type of the premise:
it is not a claim that the isolated instance MRC_(σ,τ) always makes
that same isolated instance necessary without other hypotheses.

## 2. A universal necessarily serial relation

Fix τ. Define the admitted relation on τt and τ by

```math
U(F,y):=Fy\lor\neg\exists z^\tau Fz
\tag{3}
```

H proves ∀F∃y U(F,y): use an F-instance when one exists, and use
inhabitation of τ otherwise. Its necessitation is an unconditional
C theorem. Apply MRC_(τt,τ), obtaining an admitted S such that

```math
\Box\mathrm{Functional}(S),\qquad S\le U
\tag{4}
```

Thus at every accessible evaluation S selects exactly one y from
each property F, and if F is inhabited, its selected y satisfies F.
Equation (4) has an actual S-witness and necessary assertions about
it. We have not boxed the existence premise by an optional rule.

## 3. One selector uniformly refines every relation

Fix any input type σ and put ρ=στt. From S define the admitted
operation T_S:ρρ by

```math
T_S(R)(x,y):=(Rx)y\land
\bigl(S(\lambda z^\tau\,(Rx)z)\bigr)y
\tag{5}
```

Formula (5) is shorthand for the displayed lambda abstraction; all
curried applications on the right are explicitly parenthesized.
Its output is a relation, so it is admitted even when τ=e.

The algebraic bound T_S(R)≤R is unconditional. From (4), at every
accessible evaluation and for every R and x there, if R has an
output at x, its row λz(Rx)z is inhabited. The unique S-selected
element of that row is an R-output, and it is precisely the unique
T_S(R)-output at x. Consequently (4) entails

```math
\Box\forall R^\rho\left[
T_S(R)\le R\land
\forall x^\sigma\left(
(\exists y^\tau(Rx)y)\to
\exists!y^\tau\,T_S(R)(x,y)\right)\right]
\tag{6}
```

For the order conjunct inside (6), the unconditional bound is true
necessarily; the row assertion follows directly by instantiating
the boxed functionality of S and its boxed inclusion in U. The
universal R,x binders are already inside those necessary statements
after the ordinary typed substitution. No BF moves a merely
current universal statement through a box.

More explicitly, the C proof from the unboxed matrix
Functional(S) and S⊆U establishes the unboxed row assertion for all
R,x. Necessitating its unconditional implication and applying K to
(4) proves the boxed row assertion in (6). The order conjunct uses
the independent unconditional bound, not current functionality.

At any accessible evaluation, let R be necessarily serial from
there onward. By (6), T_S(R) is necessarily functional from there
onward and entails R. This is an MRC witness constructed from R and
the same S. Hence □MRC_(σ,τ). T and the unconditional MRC⇒RC theorem
then give □RC_(σ,τ) as well.

The argument covers new R and x at later evaluations: (4) quantifies
necessarily over all property inputs there, and the row abstraction
in (5) is available there by H. It does not require all those inputs
to be projections of root entities.

## 4. Necessary Intensional Choice and the full equivalence

For a property F:τt define

```math
G_F(y):=Fy\land(SF)y
\tag{7}
```

Again G_F≤F unconditionally, and (4) proves
□∀F(I(F)→∃!y G_F(y)). At any accessible evaluation where F is
necessarily inhabited, (7) therefore supplies a necessarily unique
subproperty of F. Thus □IC_τ. This completes (1).

Full MRC includes MRC_(τt,τ) for every τ, so (1) gives full □MRC,
□RC and □IC. The converse □MRC⇒MRC is T. The existing chooser-of-graphs
theorem gives □RC+IC⇒MRC; adding T for □IC gives the final equivalence
in (2). Every schema is handled at its individual fixed types, with
no object-language quantifier over types.

The [free-root countermodel](free-root-choiceless-henkin-leaf.md)
satisfies RC+□IC but fails MRC. Thus □RC in (2) cannot be replaced
by RC, even with the stronger necessary IC premise.

## 5. Sources and relation to the type-specific BF theorem

- Universal membership totalization and the new cross-instance
  persistence proof: this note, §§2–4, OpenAI Codex,
  26 October 2026, `misc`, unpaginated.
- The definition of MRC and its entailing form: [merged native
  record](../../../../logical-maps/topics/classicism/principles/modalized-relational-choice-r.yaml),
  attributed there to Cian Dorr, 11 October 2026.
- The converse □RC+IC⇒MRC: [existing chooser-of-graphs
  result](../../../../logical-maps/topics/classicism/results/necessary-relational-choice-and-intensional-choice-imply-modalized-relational-choice.yaml),
  its proof attributed there to Cian Dorr, 11 October 2026.
- The [BF-only theorem](barcan-persistence.md), §3, remains useful
  for an isolated fixed instance MRC_(σ,τ), since its premise does
  not include MRC_(τt,τ). For the full schema, the present theorem
  removes BF entirely. Its separate BF-only IC theorem remains
  unchanged. The [finite-support absorbing-entrance countermodel](absorbing-entrance-finite-support-pairs.md)
  now refutes IC⇒□IC over bare C by an explicit ZFC construction,
  so that separate BF premise cannot simply be dropped.
