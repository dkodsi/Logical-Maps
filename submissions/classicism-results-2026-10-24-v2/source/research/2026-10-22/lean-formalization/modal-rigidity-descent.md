# Rigid unions, images and comprehension descent

22 October 2026. New mathematical continuation by Codex, with Lean drafts in
`Classicism/Results/Research/ModalRigidityDescent.lean`. This note gives the
argument rather than claiming novelty or completed formal verification. The
live verification state is in `modal-descent-status.md`.

Work in the original finitary C. Write `WI(P)` for weak inextensibility and
`WP(P)` for weak persistence. Full rigidity is `□WP(P) ∧ □WI(P)`, and C proves
`Rigid(P) → □Rigid(P)` using 4. Each type parameter below is external to the
formula schema; there is no object-language type quantifier.

## A rigid indexed family has a rigid union

Let σ and τ be admitted types, including e. Take `R:σt` and `F:στt`, and define

```
U(y) := ∃x (R(x) ∧ F(x,y)).
```

Assume R is rigid and every current R-member x has a rigid fiber F(x,−).
First seal the fiber condition. Each such x necessarily has a rigid fiber,
because rigidity is necessary. Apply WI(R) to the property
`λx.Rigid(F(x,−))`. This gives `□∀x(R(x) → Rigid(F(x,−)))`.

For persistence, at an arbitrary accessible point an instance U(y) supplies a
current witness x. Persistence of R gives `□R(x)`. The sealed fiber condition
and persistence of F(x,−) give `□F(x,y)`. Necessary existential introduction,
with the same x, gives `□U(y)`. The argument uses the necessarily available
weak persistence of R and the sealed fiber condition, so U is persistent.

For weak inextensibility at that point, let Z necessarily cover each current
U-member. For every current R-member x, every current F(x,−)-member belongs
to U and is therefore necessarily Z. WI(F(x,−)) gives
`□∀y(F(x,y) → Z(y))`. WI(R), tested on
`λx.∀y(F(x,y) → Z(y))`, then gives
`□∀x(R(x) → ∀y(F(x,y) → Z(y)))`. Existential elimination under that box gives
`□∀y(U(y) → Z(y))`. Since WI(R) and the sealed fiber condition hold at every
accessible point, U is inextensible. Thus U is rigid.

Only the root fiber-rigidity condition was assumed. No BF, choice, ND,
comprehension, or necessarily universal root domain was used.

## Direct images

For an admitted operation `f:σ→τ`, where τ is relational, put
`f[R](y):=∃x(R(x) ∧ y=f(x))`. Each fiber `λy.y=f(x)` is rigid in C:
persistence is necessity of identity; weak inextensibility follows by taking
the necessary value of a covering predicate at f(x) and transporting it
along equality. Both arguments are closed C theorems and hence hold
necessarily. The indexed-union result therefore makes `f[R]` rigid whenever
R is rigid. No injectivity or surjectivity of f is required.

The restriction on the output of f is syntactic: C has no individual-valued
function type. The preceding relational-fiber theorem still allows τ=e.

## Inverse images along necessary embeddings

Let τ be relational, `f:σ→τ`, and assume `□Injective(f)`. Let P:τt be rigid,
with every current P-member in the image of f. Put `Y(x):=P(f(x))`.

The image restriction seals itself. If P(y), choose a current a with y=f(a).
Necessity of identity and necessary existential introduction give
`□∃a(y=f(a))`. WI(P) therefore yields
`□∀y(P(y) → ∃a(y=f(a)))`. Persistence of Y follows by instantiating the
necessary weak persistence of P at f(x).

For weak inextensibility, let Z necessarily cover every current Y-member.
For each current P-member y, the image condition supplies a with y=f(a).
Then Y(a), so `□Z(a)`, and necessity of identity gives `□(y=f(a))`.
Together with necessary injectivity this yields

```
□∀x(y=f(x) → Z(x)).
```

Indeed, at each future point, f(x)=f(a) forces x=a. Test WI(P) on
`λy.∀x(y=f(x) → Z(x))`. It yields a necessary universal implication;
instantiate y=f(x) to obtain `□∀x(Y(x) → Z(x))`.
The same argument is available necessarily: P is inextensible, its image
condition is sealed, and 4 preserves necessary injectivity. Hence Y is rigid.

Finally suppose `RC_(τt)`. Given X:σt, apply it to `f[X]` and obtain a rigid
P actually coextensive with that direct image. All current P-members are
coded, so the preceding theorem gives rigidity of `P∘f`. Actual injectivity
gives `f[X](f(x)) ↔ X(x)`, so `P∘f` is actually coextensive with X. Thus

```
□Injective(f) + RC_(τt) → RC_(σt).
```

The injectivity assumption is necessarily quantified over future arguments;
mere root injectivity is not substituted for it. The haecceity construction
in the earlier modal-propagation proof is a canonical instance, where the
injection law is itself a closed theorem of C. No converse, arbitrary
inverse-image closure, or unboxed-injectivity variant is asserted here.
