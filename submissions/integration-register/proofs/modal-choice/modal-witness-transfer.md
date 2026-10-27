# Transferring modal witnesses through relational profiles

OpenAI Codex, 26 October 2026. Direct source: `misc`, this note, unpaginated.

## 1. An extensional-input transfer lemma

Let θ=α₁…αₙt be any relational type, including t when n=0.
Write A≈A′ for current coextension at θ. Let Φ(A,b) be a formula,
possibly with fixed parameters, for which C proves

```math
A\approx A'\ \longrightarrow\
\bigl(\Phi(A,b)\leftrightarrow\Phi(A',b)\bigr).
\tag{1}
```

Here b can be a finite tuple of admitted types. Assume the current
instance IC_θ. Then

```math
\boxed{\quad
\forall A^\theta\exists b\,\Box\Phi(A,b)
\ \longrightarrow\
\Box\forall A^\theta\exists b\,\Phi(A,b).
\quad}
\tag{2}
```

This is not unrestricted Barcan or an operation returning a selected
entity. The extensional-input condition (1) is essential to the proof.

Define

```math
B(A):=\neg\exists b\,\Phi(A,b),\qquad
P(A):=B(A)\lor\neg\exists A'\,B(A').
```

H proves ∃A P(A): if a bad input exists choose one, and otherwise
every input is permitted. Necessitating this unconditional theorem
gives □∃A P(A). IC_θ therefore supplies G:θt with G≤P which is
necessarily uniquely instantiated.

Form the admitted relational profile

```math
\widehat A[\bar x]:=
\exists A^\theta\bigl(GA\land A[\bar x]\bigr).
\tag{3}
```

For θ=t, (3) simply means Â=∃A(GA∧A). At each accessible
evaluation, if A is the unique G-instance, Â≈A. This is ordinary
material quantifier reasoning at that evaluation; it asserts no
identity of Â and A and no algebraic-join description of (3).

Apply the antecedent of (2), at the starting evaluation, to the
single entity Â. Obtain b with □Φ(Â,b). Now reason at an arbitrary
accessible evaluation. If a bad input exists there, G's unique
instance A satisfies B(A), since G≤P. But Â≈A there, so (1) and
Φ(Â,b) give Φ(A,b), contradicting B(A). Thus no bad input exists
at any accessible evaluation, proving (2).

The only necessitated implications are unconditional C theorems,
including (1). Neither the antecedent of (2) nor current IC has
been necessitated. The witness b is obtained once at the starting
evaluation and remains available for the modal argument.

### The converse for a relational output

Suppose b is one variable of a relational type η, C also proves
that Φ is invariant under current coextension in b, and IC_η holds.
Then the converse of (2) holds as well. Given
□∀A∃b Φ(A,b), fix any current A. Necessary universal instantiation
gives □∃b Φ(A,b). IC_η supplies a necessarily singleton property
of b-entities entailing Φ(A,−). Its material profile b̂ is coextensive
with its selected b at each accessible evaluation. Output
extensionality therefore gives □Φ(A,b̂).

Consequently, under IC_θ+IC_η and the two extensionality conditions,

```math
\forall A^\theta\exists b^\eta\Box\Phi(A,b)
\quad\longleftrightarrow\quad
\Box\forall A^\theta\exists b^\eta\Phi(A,b).
\tag{2a}
```

This converse is not asserted for individual-valued outputs: the
relational profile operation is precisely what makes it possible.

## 2. Conditional modal transversals for arbitrary relations

Fix any type σ, including e. The existing
[modal-transversal construction](modal-transversals-from-current-completeness.md),
§§2–3, proves

```math
C+BC_{\sigma t}+MRC_{\sigma t,\sigma}:\qquad
\Box\mathrm{Equiv}(R)
\ \longrightarrow\ \exists X\,\Box\mathrm{Tr}_R(X).
\tag{4}
```

Its necessary-equivalence hypothesis can be removed by retaining
equivalence as a condition inside the output box. For arbitrary R,
define

```math
(\widehat R x)y:=
\bigl(\mathrm{Equiv}(R)\land(Rx)y\bigr)
\lor\bigl(\neg\mathrm{Equiv}(R)\land x=y\bigr).
\tag{5}
```

H proves that R̂ is an equivalence: where R is an equivalence it
has R's current extension, and otherwise it has the identity
relation's extension. Consequently □Equiv(R̂) is a C theorem.
Applying (4) gives one X with □Tr_R̂(X). At every evaluation where
Equiv(R) holds, R̂ and R are coextensive, so the same X is a
transversal of R. Therefore

```math
\boxed{C+BC_{\sigma t}+MRC_{\sigma t,\sigma}\ \vdash\
\forall R^{\sigma\sigma t}\exists X^{\sigma t}
\Box\bigl(\mathrm{Equiv}(R)
\to\mathrm{Tr}_R(X)\bigr).}
\tag{6}
```

In particular, these premises imply current TC_σ even when the
given equivalence R is not necessarily an equivalence. Formula (5)
is a material qualification of a relation; it does not identify R̂
with R as an entity under an optional hypothesis.

## 3. One unboxed completeness instance gives necessary TC

Take θ=σσt and

```math
\Phi(R,X):=\mathrm{Equiv}(R)\to\mathrm{Tr}_R(X).
```

The formula Φ depends only on R's current extension. H proves (1)
for this Φ, directly from the definitions of equivalence and
transversal. Combine (6) with the transfer lemma:

```math
\boxed{C+BC_{\sigma t}+MRC_{\sigma t,\sigma}+IC_{\sigma\sigma t}
\ \vdash\ \Box TC_\sigma.}
\tag{7}
```

Thus, with the full MRC schema,

```math
\boxed{C+MRC_{\rm all}+BC_{\sigma t}
\ \vdash\ \Box TC_\sigma.}
\tag{8}
```

Full MRC supplies the required IC instance by the
[universal-selector theorem](universal-modal-selectors.md), §§2–4.
Formula (7) states the extra IC type explicitly; the single instance
MRC_(σt,σ) is not asserted to supply IC_(σσt).

Completeness remains current and unboxed. Its role is to obtain
modal witnesses for the current input relations in (6). Intensional
Choice and the profile argument then cover future inputs as well,
without a Barcan premise or a claim that every future relation has
a current entity preimage.

There is also an exact characterization independent of completeness.
Under IC_(σσt)+IC_(σt), the conditional modal-transversal statement
in (6) is equivalent to □TC_σ, by (2a): the transversal condition
depends only on the current extensions of both R and X. This
equivalence isolates the choice of future witnesses from the
separate question of constructing them in the first place.

## 4. Scope and sources

Equations (2), (6), and (7) are the positive results of this note.
They sharpen the modal scope of the existing completeness argument;
they do not remove its completeness premise. In particular, (8)
at σ=t uses BC_tt, not BC_t. No unrestricted MRC⇒Modal
Well-Ordering, RC⇒TC, or BC_t-plus-choice⇒Actuality conclusion is
claimed. All three terminal research targets remain unresolved.

- New transfer lemma and its application: this note, §§1–3,
  OpenAI Codex, 26 October 2026, `misc`, unpaginated.
- Modal-transversal existence from unboxed completeness:
  [Modal transversals from current Boolean completeness](modal-transversals-from-current-completeness.md),
  §§2–3, unpaginated; this is an ordinary self-audited proof.
- Intensional Choice and its exact type convention:
  [principle record](../../../../logical-maps/topics/classicism/principles/intensional-choice-r.yaml).
- MRC's cross-instance consequences:
  [Universal modal selectors](universal-modal-selectors.md), §§2–4,
  unpaginated.
