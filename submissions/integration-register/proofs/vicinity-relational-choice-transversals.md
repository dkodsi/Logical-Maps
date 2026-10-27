# Vicinity suffices for Relational Choice to imply Transversal Choice

Ordinary mathematical research by OpenAI Codex, 26 October 2026. Direct
source: `misc`, this note, §§1–5, unpaginated. This is a new argument from
the two earlier research proofs cited below. It has been self-audited in
this pass; no independent review, human verification, Lean certificate,
or literature-priority claim is asserted.

## 1. Statement and dependencies

For every fixed type σ in the original relational language,


```math
\boxed{C+\mathrm{Vicinity}+RC_{(\sigma t),\sigma}
       \ \Longrightarrow\ TC_\sigma.}
\tag{1}
```


The RC instance is current and unboxed. No Boolean Completeness,
Actuality, observer separation, Barcan, or Functionality is added to the
ambient premises. In particular,


```math
\boxed{C+\mathrm{Vicinity}+RC_{\rm all}\Longrightarrow TC_{\rm all}.}
\tag{2}
```


The dependencies are the following ordinary mathematical proofs, with
their exact scopes retained:

1. [The supported C5 interpretation from Vicinity](../../next-update/proofs/vicinity-supported-interpretation.md), §§1–4: the true-core bound law and supported interpretation of C5. These use Vicinity alone. Section 4 below proves the required current-RC transfer.
2. [Strict local sections, crisp chains, and Relational
   Choice](../../next-update/proofs/c5-relational-choice-implies-transversal-choice.md),
   §§1–4: C5 + RC_((αt),α) implies TC_α, for every type α, including e.

The extra step here is to rebase the source individual sort to the
*entire original σ carrier* before using the supported interpretation.
This ensures that the obtained transversal is about every original
σ-entity, rather than only the fixed part of a retraction of σ.

## 2. Rebase the individual sort

Fix σ. Use a fresh copy of the relational type grammar, with base sorts
e₀ and t₀, and define its interpretation in original types by


```math
\iota(e_0)=\sigma,\qquad \iota(t_0)=t,\qquad
\iota(\alpha\beta)=\iota(\alpha)\iota(\beta).
\tag{3}
```


This respects the type restriction: an arrow in the source has codomain
different from e₀, so its interpreted codomain is t or an original
relational type, never e. The image of e₀ itself may be e; in that case
there is still no source operation with individual codomain.

Choose the true core s supplied by Vicinity, as in dependency 1:


```math
A_w=\forall r^t\,(r\to w\le\Diamond r),\qquad s=w\land A_w.
\tag{4}
```


The cited true-core lemma holds at every original argument type τ:


```math
\forall x^\tau\,(s\le F(x))\quad\Longrightarrow\quad
s\le\forall x^\tau F(x).
\tag{5}
```


It also proves that s decides every current identity of original
entities: s∧(a=b) is s when a=b and is 0 otherwise. These facts do not
depend on interpreting the source individual sort specifically as e.

Define the retractions indexed by *source* types:


```math
j_{e_0}(x)=x,\qquad j_{t_0}(p)=s\land p,\qquad
j_{\alpha\beta}(F)=\lambda x^{\iota(\alpha)}\,
 j_\beta(F(j_\alpha x)).
\tag{6}
```


The first clause is an identity substitution convention; it need not be
an admitted σσ operation. Thus (6) also works for σ=e. Each other
displayed operation has an admitted original type. The structural
β-reduction and lower-type identity substitution in dependency 1, §2,
prove whole idempotence of each j.

Let D_α be its fixed-point domain. In particular,


```math
D_{e_0}=\text{the entire original }\sigma\text{ carrier},\qquad
D_{t_0}=[0,s],\qquad
j_{e_0t_0}(X)=\lambda a^\sigma\,s\land X(a).
\tag{7}
```


The type map need not be injective. If σ=t, for example, both source
base sorts map to original t, but D_e₀ is all original propositions and
D_t₀ is [0,s]. There is no contradiction: the domains and retractions
are indexed by source sorts, and a many-sorted interpretation may use
different definable domains in the same original carrier. They must
not be identified merely because their original types coincide.

## 3. The rebased structure satisfies C5

On fixed domains use restricted application, relative equality
s∧(x=y), endpoints 0,s, relative complement s∧¬p, and quantifiers


```math
\exists^s x\,F(x)=s\land\exists x^{\iota(\alpha)}F(j_\alpha x),
\qquad
\forall^s x\,F(x)=s\land\forall x^{\iota(\alpha)}F(j_\alpha x).
\tag{8}
```


Their current truth is precisely quantification over D_α, because D_α
is the image of j_α and s is true. Equation (5) makes the quantified
values the actual joins and meets of the fixed-domain ranges in [0,s].

The H and strict Logical Equivalence verification is exactly dependency
1, §3, with original type τ there replaced by ι(α) at each source sort.
To spell out the relevant side condition, translate variables through
their j's and abstractions by projected arguments and outputs. For a
finite source H derivation, collect the required whole idempotence and
logical-operation identities in a finite positive-identity guard E.
Under E∧s the H derivation relativizes to the images; outside s both
translated proposition matrices are false. Thus an H-theorem
Φ↔Ψ gives the original H-theorem


```math
(E\land\Phi^s)\leftrightarrow(E\land\Psi^s).
\tag{9}
```


Original Logical Equivalence applies to (9). The actual identities in
E make E literally Top by C's NI theorem, so entity substitution
removes the guard. No equivalence conditional on Vicinity is fed into
Logical Equivalence. The rebasing changes types, not this argument.

For each source sort, the relative identity of two fixed entities is
0 or s by the identity-decision property following (5). Consequently
the ND matrix for each pair has relative value s. The quantifier bound
law makes its universal closure literally s as well; its relative box
is s. This gives *boxed all-type ND* in the interpreted source, hence
C5, rather than merely its unboxed ND instances. This does not assert
any corresponding original C5 or ND premise.

## 4. Transfer choice, obtain a transversal, and descend it

Let U be a supported relation currently serial from D_(e₀t₀) to
D_e₀. Its original type is (σt)σt. The original admitted relation


```math
V(X,a):=U(j_{e_0t_0}(X),a)
\tag{10}
```


is serial on the entire original (σt) carrier: the projected input is
fixed, and the output domain is all original σ. Apply precisely
RC_((σt),σ), obtaining a current total functional subrelation K⊆V.
Its supported projection is


```math
L(X,a):=s\land K(j_{e_0t_0}(X),a).
\tag{11}
```


This is fixed at the source relation type by idempotence. On fixed X
its current membership agrees with K(X,a), so it is total, single
valued, and contained in U. Relative equality of outputs has the same
current truth as original entity equality. Thus the source satisfies
RC_((e₀t₀),e₀). No other RC instance has been transferred or used.

Now take any original current equivalence R on σ and put


```math
R^s(a,b):=s\land R(a,b).
\tag{12}
```


This is a supported equivalence on D_e₀ with exactly R's current
extension. The interpreted source satisfies the hypotheses of
dependency 2 at α=e₀. It therefore supplies a fixed property F of
source type e₀t₀ meeting each R^s-cell exactly once.

The same F is an original admitted property of type σt. The source
individual domain contains every original σ-entity; current equality,
membership, and R^s agree with original equality, F-membership, and R.
Hence F meets every original R-cell exactly once. This proves TC_σ.
There is no selection of representatives of a quotient, no restriction
of the target equivalence to a smaller carrier, and no descent across
coextensive codes. This proves (1) and (2).

## 5. Consequences and scope

By the recorded unboxed ND_t⇒Vicinity theorem, (1) also gives


```math
C+ND_t+RC_{(\sigma t),\sigma}\Longrightarrow TC_\sigma.
\tag{13}
```


In particular the all-type C5 premise can be replaced by unboxed
propositional ND. At σ=t the required RC instance in (1) and (13) is
RC_(tt,t); it is **not** RC_(t,t).

Combining (2) with the already established bare-C choice implications
gives, over C+Vicinity,


```math
RC_{\rm all}\ \longleftrightarrow\ TC_{\rm all}
\ \longleftrightarrow\ Zorn_{\rm all}
\ \longleftrightarrow\ WO_{\rm all}.
\tag{14}
```


These are schema-level equivalences, not identifications of their
single-type instances. In fact the family of instances
RC_((σt),σ), as σ varies, suffices for the forward implication.

Any model separating all-type RC from all-type TC must therefore fail
Vicinity, and must fail unboxed ND_t. Equivalently, by dependency 1,
§6, its persistent propositions cannot have a greatest proper member.

Bare C+RC⇒TC remains unresolved. The theorem does not derive Vicinity
from RC, does not derive Actuality without the additional completeness
premises, and does not settle either bare-C Actuality question.
