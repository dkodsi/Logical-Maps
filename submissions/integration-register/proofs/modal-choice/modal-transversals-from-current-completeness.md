# Modal transversals from current Boolean completeness

26 October 2026. Ordinary mathematical argument by OpenAI Codex.
Direct source: `misc`, this note, §§1–5, unpaginated. Self-audited;
no independent review, human verification, Lean certification, or
literature-priority claim is made. Work in the fixed relational C.

## 1. Statements

For a fixed type σ, including e, let Tr_R(X) say that X contains
exactly one member of each R-equivalence class. Then

```math
\boxed{C+BC_{\sigma t}+MRC_{\sigma t,\sigma}\ \vdash\
\forall R^{\sigma\sigma t}
\bigl(\Box\mathrm{Equiv}(R)
\to\exists X^{\sigma t}\Box\mathrm{Tr}_R(X)\bigr).}
\tag{1}
```

Boolean completeness is **current and unboxed**. Neither BF, ND,
Vicinity, nor a selecting operation with output type σ is assumed.
The witness X is a necessarily valid transversal, not just a current
one.

As a consequence, with full schemas,

```math
\boxed{C+BC_{\rm all}:\qquad
MRC\ \longleftrightarrow\ \mathrm{Modal\ Well\!\!\!\!-Ordering}
\ \longleftrightarrow\ (\Box RC+IC).}
\tag{2}
```

More precisely, a single current completeness instance suffices for
each target type:

```math
\boxed{C+MRC_{(\sigma t)t,\sigma t}+BC_{(\sigma t)t}
\ \vdash\ \mathrm{Modal\ Well\!\!\!\!-Ordering}_\sigma.}
\tag{2a}
```

Thus (2a) uses just one MRC instance and one unboxed BC instance.
It does not need a separate Intensional Choice premise at the type
of order relations.

This supplies another sufficient hypothesis for the unrestricted
MRC-to-Modal-Well-Ordering problem. It does not settle that problem
without completeness, or either BC_t-plus-choice Actuality target.
In particular, BC_t is not substituted for the property-type
completeness in (1) or for the full schema in (2).

## 2. Necessarily separated properties form a chain-complete poset

Fix R with □Equiv(R). Call X:σt separated when

```math
\mathrm{Sep}_R(X):=
\Box\forall x^\sigma y^\sigma
\bigl(Xx\land Xy\land(Rx)y\to x=y\bigr).
\tag{3}
```

Order these properties by their **algebraic** order ≤, not by current
extension inclusion. This is an antisymmetric order on entities.
Bottom is separated.

Define the admitted operation

```math
(\Gamma_R B)x:=\forall y^\sigma
\bigl(By\land(Rx)y\to x=y\bigr).
\tag{4}
```

The definitions of algebraic order and necessary universal closure
give

```math
A\le\Gamma_R B
\quad\longleftrightarrow\quad
\Box\forall x y\bigl(Ax\land By\land(Rx)y\to x=y\bigr).
\tag{5}
```

Necessary symmetry of R makes the right side symmetric in A,B, so

```math
A\le\Gamma_R B\quad\longleftrightarrow\quad B\le\Gamma_R A.
\tag{6}
```

These are ordinary C deductions using the explicitly boxed symmetry
premise. They do not apply Logical Equivalence to an equivalence
proved only under that premise. The operation Γ_R is antitone, and
Sep_R(X) is equivalent to X≤Γ_R X.

Let D be any current represented chain of separated properties and
let J be its Boolean join, supplied by the single current premise
BC_(σt). For any current A,B in D, comparability and separation give
A≤Γ_R B. Indeed, if A≤B, use A≤B≤Γ_R B; if B≤A, use
A≤Γ_R A≤Γ_R B.

For fixed B, every current D-member A lies below Γ_R B. Hence
J≤Γ_R B. By (6), B≤Γ_R J. Applying the join property once more gives
J≤Γ_R J. Thus J is separated and is also the join in the separated
poset. The empty-chain join is Bottom.

This establishes exactly the current represented chain completeness
needed below. It does not assume that D remains a chain, that D's
membership persists, or that J remains a join at later evaluations.
The necessary separation of J comes instead from its algebraic
inequality J≤Γ_R J. No BF step is hidden in (5): the universal
binders are already inside the box in algebraic order.

## 3. A progressive operation which adds a missed class modally

By the [universal modal selector construction](universal-modal-selectors.md),
§2, MRC_(σt,σ) supplies S:(σt)σt satisfying

```math
\Box\mathrm{Functional}(S),\qquad
S\le\lambda F\,y\bigl(Fy\lor\neg\exists z^\sigma Fz\bigr).
\tag{7}
```

For X:σt define its property of missed points

```math
M_X(y):=\neg\exists x^\sigma\bigl(Xx\land(Rx)y\bigr),
```

and the admitted properties and operation

```math
D_X(y):=M_X(y)\land(SM_X)y,\qquad
\Phi(X):=X\lor D_X.
\tag{8}
```

At every accessible evaluation, D_X has at most one instance. If
M_X is instantiated there, D_X has exactly one instance there;
if M_X is empty there, D_X is empty there. This follows directly
from the necessary functionality and inclusion in (7).

Consequently, if X is necessarily separated, so is Φ(X). At any
accessible evaluation, two old points are covered by separation of
X; two added points are identical by the at-most-one assertion;
and an added point is R-related to no old point by its membership
in M_X. Necessary symmetry of R handles either order of the mixed
pair. Thus Φ maps the separated poset into itself. Also X≤Φ(X)
unconditionally, by its displayed disjunction.

Apply the existing represented Bourbaki–Witt/canonical-chain lemma
to this poset and Φ. Its hypotheses were proved in §2, and Φ is an
admitted operation, so its functional graph needs no further choice.
We obtain a separated X with the **entity identity**

```math
\Phi(X)=X.
\tag{9}
```

By (8)–(9), D_X≤X. But D_X≤M_X, and necessary reflexivity of R
gives □∀y(Xy→¬M_X(y)). Hence D_X is necessarily empty. By the
necessary selection assertion following (8), M_X must therefore
be necessarily empty as well. Equivalently,

```math
\Box\forall y^\sigma\exists x^\sigma
\bigl(Xx\land(Rx)y\bigr).
\tag{10}
```

Combine (10) with Sep_R(X). At every accessible evaluation X meets
each R-class exactly once. This is □Tr_R(X), proving (1).

The fixed point is an equality of property entities; it is not
merely a current coextension statement. That is what lets the
necessary selection in (7) rule out a missed class at any later
evaluation.

## 4. Full current BC closes the modal well-ordering implication

Assume full current BC and full MRC. For each σ, apply (1) at the
type σt to the relation

```math
E(F,G):=\forall x^\sigma(Fx\leftrightarrow Gx).
\tag{11}
```

H proves that E is an equivalence, so □Equiv(E) is an unconditional
C theorem. Formula (1) supplies a property T of σ-properties which
necessarily contains exactly one representative of each coextension
class. In particular □Transversal_σ holds: the same T-witness works
at every accessible evaluation. This argument is repeated at each
fixed type; it makes no object-language quantification over types.

The [universal modal selector theorem](universal-modal-selectors.md),
§§3–4, also gives □RC_all and IC_all from MRC. Necessitating the
existing, discharged C implications now gives

```math
\Box\mathrm{Transversal}_{\rm all}+\Box RC_{\rm all}
\ \Longrightarrow\ \Box TC_{\rm all}
\ \Longrightarrow\ \Box WO_{\rm all}.
\tag{12}
```

Finally, □WO+IC gives Modal Well-Ordering: choose intensionally a
unique well-order at each evaluation and take its material union,
as in the existing chooser-of-orders proof. This proves the forward
direction of (2). Modal Well-Ordering⇒MRC is already a C theorem,
and MRC↔(□RC+IC) was proved in the universal-modal-selector note.

No instance of current BC has been necessitated. Each completeness
instance is used at the starting evaluation to obtain one fixed
point whose defining entity identity and separatedness give the
modal conclusion. The later boxed implications in (12) are obtained
from unconditional C implications and explicitly boxed premises.

### The single-completeness-instance bound

For (2a), one can bypass the all-type TC/Zorn detour in (12).
The standard conforming-well-order argument uses only
Transversal_σ and RC_(σt,σ) to obtain WO_σ. Here are the details
needed to expose those types.

Transversal_σ supplies one chosen property entity for each current
coextension class of σ-properties. Use RC_(σt,σ) to choose a member
of every inhabited chosen property, with a default on empty ones.
Composing with the chosen representative of the complement of P
gives a total functional graph K(P,x) such that, whenever P is not
full, its selected x is outside P. Moreover, coextensive P,Q receive
the same x: their chosen complement representatives are identical
entities, and the RC graph is entity-functional. No operation with
output type σ has been extracted.

Call a well-order R of its own field conforming when each field
member x is K's choice from its strict predecessor property
P_(R,x). Any two conforming orders agree by initial segment.
For completeness, let I consist of the points whose closed initial
segments in both orders have the same extension and the same order.
This is an initial segment of each, and the orders agree on I.
If both orders have points outside I, take their respective least
such points x,y. Each strict predecessor property is coextensive
with I. Coherence and functionality of K give x=y; their closed
initial segments now agree as well, contradicting x∉I. Thus one
order is an initial segment of the other.

The material union W of all conforming orders is therefore an
admitted conforming well-order on its field. To check well-foundedness,
take any inhabited admitted subproperty of that field and a
conforming order containing one of its members. Its least member
within that order is least in the whole union, by initial-segment
comparison. Each point's predecessors in W are precisely its
predecessors in any conforming order containing it, so the defining
K-condition transfers by coherence. If W's field were not full,
append K's chosen point outside it at the top. The enlarged order
would be conforming and would contain a point outside the union of
all conforming orders, a contradiction. Hence WO_σ.

This proves the type-specific C implication

```math
\mathrm{Transversal}_\sigma+RC_{\sigma t,\sigma}
\ \Longrightarrow\ WO_\sigma.
\tag{13}
```

In fact the proof just given defines its well-order uniformly from
K, by the admitted formula

```math
(W_Kx)y:=\exists R^{\sigma\sigma t}
\bigl(\mathrm{Conforming}_K(R)\land(Rx)y\bigr).
\tag{14}
```

Consequently, if K is necessarily functional, necessarily coherent
on coextensive inputs, and necessarily chooses outside nonfull
inputs, then W_K is **necessarily** a well-order. To justify this
precisely, discharge those three current K-hypotheses in the proof
above, necessitate the resulting unconditional C implication, and
apply it to their boxed versions. The same admitted W_K is the
witness; no separate IC instance on well-orders is required.

Only one MRC instance is needed to construct that K. Put ρ=σt.
The premise MRC_(ρt,ρ) supplies a universal necessarily functional
membership selector S_ρ for ρ-properties. The same S_ρ, together
with BC_(ρt), gives by (1) a fixed T which necessarily selects one
representative of each coextension class of σ-properties.

It also gives a universal modal membership selector for σ itself,
by selecting **haecceity codes**. Fix any a:σ and write
H_x:=λz^σ(z=x). For F:σt set

```math
V_F(Y):=
\exists x^\sigma(Fx\land Y=H_x)
\ \lor\ (\neg\exists x^\sigma Fx\land Y=H_a),
\qquad Y:\rho.
\tag{15}
```

H proves that every V_F is inhabited, so it is necessarily so.
At every accessible evaluation S_ρ selects exactly one Y in V_F;
Y is the haecceity of an F-member when F is inhabited, and H_a
otherwise. Therefore the admitted relation

```math
Q(F,x):=\exists Y^\rho
\bigl((S_\rho V_F)Y\land Yx\bigr)
\tag{16}
```

is necessarily total and functional, and necessarily chooses an
F-member whenever there is one. This is relational decoding of a
selected singleton, including when σ=e; it does not assert an
individual-valued operation or identify a material union with a
selected entity of relational type.

Compose Q with T's necessarily unique representative of each
complement property, exactly as in the construction of K above.
The resulting single K has all three necessary qualifications used
in (14). Hence □WO(W_K). This proves (2a) using only
MRC_((σt)t,σt) and current BC_((σt)t).

## 5. Sources and exact remaining scope

- New modal-transversal construction and the unboxed-completeness
  implication: this note, §§2–4, OpenAI Codex, 26 October 2026,
  `misc`, unpaginated.
- Universal necessary membership selector: [Universal modal
  selectors](universal-modal-selectors.md), §§2–4, unpaginated.
- Represented fixed-point lemma: [Relational Choice and Boolean
  Completeness imply Actuality](../../../next-update/proofs/propositional-canonical-chain-lemmas.md),
  Appendix D, unpaginated. Its current entity-antisymmetric order
  and represented-chain hypotheses are checked in §2 above.
- Transversal+RC⇒TC: [recorded argument](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/transversal-and-relational-choice-imply-transversal-choice.yaml),
  attributed there to Christopher Sun, 26 September 2026.
- TC⇒Zorn⇒WO: the [Lewin translation](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/transversal-choice-r-implies-zorn-r.yaml)
  and [well-ordering argument](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/zorn-r-implies-well-ordering-r.yaml).
- □WO+IC⇒Modal Well-Ordering: [recorded chooser-of-orders argument](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/necessary-well-ordering-and-intensional-choice-imply-modal-well-ordering.yaml),
  attributed there to Cian Dorr, 8 October 2026.

The unrestricted MRC⇒Modal Well-Ordering and RC⇒TC questions remain
open here. So do BC_t+RC_(t,t)⇒Actuality and BC_t+Zorn_t⇒Actuality.
The theorem above is a positive implication with its exact extra
completeness hypothesis, not a countermodel or a claim that those
hypotheses follow from the original premises.
