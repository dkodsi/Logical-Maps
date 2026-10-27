# Reducing modal well-ordering to current transversal choice

OpenAI Codex, 26 October 2026. Direct source: `misc`, this note, unpaginated.

Modal Well-Ordering reduces to current Transversal Choice under full Modalized Relational Choice, with an explicit type bound for extracting a counterexample. All reasoning is in C; schemas below are proof families.

## 1. A fixed-type implication

Fix any admitted type σ, including e, and put ρ=σσt and κ=ρt.
Then

```math
C+MRC_{\rho t,\rho}\ \vdash\
\Box TC_\kappa\ \longrightarrow\ MWO_\sigma
\tag{1}
```

Here TC_κ is transversal choice for equivalence relations on κ,
and MWO_σ asserts that one admitted relation necessarily well-orders
σ. In particular, the types on the two sides of (1) differ.

First isolate the ordinary theorem used by the recorded
TC⇒Zorn⇒WO argument:

```math
C\ \vdash\
(RC_{\rho t,\rho}\land TC_{\rho t})\longrightarrow WO_\sigma
\tag{2}
```

For completeness, the type accounting is as follows. To prove
Zorn at ρ, Relational Choice chooses a strict upper bound for each
chain property of type ρt, under the assumption that the preorder
has chain bounds and no maximal element. Thus the required RC
instance has input ρt and output ρ. TC at ρt gives a transversal
of current coextension of those chain properties. Composing the
bound-selector graph with that transversal makes its values
independent of coextensive chain codes. The recorded Lewin argument
then gives Zorn_ρ. The recorded end-extension argument applies
Zorn at ρ=σσt to obtain WO_σ. Neither argument requires an operation returning the selected objects.

The [universal modal selector theorem](universal-modal-selectors.md),
§§2–4, gives both □RC_(ρt,ρ) and IC_ρ from the single premise in
(1). Necessitate the discharged C theorem (2), and use K together
with □TC_κ and □RC_(ρt,ρ). This yields □WO_σ.

Apply IC_ρ to the necessarily inhabited property λR.WO(R). It
supplies a subproperty G that is necessarily uniquely inhabited
and entails that property. Define

```math
R'(x,y):=\exists R^\rho\,[GR\land(Rx)y]
```

At each accessible evaluation R' is currently coextensive with the
unique selected well-order there. Well-ordering depends only on
the relation's current extension, so □WO(R'). This proves (1).
This is the recorded chooser-of-orders proof, with precisely IC_ρ.
No optional premise has been necessitated.

## 2. The full-schema proof obligations

The following are equivalent **provability questions**:

```math
\begin{split}
&C+MRC_{\rm all}\vdash MWO_{\rm all},\\
&C+MRC_{\rm all}\vdash TC_{\rm all}
\end{split}
\tag{3}
```

For the forward direction, MWO_σ implies current WO_σ by T, and
least representatives give TC_σ.

For the reverse direction, suppose a proof of each TC instance
from full MRC has been supplied. Each individual proof uses only
finitely many MRC instances. Discharge them as a finite conjunction
and necessitate the resulting C theorem. Full MRC supplies the
boxed versions of those instances by its established persistence
theorem. Thus it supplies □TC at every type. Apply (1), separately
for each target σ, to obtain full MWO.

Consequently a proof of the other assigned target

```math
C+RC_{\rm all}\vdash TC_{\rm all}
\tag{4}
```

would settle the modal target as well. One can either combine (4)
with MRC⇒RC and then use (3), or necessitate each finite discharged
proof of (4) and use MRC⇒□RC before applying (1).

These deductions do not prove either entailment compared in (3),
or the entailment (4). In particular they do not assert that an arbitrary
current TC assumption is necessary, or that the converse reduction
from an MRC⇒MWO proof to an RC⇒TC proof has been established.

## 3. Extracting an ordinary counterexample from a modal one

The contrapositive of (1) gives the exact local consequence

```math
C+MRC_{\rho t,\rho}+\neg MWO_\sigma
\ \vdash\ \Diamond\neg TC_{(\sigma\sigma t)t}
\tag{5}
```

To see its modal content directly, IC_ρ and failure of MWO_σ force
failure of □WO_σ, by the chooser-of-orders argument. Thus there is
possibly a failure of ordinary WO_σ. Necessary RC_(ρt,ρ) remains
available there, and (2) then forces failure of TC_(ρt).

In a modal model satisfying full MRC at the evaluation point, its
full persistence theorem makes every MRC instance true at every
accessible point. Therefore any countermodel to MRC⇒MWO contains
an accessible point satisfying full MRC, hence full RC, and failing
TC at the explicit type in (5). No assumption that future entities
are images of current entities is needed. For presentations without
explicit worlds, (5) is the syntactic possibility conclusion; the
reachable-point wording concerns a modal presentation of a model.

Conversely, a point satisfying full MRC and failing TC_σ already
fails MWO_σ, since MWO_σ implies TC_σ. Thus a search for a
full-MRC counterexample can target failure of ordinary TC directly.
An arbitrary RC/TC countermodel is not thereby shown to satisfy
MRC.

## Sources

- Direct source for the reductions and type accounting: this note,
  OpenAI Codex, 26 October 2026, `misc`, §§1–3, unpaginated.
- [Universal modal selectors and MRC persistence](universal-modal-selectors.md),
  §§2–4.
- [TC⇒Zorn](../../../../logical-maps/topics/classicism/results/transversal-choice-r-implies-zorn-r.yaml):
  the recorded C translation of Jonathan Lewin's argument,
  *A Simple Proof of Zorn's Lemma*, pp. 353–354.
- [Zorn⇒WO](../../../../logical-maps/topics/classicism/results/zorn-r-implies-well-ordering-r.yaml):
  the recorded end-extension proof, explicitly at σσt.
- [□WO plus IC⇒MWO](../../../../logical-maps/topics/classicism/results/necessary-well-ordering-and-intensional-choice-imply-modal-well-ordering.yaml):
  the recorded proof attributed to Cian Dorr, 8 October 2026.
- [WO⇒TC](../../../../logical-maps/topics/classicism/results/well-ordering-r-implies-transversal-choice-r.yaml):
  the recorded least-member argument at the same type.
