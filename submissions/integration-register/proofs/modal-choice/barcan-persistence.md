# Barcan persistence of modal choice

26 October 2026. Ordinary mathematical proof by OpenAI Codex.
Direct source: `misc`, this note, §§1–4, unpaginated. No independent
review, human verification, or Lean certification is claimed.

Work in fixed finitary relational C. All type variables are external
schema parameters. Every admitted type is inhabited. The proofs use
only C's unconditional modal laws and the displayed current premises.

## 1. An entailing form of Intensional Choice

For F:σt write I(F):=∃x Fx and U(F):=∃!x Fx. The usual instance is

```math
IC_\sigma:\quad
\forall F^{\sigma t}\,[\Box I(F)\to
\exists G^{\sigma t}(G\le F\land\Box U(G))].
```

Over C it is equivalent to

```math
IC^*_{\sigma}:\quad
\forall F^{\sigma t}\exists G^{\sigma t}
[G\le F\land\Box(I(F)\to U(G))].
\tag{1}
```

The reverse implication is immediate by K. For the forward direction,
given F let F′(x):=Fx∨¬I(F). H proves I(F′), since σ is inhabited.
Hence C proves □I(F′). Apply IC_σ to obtain H≤F′ with □U(H), and
put G:=λx(Hx∧Fx). The bound G≤F is unconditional. Necessarily, wherever
I(F) holds, F′ and F have the same extension. There H≤F and G has
the same extension as the uniquely instantiated H. Thus
□(I(F)→U(G)). All identities used to define the Boolean intersection
are unconditional instances of H equivalence; no optional equivalence
is passed to Logical Equivalence.

## 2. Positive boxed witnesses persist

For any formula A(x,y), C proves

```math
(\exists y\,\Box A(x,y))\to
\Box\exists y\,\Box A(x,y).
\tag{2}
```

Indeed, fix a witness y. Axiom 4 gives □□A(x,y). Necessitated
existential introduction and K give □∃z□A(x,z). Discharge the witness
using ordinary existential elimination. This uses persistence of a
current witness under C's logic; it does not require BF.

Consequently, if P(x) is an existentially quantified finite conjunction
of boxed tests, C proves P(x)→□P(x). Under the single Barcan instance
BF_α for the type of x,

```math
\forall x^\alpha P(x)\quad\Longrightarrow\quad
\forall x^\alpha\Box P(x)\quad\Longrightarrow\quad
\Box\forall x^\alpha P(x).
\tag{3}
```

No ND premise is needed: there is no negative boxed test outside a
box in this formulation.

## 3. Type-specific persistence theorems

In (1), G≤F is the boxed universal implication □∀x(Gx→Fx).
Its conjunction with the other boxed test is a single boxed matrix.
Thus (2)–(3) yield

```math
\boxed{C+BF_{\sigma t}\ \vdash\
IC_\sigma\leftrightarrow\Box IC_\sigma.}
\tag{4}
```

To pass between IC and IC*, use the unconditional C equivalence from
§1, and its necessitation. Only BF at σt is used, not BF at σ or t.

For Modalized Relational Choice use the existing entailing form

```math
\forall R^{\sigma\tau t}\exists S^{\sigma\tau t}
\left[S\le R\land
\Box\forall x^\sigma
\left((\exists y^\tau\,(Rx)y)\to
\exists y^\tau\big((Sx)y\land
\forall z^\tau((Sx)z\to y=z)\big)\right)\right].
\tag{5}
```

The same positive-boxed-witness argument gives

```math
\boxed{C+BF_{\sigma\tau t}\ \vdash\
MRC_{\sigma,\tau}\leftrightarrow\Box MRC_{\sigma,\tau}.}
\tag{6}
```

The reverse directions of (4) and (6) are T. Their forward directions
do not assert rigidity of the negations. In particular, this proof
does not establish ¬IC→□¬IC or ¬MRC→□¬MRC under BF alone.

Equations (4) and (6) remove ND_t from the corresponding positive
propagation results in the earlier choice-proof-simplifications note.
That earlier note's stronger claim about both truth and falsity
retains its own hypotheses.

With full BF, the existing chooser-of-graphs theorem now gives, over C,

```math
\boxed{MRC_{\rm all}\ \longleftrightarrow\
\Box RC_{\rm all}+IC_{\rm all}
\ \longleftrightarrow\
\Box RC_{\rm all}+\Box IC_{\rm all}.}
\tag{7}
```

**Later strengthening in this pass:** the [universal-modal-selector
theorem](universal-modal-selectors.md) proves (7), and MRC↔□MRC,
already over bare C without BF. The BF argument above remains a
type-specific proof using only the same isolated MRC instance.

**Later separation in this pass:** the
[finite-support absorbing-entrance model](absorbing-entrance-finite-support-pairs.md)
is an explicit ZFC model satisfying full IC but failing □IC_e.
It even satisfies □BF_e and □ND_e, while failing the relevant
predicate-level BF_(et). Thus IC does not share full MRC's
unconditional positive propagation, and the subscript in the
positive BF bound matters. The earlier choiceless full-model
variant is retained separately with failure at IC_t.

Here sums denote conjunctions of schemas; each box is applied to the
closed instance. For the forward direction, (6) makes each MRC
instance necessary, and the necessary instances of the established
MRC⇒RC and MRC⇒IC implications apply. For the reverse direction use
the existing theorem □RC+IC⇒MRC. This does not replace □RC by RC.

## 4. Sources

- Entailing MRC: [the merged native definition](../../../../logical-maps/topics/classicism/principles/modalized-relational-choice-r.yaml),
  variant `entailing`; Cian Dorr's formulation of 11 October 2026.
- The earlier ND_t+BF persistence bounds: [Choice, atom tests and
  necessity](../../../next-update/proofs/choice-proof-simplifications.md),
  §3, unpaginated.
- Chooser of graphs: [□RC and IC imply MRC](../../../../logical-maps/topics/classicism/results/necessary-relational-choice-and-intensional-choice-imply-modalized-relational-choice.yaml),
  proof attributed there to Cian Dorr, 11 October 2026.
- New entailing IC formulation and removal of ND from positive
  propagation: this note, §§1–3, `misc`, unpaginated.
