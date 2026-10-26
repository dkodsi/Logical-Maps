# Vicinity, Relational Choice and propositional completeness imply Actuality

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated.

The sharp theorem uses only the single Relational Choice instance with propositional inputs and outputs:

```math
C+\mathrm{Vicinity}+BC_t+RC_{t,t}\ \Longrightarrow\ \mathrm{Actuality}.
```

All three added premises are unprefixed. The [shared supported interpretation](vicinity-supported-interpretation.md) supplies C5 and preserves BC_t. We transfer RC_{t,t} to that same interpretation and apply the [C5 Relational Choice theorem](c5-relational-choice-and-propositional-completeness-imply-actuality.md).

## 1. Transferring Relational Choice

More generally, fix any old RC_(σ,τ) instance. Let U be a supported relation currently serial on D_σ×D_τ. The old relation

```math
R(x,y):=D_\tau(y)\land U(j_\sigma x,y)
```

is serial on all old x: j_σx is fixed, and supported seriality supplies a fixed y. Old RC gives a current total functional subrelation K of R. Retract K to S:=j_(στt)(K). On fixed arguments,

```math
S(x,y)=s\land K(x,y),
```

so S has precisely K's current membership there. Its selected outputs are fixed because K is contained in R. It is therefore a supported total functional subrelation of U, where functional uniqueness uses equality of fixed entities. In particular, old RC_(t,t) alone transfers to the instance required by the C5 theorem.

## 2. Descending Actuality

The shared construction and §1 supply C5, RC_(t,t) and BC_t in the supported interpretation. The already proved [strict-partition reconstruction theorem](c5-relational-choice-and-propositional-completeness-imply-actuality.md), §§1–8, therefore supplies a true supported Actuality witness u∈D_t.

For every original true proposition q, the proposition s∧q belongs to D_t and is currently true. Supported Actuality gives

```math
u\le s\land q\le q
```

in the original algebra. Thus this same u is an original Actuality witness. This proves the theorem. Choice and completeness were used only at their original current evaluation; neither was transported by necessitation.

## 3. Equivalence and remaining question

Since Actuality implies Vicinity over C,

```math
C+BC_t+RC_{t,t}\ \vdash\ \mathrm{Actuality}\leftrightarrow\mathrm{Vicinity}.
```

The existing [ND at t implies Vicinity](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/results/distinctness-necessary-t-implies-vicinity.yaml) also makes unprefixed propositional ND a sufficient premise. The [shared construction, §6](vicinity-supported-interpretation.md#6-vicinity-and-persistent-propositions) characterizes Vicinity by a greatest proper persistent proposition. Deriving Vicinity from BC_t and RC_{t,t} alone remains open.

The [Zorn theorem](vicinity-zorn-and-propositional-completeness-imply-actuality.md) uses the same interpretation and a separate transfer argument.
