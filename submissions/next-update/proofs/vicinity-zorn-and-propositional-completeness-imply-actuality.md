# Vicinity, propositional completeness and Zorn imply Actuality

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated.

**Over C + BC_t + Zorn_t, Actuality is equivalent to Vicinity.** This weakens the C5 premise in the earlier Zorn theorem. In particular, current propositional ND suffices; neither boxed ND nor Barcan is assumed in the original theory.

## 1. Exact statements

In the fixed finitary relational language,

```math
\boxed{C+\mathrm{Vicinity}+BC_t+Zorn_t
\ \Longrightarrow\ \mathrm{Actuality}}
\tag{1}
```

Both completeness and Zorn are current and unboxed. Zorn has carrier t, and BC_t concerns the Boolean algebra of propositions. Since Actuality implies Vicinity already over C, this gives

```math
\boxed{\text{over }C+BC_t+Zorn_t:\quad
\mathrm{Actuality}\ \longleftrightarrow\ \mathrm{Vicinity}}
\tag{2}
```

Vicinity says that some true proposition entails the possibility of every current truth. Actuality requires a true proposition entailing those truths themselves. The theorem shows that propositional completeness and Zorn close this gap.

The recorded implication ND_t⇒Vicinity also gives

```math
C+ND_t+BC_t+Zorn_t\ \Longrightarrow\ \mathrm{Actuality}
\tag{3}
```

Here ND_t is unprefixed and only propositional. We do not infer C5 for the original structure. Whether BC_t+Zorn_t alone supplies Vicinity remains unresolved.

## 2. The shared supported interpretation

Use the [construction from Vicinity](vicinity-supported-interpretation.md), §§1–5. It supplies a true support s, the idempotent retraction j_t(p)=s∧p and the supported carrier D_t=[0,s], together with C5 and current BC_t in the interpretation. It does not use Relational Choice.

For an old predicate Y on propositions its retraction satisfies

```math
j_{tt}(Y)(d)=s\land Y(j_t d)
\tag{7}
```

On fixed d, this has precisely Y's current extension, since s is true. The same holds for relations on fixed tuples. These are the only additional facts needed for the transfer below.

## 3. Zorn transfers to the supported carrier

Assume old Zorn_t. Let R be a supported preorder on D_t such that every admitted supported R-chain has a supported upper bound. Write j=j_t and define an old relation on all propositions by

```math
R'(p,q):=R(jp,jq)
\tag{8}
```

This is admitted by lambda abstraction. It is currently reflexive and transitive because j maps every old proposition into D_t and R is a preorder there.

Let X be any admitted old R'-chain. Form the old predicate

```math
Y(d):=D_t(d)\land\exists p\,[Xp\land d=jp],
\tag{9}
```

and retract it by (7). On supported d this represents precisely the current image j[X]. It is a supported R-chain. Totality and transitivity follow from the corresponding properties of X under R'. For antisymmetry, if d=jp and e=jq are current image members and both R(d,e) and R(e,d) hold, then R'(p,q) and R'(q,p) hold. Antisymmetry on X gives p=q, and therefore d=e. In particular j cannot identify two different current members of X: if jp=jq, reflexivity of R supplies both comparisons, so the same argument applies.

By the supported chain-bound hypothesis, there is a fixed v upper-bounding (9). For each p with Xp, R(jp,v) holds. Since jv=v, this is R'(p,v). Thus every old R'-chain has an old upper bound. Empty chains cause no exception: the fixed domain is inhabited and the stipulated supported chain-bound property also covers its empty predicate.

Old Zorn_t now supplies an old R'-maximal m. Put n=jm. It is supported. If a supported d satisfies R(n,d), then jd=d gives R'(m,d). Maximality yields R'(d,m), namely R(d,n). Thus n is supported R-maximal.

This proves supported Zorn_t. The proof uses neither a choice operation nor a selector of chain bounds. Every application of Zorn has carrier t. Higher predicates appear only in the admitted image formula (9) and its retraction.

## 4. Actuality and the remaining boundary

The supported interpretation now satisfies C5+BC_t+Zorn_t. Apply [Zorn and propositional completeness imply Actuality](c5-zorn-and-propositional-completeness-imply-actuality.md). It supplies a currently true supported proposition u that lies below every supported truth.

For each original true proposition q, the supported proposition s∧q is true. Hence

```math
u\le s\land q\le q
\tag{10}
```

The same u therefore witnesses original Actuality, proving (1). The converse in (2) is the existing bare-C implication Actuality⇒Vicinity. Equation (3) follows from the existing ND_t⇒Vicinity implication.

This theorem and the separately proved [C+BC_tt+Zorn_t⇒Actuality](zorn-and-higher-completeness-imply-actuality.md) make different trades: the present theorem keeps completeness at t and assumes Vicinity; the other raises completeness to tt and needs no Vicinity. Neither settles C+BC_t+Zorn_t⇒Actuality.

The parallel recorded RC theorem gives Actuality↔Vicinity over C+BC_t+RC_(t,t). The present proof transfers Zorn directly; it does not derive RC_(t,t) from Zorn_t.

## Sources

The shared construction retains the attribution to Sun and the new supported-interpretation argument. The Zorn transfer is OpenAI Codex, *Vicinity, propositional completeness and Zorn imply Actuality*, 25 October 2026, §§1–4, unpaginated. The C5 theorem and [existing converse](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/results/actuality-implies-vicinity.yaml) retain their separate attributions.
