# Endpoint separation and Infinitary Comprehension characterize full standard models

**Lean certified.** In the specified infinitary language, λ-free H together with full typed endpoint-valued observer separation and actual Infinitary Comprehension yields the full standard relational hierarchy. The representation preserves the original typed carriers, application, current truth and complete values of original formulas. Full standard hierarchies satisfy the same schemas conversely.

The domains are represented as

```math
D_e=A,\qquad D_t\cong\mathcal P(W),\qquad
D_{\sigma\tau}\cong D_\tau^{D_\sigma}\quad(\tau\ne e),
```

with nonempty individuals and worlds and a designated actual world. Fullness concerns all functions with relational output; no individual-valued function type is added.

## 1. The language and schemas

Use the original closed relational types and concrete λ-free H syntax, with ordinary classical truth and substitution clauses. Retain H's definitions of Top, Bottom and $`\Box B=(B=\top)`$. The base includes theorem-only necessity of its explicitly stated ordinary logical schemas. Optional hypotheses are not thereby necessitated.

Admit arbitrary well-founded infinitary conjunctions and disjunctions, with simultaneous typed parameters, within the universe of the interpretation. Relation arities and object-quantifier blocks remain finite. Formation supplies proposition denotations for formed matrices under assignments.

Actual Infinitary Comprehension says

```math
\exists R^{\bar\sigma t}\, .\,
\Box\forall\bar x\, .\,
\bigl(R[\bar x]\leftrightarrow B(\bar x)\bigr),
```

for every formed matrix and every assignment of its other parameters, with fresh $`R`$. The tuple may be empty. This is the actual schema, not an assumed boxed schema.

Without primitive abstraction, express identity of composite operations by common representatives. Put

```math
\mathrm{Rep}_{\bar v}(R,B)=
\Box\forall\bar v\, .\,(R[\bar v]\leftrightarrow B),
```

```math
\mathrm{Same}_{\bar v}(B,C)=
\exists R\, .\,
\bigl(\mathrm{Rep}_{\bar v}(R,B)\land
\mathrm{Rep}_{\bar v}(R,C)\bigr).
```

For each finite type list $`\Delta`$, require Boolean preservation and universal/existential quantifier preservation at its types in this common-representative form. Retain the translated equality guards

```math
\forall x^\sigma\, .\,E(x=x),\qquad
\forall x,y^\sigma\forall F^{\sigma t}\, .\,
E(x=y)\to\bigl(E(Fx)\to E(Fy)\bigr).
```

Endpoint observers also satisfy $`\forall p\, .\,(Ep=\top\lor Ep=\bot)`$. Full typed separation requires, for every relational $`\tau=\bar\sigma t`$ and finite $`\Delta`$,

```math
\forall X,Y^\tau\, .\,
X=Y\ \leftrightarrow\
\forall E^{tt}\, .\,
\bigl((\mathrm{Good}_\Delta(E)\land\mathrm{End}(E))
\to\forall\bar x\, .\,
(E(X[\bar x])\leftrightarrow E(Y[\bar x]))\bigr).
```

Types and finite lists index the schema externally. At this H starting point separation is required at every relational type. After reconstruction, common representation becomes identity of the corresponding whole operations.

## 2. Finite Comprehension reconstructs the finite logic

Common representation entails agreement in truth. Boolean preservation makes qualified observers accept Top and reject Bottom. If $`p=\top`$ and $`(p\to q)=\top`$, every observer accepts $`q`$; separation from Top yields $`q=\top`$. This gives K. Likewise, necessary equivalence makes observers agree, and separation yields propositional Intensionality.

Necessitated ordinary universal instantiation and K turn necessary universal coextension into necessary equivalence at each current argument tuple. Propositional Intensionality identifies the values; full relational separation then identifies the relations. Pointwise identities similarly yield Functionality. No abstraction is used in these steps.

For a finite Comprehension witness, boxed instantiation and Intensionality upgrade its defining equivalence to the exact application law

```math
R[\bar a]=B(\bar a).
```

For relational-valued bodies, saturate their finite output argument tuple and use typed Intensionality. Representatives are unique. This supplies the finite logical operations and abstraction with its conversion laws, recovering C with its original H-theoremhood gate. The finite matrix $`p=\top`$ supplies the necessity operation. Uniqueness also identifies the common-representative qualification with whole-operation preservation.

The infinitary box/meet law follows from necessitated infinitary projections and the all-Top logical theorem, using recovered K. It is derived rather than assumed.

## 3. Endpoint observers give stable worlds

An endpoint separator sends distinct propositions to opposite endpoints. Necessary identity preserves those output identities, giving ND at $`t`$. Quantifier preservation gives BF at $`t`$; the established implication from these two principles supplies C5.

A qualified endpoint observer determines the diagonal

```math
a_E=\forall p^t\, .\,(Ep\to p).
```

Quantifier preservation and $`E(Ep)=Ep`$ give $`E(a_E)=\top`$, so the diagonal is nonbottom. Necessitated instantiation makes it entail every accepted proposition and the negation of every rejected one. Thus it is an atom. Separating a nonbottom proposition from Bottom supplies an atom beneath it.

Let $`W`$ be all proposition atoms. The construction gives a unique currently true atom $`w_0`$ and the faithful representation

```math
\beta_\tau(R)=
\{(w,\bar a):w\in W,\ w\le R[\bar a]\}.
```

Finite qualification lists cover the same worlds, and the translated equality clauses supply rigid typed equality. Atom observers give the quantifier truth clauses; Functionality and separation make the representation faithful. Current truth is evaluation at $`w_0`$, and necessity ranges over all worlds. At this stage the admitted domains can still omit subsets and functions.

## 4. Formation and IC fill the hierarchy

Infinitary logical formation and the derived box/meet law give genuine Boolean meets and joins. An atom lies below a join exactly when it lies below one of its members. Hence arbitrary formed disjunctions and conjunctions have their usual truth clauses at every atom world.

For every $`U\subseteq W`$, the proposition $`\bigvee_{w\in U}w`$ has exactly support $`U`$, uniquely by Intensionality. This fills the proposition domain. For a relation support $`U\subseteq W\times\prod_iD_{\sigma_i}`$, use IC on

```math
B_U(\bar x)=
\bigvee_{(w,\bar a)\in U}
\left(w\land\bigwedge_i x_i=a_i\right).
```

Rigid equality makes its support exactly $`U`$. Comprehension supplies one relation collecting these values at every world and tuple, and Intensionality gives uniqueness.

For an arbitrary function $`f:D_\sigma\to D_\tau`$, write $`\tau=\bar\rho t`$ and take the support

```math
U_f=\{(w,x,\bar y):w\le f(x)[\bar y]\}.
```

Its representing relation has type $`\sigma\tau`$ and agrees with $`f`$ at every input, world and remaining argument tuple. Intensionality identifies the values, proving full function representation.

Primitive quantifiers over new infinitary matrices also have the required interpretation. IC supplies an exact representative $`R`$ of $`B(x)`$. Necessitated binder congruence and K give necessary equivalence between $`\forall x\, .\,Rx`$ and $`\forall x\, .\,B(x)`$; Intensionality identifies their values. The established quantifier clause for $`R`$ therefore applies to the original matrix. The existential case is dual. Structural induction preserves complete formula values throughout the well-founded syntax.

Conversely, the full standard hierarchy admits endpoint readers at every world. They preserve the logical operations and separate all relation intensions. Well-founded interpretation supplies every infinitary matrix's truth function, and fullness supplies its curried IC representative. This proves the converse in the same language.

## 5. Certificate and metatheory

The main declarations are `HOriginalTheorem.full_standard_representation`, `original_carriers_preserved`, `original_syntax_interpretation`, and `HStandard.full_standard_satisfies`. The syntax interpretation and grounding of auxiliary indices to original closed types are proved. No additional C, Intensionality, ND, fullness, matrix-interpreter or auxiliary-type schema hypothesis remains.

The [certificate](../certificates/endpoint-ic-full.json) identifies the exact starting theory, declarations, source closure and successful audit. Its [42 source files](../certificates/endpoint-ic-full-sources.zip) include both directions and the original-language connections. All 41 principal axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.

This is certification in Lean's classical metatheory. The separate ordinary argument that the positive representation works in ZF is not a choice-free Lean certificate, and the result is not completeness for an infinitary proof calculus.

Mathematical development and formalization: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), `endpoint-development.md`, §§1–4, and the full endpoint acceptance receipt; unpaginated. The [source manifest](../evidence/source-manifest.json) records the exact versions. Earlier finite reconstruction and endpoint arguments retain their attribution in the source development.
