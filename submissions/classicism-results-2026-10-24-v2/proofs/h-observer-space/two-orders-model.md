# Full function model with diamond meet and chain join

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–5, unpaginated.

Conjoining two separation principles is weaker than requiring one separating class to satisfy both qualifications. This distinction persists with full typed separation, endpoint-valued observers, all-type equality fixing and all quantifier instances. The following eight-proposition model proves it.

## 1. Construction

Let L={0,a,b,1}. Give L two orders: the diamond order with incomparable a,b, and the chain order 0<a<b<1. Write ∧d for diamond meet, ∨c for chain join, and c for diamond complementation, which interchanges 0 with 1 and a with b.

Take a nonempty individual domain, D_t=2×L, and the full function space at every higher relational type. Application and lambda abstraction are ordinary function application and abstraction. A proposition (i,l) is true just when i=1. Interpret the primitives by

```math
\begin{aligned}
(i,l)\land(j,m)&:=(i\land j,l\land_d m),\\
(i,l)\lor(j,m)&:=(i\lor j,l\lor_c m),\\
\neg(i,l)&:=(1-i,c(l)).
\end{aligned}
```

For every type σ and every admitted F:σt, interpret universal quantification by the coordinatewise Boolean and diamond meets of its values, and existential quantification by the coordinatewise Boolean and chain joins. The finite lattices are complete, so this defines quantification over every higher domain, however large. Equality at every type has value (1,1) for equal domain elements and (0,0) otherwise.

Every logical primitive has its classical truth condition in the first coordinate. Equality truth is actual identity, and function application and abstraction validate beta and eta. Hence the construction is an H model. It also satisfies all Functionality instances, since higher objects are actual functions.

The fixed formula u:=∀p p has value (0,0). Its negation has value (1,1), so the fixed abbreviations Top=u∨¬u and Bottom=u∧¬u have values T=(1,1) and B=(0,0). All-type identity bivalence holds: equality judgments are T or B.

## 2. The conjunction and universal branch

For l∈L with l≠0, define an admitted endpoint-valued observer

```math
E_l(i,m):=\begin{cases}T&l\le_d m,\\B&\text{otherwise.}\end{cases}
```

Also let E_*(i,m) be T if i=1 and B otherwise. These are admitted because the type tt is a full function domain.

Every displayed observer fixes T and B. Thus it accepts Top, rejects Bottom and fixes every identity judgment at every type. Each map m↦[l≤d m] preserves arbitrary diamond meets: l is below the meet of a family exactly when it is below every member. The coordinate truth reader has the analogous Boolean property. On the endpoint subalgebra, primitive conjunction and every primitive universal act as Boolean meet. Therefore these observers preserve conjunction and every universal quantifier as output identities. Since the higher domains are full function spaces, the pointwise calculations identify the whole composite operations.

The observers jointly separate propositions. E_* distinguishes differing first coordinates. If m≠n, either m is not below n, in which case m≠0 and E_m distinguishes them, or n is not below m and E_n does. Functionality then supplies full typed separation.

There is a stronger version. The diamond is a four-element Boolean algebra. The two tests E_a and E_b, together with E_*, separate 2×L and preserve diamond complementation as well as every diamond meet. Consequently the model satisfies full typed separation by endpoint-valued observers which simultaneously fix both endpoints, fix every equality operation, and preserve primitive conjunction, primitive negation and every universal quantifier.

## 3. The disjunction and existential branch

For l∈{0,a,b}, define

```math
D_l(i,m):=\begin{cases}T&m\not\le_c l,\\B&\text{otherwise.}\end{cases}
```

Use these observers together with E_*. They fix both endpoints and all identity judgments. For every admitted nonempty family (m_x),

```math
\sup_c(m_x)\not\le_c l\quad\Longleftrightarrow\quad\exists x\,(m_x\not\le_c l).
```

This follows because l is an upper bound of the family exactly when every member is below l. It proves existential preservation; the two-input instance proves disjunction preservation. The endpoint operations are the Boolean join operations, so these are output identities and hence full composite identities.

The threshold maps distinguish any two chain elements: if m<n, choose l=m, which is below 1. E_* handles the first coordinate. Thus this second class also supplies full typed separation, with endpoint range, endpoint fixing, all-type equality fixing, disjunction and every existential quantifier in one common qualification.

## 4. Failure of a common conjunction and disjunction class

Separation by any class preserving both primitive conjunction and primitive disjunction materially would force absorption. Indeed every eligible E has the same truth value on p and p∧(p∨q), by the ordinary Boolean absorption truth table; separation would identify those propositions.

Here choose p=(0,a) and q=(0,b). Then

```math
p\lor q=(0,b),\qquad p\land(p\lor q)=(0,0)\ne(0,a)=p.
```

Thus even material common-class conjunction/disjunction separation fails. In particular C fails, since C identifies the H-equivalent formulas p and p∧(p∨q).

The two strong separation theories in §§2–3 therefore hold jointly without entailing their common-class strengthening. This is not an issue about weak endpoint clauses, identity judgments, higher-type Functionality, absent quantifier instances or arbitrary external functions being inadmissible: the construction explicitly supplies all those features.

The model additionally separates the primitive existential from the existential derived from negation and the universal. Take a predicate with values including (0,a),(0,b) and no value with second coordinate 1, on a type with at least two elements (type t suffices). Its primitive existential has second coordinate b, while ¬∀x¬Fx has second coordinate 1. The stronger meet/negation/universal observer class therefore need not preserve the independent primitive existential.

## 5. Model verdicts and sources

Verified satisfied packages are the full typed separation theories in §§2–3, all-type Functionality, and all-type identity bivalence. Verified failures are common-class conjunction/disjunction separation, the displayed absorption identity, primitive existential De Morgan identity, and C. No verdict about other principles is inferred from omission here.

The direct source for the construction and these verifications is this original argument (`misc`, OpenAI Codex, 24 October 2026, §§1–4, unpaginated). The general profile argument used in §4 is in [Truth profiles and connective reducts](truth-profiles-and-connective-reducts.md), §§2–3. The relation between propositional and full typed separation is proved in [Typed separation and the recovery of Classicism](typed-separation-and-classicism.md), §2.
