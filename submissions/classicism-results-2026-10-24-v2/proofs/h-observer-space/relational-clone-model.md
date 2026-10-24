# Four-proposition relational model separating the negation tiers

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated. The type system is the fixed relational system from the [topic background](../../source/topics/classicism/background.md).

There is an H model satisfying all Functionality instances and full typed material negation separation, but failing even propositional separation by observers that preserve negation as an output identity. Thus Functionality does not collapse the material and pointwise tiers. It does collapse pointwise and whole-operation negation preservation, as expected.

## 1. The proposition domain and its relation

Let

$$
D_t=\{c,d,c',d'\},\qquad A=\{c,d\},\qquad B=\{c',d'\}.
$$

The true propositions are c and d'; the false propositions are d and c'. Define negation N by

$$
Nc=c',\quad Nc'=c,\qquad Nd=d',\quad Nd'=d.
$$

Thus N reverses truth and is an involution. Put

$$
v=(c,d,c',d'),\qquad Nv=(c',d',c,d),
$$

$$
R_t:=A^4\cup B^4\cup\{v,Nv\}\subseteq D_t^4.
\tag{1}
$$

This four-place relation is reflexive: every constant tuple belongs to A⁴ or B⁴. Applying N coordinatewise exchanges A⁴ with B⁴ and v with Nv, so N preserves R_t.

Take D_e to be a singleton and R_e=D_e⁴. The relations R_σ are semantic restrictions used to construct the domains; they are not additional object-language predicates or assumptions.

## 2. Higher domains, application and abstraction

At every admitted arrow type σρ, where ρ≠e, define

$$
D_{\sigma\rho}:=\{f:D_\sigma\to D_\rho:
\forall(x_1,x_2,x_3,x_4)\in R_\sigma,
(fx_1,fx_2,fx_3,fx_4)\in R_\rho\}.
\tag{2}
$$

For f₁,…,f₄ in this domain, define

$$
(f_1,f_2,f_3,f_4)\in R_{\sigma\rho}
\quad\Longleftrightarrow\quad
\forall(x_1,x_2,x_3,x_4)\in R_\sigma,
(f_1x_1,f_2x_2,f_3x_3,f_4x_4)\in R_\rho.
\tag{3}
$$

Every R_σ is reflexive, inductively: at an arrow type, the diagonal tuple (f,f,f,f) satisfies (3) precisely because f satisfies (2). Every domain is nonempty. Given a∈D_ρ, the constant function with value a belongs to D_{σρ}, since the diagonal tuple of a belongs to R_ρ.

Application is ordinary function application. Its preservation of the relations is exactly (3): a related tuple of functions applied to a related tuple of arguments gives a related tuple of results.

For completeness, abstraction is closed in these domains. Interpret a context by the product of its domains, with its relation defined coordinatewise. Suppose a body M with an additional variable x:σ defines a relation-preserving function g on that context and D_σ. Fix a context assignment γ. The tuple (γ,γ,γ,γ) is related, so g(γ,−) preserves R_σ and belongs to D_{σρ}. If γ₁,…,γ₄ are related context assignments, then for every related x₁,…,x₄ the results g(γᵢ,xᵢ) are related. By (3), the four sections g(γᵢ,−) are related elements of D_{σρ}. Thus the curried interpretation is itself relation-preserving.

Variables preserve the context relation. An interpreted constant does too, since every domain element is diagonal-related. Application and the preceding abstraction argument therefore prove by induction that every term has an admitted denotation and preserves related assignments. This supplies the complete interpretation of lambda terms; no external closure theorem is assumed.

Because arrows are actual functions on the admitted domains, beta and eta hold as identities, including their contextual instances. Equality of values at every input is equality of functions, so all Functionality instances hold.

## 3. The remaining logical objects and H soundness

Interpret conjunction and disjunction by their ordinary truth conditions, returning c when the resulting condition is true and d when it is false. At every type σ, set

$$
\forall_\sigma F=
\begin{cases}c&\text{if every }x\in D_\sigma\text{ makes }Fx\text{ true},\\
d&\text{otherwise},\end{cases}
$$

with the analogous existential interpretation, again returning c or d. Interpret equality at every type by

$$
\mathrm{Eq}_\sigma(x,y)=
\begin{cases}c&x=y\text{ as domain elements},\\d&x\ne y.\end{cases}
\tag{4}
$$

Each displayed operation has its entire output range in A. Consequently, any four outputs form a tuple in A⁴⊆R_t. The uncurried operations preserve their product relations, and §2 supplies their curried admitted interpretations. This argument covers equality at every higher type and quantification over every admitted domain. Negation is admitted separately by its preservation of R_t in §1.

All primitives therefore have their required H truth conditions. PC and MP are sound by the truth tables. UI and EG are sound because term denotations are admitted and quantifiers range over exactly those domains. Gen is sound with its free-variable condition. Inst, from P→Q to (∃x P)→Q when x is not free in Q, is sound by taking the existential witness and applying the premise under that assignment. Ref and Leibniz substitution are sound because equality truth is actual identity. The contextual beta and eta equations were checked in §2. Nonempty D_e supplies individual existence.

This verifies H directly. The rule inventory and its source-draft qualification are recorded in [Local separation tiers](local-tiers-and-models.md), §1. No arbitrary rule turning a material equivalence into an identity is used.

The fixed abbreviations have the following values. Since some propositions are false, a:=∀p p is d. Then ¬a=d', so

$$
\mathrm{Top}=a\lor\neg a=c,\qquad
\mathrm{Bottom}=a\land\neg a=d.
\tag{5}
$$

In particular N(Top)=c'≠d=Bottom. Thus C fails: H proves the material equivalence of ¬Top and Bottom, while their proposition objects here differ.

## 4. The exact unary observer domain

The admitted observer domain is

$$
D_{tt}=\{I,N\}\ \cup\ A^{D_t}\ \cup\ B^{D_t}.
\tag{6}
$$

Here I is identity, and A^{D_t} and B^{D_t} mean the maps whose ranges are contained in the indicated block.

For necessity, an admitted f must preserve the related tuple v. Since v lists all four proposition objects, its image tuple is the complete table of f in that order. By (1), that table either lies entirely in A, lies entirely in B, equals v, or equals Nv. These are exactly the four possibilities in (6).

Conversely, every map with range in one block preserves R_t because every output tuple lies in that block's fourth power. Identity preserves R_t, and N does by §1. This proves (6), giving 34 admitted unary maps in total.

## 5. Failure of pointwise and whole-operation negation separation

Write N_pt(E) for

$$
\forall p\,[E(Np)=N(Ep)].
$$

No observer whose range is contained in A can satisfy this: E(Np) lies in A while N(Ep) lies in the disjoint block B. The same argument exchanges A and B. By (6), the only N_pt observers are I and N, and both do satisfy the identity.

They agree in truth on the distinct propositions c and d'. Identity accepts both. Negation sends them to c' and d, both false. Thus

$$
\forall E\,[N_{\rm pt}(E)\to(Ec\leftrightarrow Ed')]
$$

is true, while c=d' is false. Propositional pointwise negation separation fails.

Whole-operation preservation is

$$
(\lambda p.E(Np))=(\lambda p.N(Ep)).
$$

The two sides are actual functions on D_t. Hence this qualification is equivalent to N_pt(E) in the model, also as a consequence of its Functionality instance at t,t. Propositional whole-operation negation separation fails as well.

## 6. Full typed material negation separation

Write N_mat(E) for

$$
\forall p\,[E(Np)\leftrightarrow\neg Ep].
$$

For each pair of ordinary Boolean values ε,δ, define an A-valued observer E_{εδ} by specifying its truth profile:

| Input | c | d | c' | d' |
|---|---|---|---|---|
| Truth of E_{εδ}(input) | ε | δ | 1−ε | 1−δ |

Each output is c for truth value 1 and d for truth value 0. These are four admitted maps by (6). They satisfy N_mat because the two inputs in each N-orbit receive opposite truth values.

The four profiles jointly distinguish all four propositions: the columns are the distinct Boolean functions ε, δ, 1−ε and 1−δ of the two independent inputs ε,δ. Thus whenever p≠q, one displayed material observer gives different truth values to p and q. This proves propositional material negation separation. Its equality-to-agreement direction follows from actual identity, as required.

All Functionality instances hold by §2. The general theorem in [Typed separation and Classicism](typed-separation-and-classicism.md), §2, therefore upgrades this propositional separation to full typed material negation separation at every relational type. Equivalently, if two higher objects differ, iterated function extensionality finds a tuple where their proposition values differ, and one of the displayed observers distinguishes those values.

Double negation also holds as an output identity. The direct tests above independently verify the corresponding instance of the general H equivalence between double negation and material negation separation in [Truth profiles](truth-profiles-and-connective-reducts.md), §6.

## 7. Exact scope of the distinction

The model proves

$$
\mathrm H+\mathrm{Functionality}
 +\mathrm{FullSep}[N_{\rm mat}]
\ \not\models\ \mathrm{Sep}_t[N_{\rm pt}].
$$

Consequently the material and pointwise separation tiers differ over H even with all Functionality and full typed material separation. The pointwise and whole-operation tiers coincide in this model; it does not counterexample their equivalence under Functionality.

No endpoint qualification, preservation of an additional primitive, or equality-fixing restriction is included in this statement. It also does not contradict the equivalence of the three complete logical separation theories: that theorem requires the complete Boolean, quantifier and translated-equality package, not negation alone.

Together with [Local separation tiers](local-tiers-and-models.md), §3, this supplies explicit H models for both local distinctions: material versus pointwise preservation, and pointwise versus whole-operation preservation. The latter construction uses a different model without the Functionality that would identify its last two tiers. The operations witnessing the two distinctions need not be the same.

The construction, exact domain classification and separation arguments are original ordinary proofs: `misc`, OpenAI Codex, 24 October 2026, this note, §§1–6, unpaginated.
