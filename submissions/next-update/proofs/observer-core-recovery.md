# What classical observer cores recover

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`).

Endpoint observers recover all relations on individuals, and ordinary second-order evaluation becomes evaluation in one common classical Henkin structure with varying interpretations of the relational parameters. There is an exact type boundary: if there is a proposition other than Top and Bottom and the endpoint observers separate them, joint normalization is faithful exactly at e and e...et. Every type taking a relational argument loses information.

Even allowing arbitrary propositional images cannot remove the general obstruction. The cores of all proper idempotent logical observers jointly miss the nonzero predicate "is the identity operation". An entire typed model is recovered by its joint core normalizations if and only if the family already includes the identity observer and hence the original model.

Recovery does become possible if observers may evaluate outputs after arbitrary original arguments have been supplied. Section 6 specifies the exact data and operations needed, instead of treating a product of bare cores as an adequate representation.

## 1. Framework

Work in a general C5 model M, in the fixed relational type system. Its actual-function presentation has nonempty $`D_{e}`$, Boolean algebra $`D_{t}`$=B, admitted actual functions $`D_{\sigma\tau}`$ subset ($`D_{\tau}`$)^($`D_{\sigma}`$), crisp Leibniz identity, and admitted quantifier infima. Current truth is an ultrafilter U with the required quantifier truth clauses.

These are inherited C5 consequences. The native bridges are necessary-nd-implies-bf, followed by barcan-r-implies-functionality-r. They require boxed all-type ND, not unboxed ND alone.

An observer E:B->B is Good_t in the existing whole-operation sense. The established C5 reduction supplies its whole Boolean laws and every typed quantifier law. When E is idempotent, put

```math
r_e^E(x)=x,\qquad r_t^E(p)=E(p),\qquad r_{\sigma\tau}^E(f)=r_\tau^E\circ f\circ r_\sigma^E\tag{1.1}
```

The e clause is external notation, never an object of forbidden type ee. All relational clauses are admitted lambda operations. Each r is idempotent. Its fixed hierarchy is the canonical C5 Henkin core of [the typed-core construction](observer-classical-cores.md), Sections 2-4.

At a flattened relational type $`\tau=\sigma_1\cdots\sigma_nt`$,

```math
(r_\tau^Ef)[x_1,\ldots,x_n]=E(f[r_{\sigma_1}^Ex_1,\ldots,r_{\sigma_n}^Ex_n])\tag{1.2}
```

Let J be any external set of idempotent Good observers. We examine

```math
N_\tau(f)=(r_\tau^E(f))_{E\in J}\tag{1.3}
```

This is a map into a product of fixed domains. It is not assumed to preserve original application or to be a logical-model homomorphism.

## 2. Exact criterion for faithful normalization

**Theorem 2.1.** For $`\tau=\sigma_1\cdots\sigma_nt`$, $`N_{\tau}`$ is injective if and only if the following local condition holds:

```math
\forall\bar a\,\forall p\ne q\,\exists E\in J.\,\bigl(\bigwedge_{i=1}^n r_{\sigma_i}^E(a_i)=a_i\;\land\;E(p)\ne E(q)\bigr)\tag{2.1}
```

Thus separating output values is not sufficient: a separating observer must also leave the particular argument tuple intact. For n=0 this is exactly separation of B by J.

Proof of sufficiency. If f≠g, actual Functionality gives a full argument tuple a with f[a]=p≠q=g[a]. Choose E by (2.1). Equation (1.2) evaluated at a gives ($`r_{\tau}^E`$ f)[a]=E(p)≠E(q)=($`r_{\tau}^E`$ g)[a].

Proof of necessity. Fix a and p≠q. Crisp tuple identity defines admitted relations

```math
f[\bar x]=\delta(\bar x,\bar a)\land p,\qquad g[\bar x]=\delta(\bar x,\bar a)\land q\tag{2.2}
```

where delta is Top on the specified tuple and Bottom otherwise. These relations differ at a. If E fails to fix some a_i, no normalized input $`r_{\sigma_i}^E`$(x_i) can equal a_i: every element of that image is fixed. Consequently both normalizations in (2.2) are constantly Bottom. If E fixes the whole tuple, their normalized values are E(p) and E(q) at a, and Bottom off its inverse image under the normalization map. Hence $`r_{\tau}^E`$ f and $`r_{\tau}^E`$ g differ only if E fixes a and separates p,q. Injectivity of $`N_{\tau}`$ supplies such an E. QED.

In particular, injectivity on $`D_{\sigma t}`$ requires every σ-object to lie in at least one of the chosen fixed domains. Coverage alone is not the exact criterion; (2.1) retains simultaneous fixation and output separation by the same observer.

## 3. The identity-operation obstruction

Let I=lambda p.p at type tt, and let

```math
H_I(f):=\delta_{tt}(f,I),\qquad H_I:(tt)t\tag{3.1}
```

This is a nonzero admitted predicate, since H_I(I)=Top. For every idempotent E,

```math
r_{tt}^E(I)=E\circ I\circ E=E\tag{3.2}
```

Thus I is fixed by $`r_{tt}^E`$ if and only if E=I. If E is proper, its normalized-input image omits I, and therefore

```math
r_{(tt)t}^E(H_I)=\bot_{(tt)t}\tag{3.3}
```

**Theorem 3.1.** A family J of idempotent Good observers has injective joint normalization at every type if and only if I belongs to J. In fact, injectivity at the single type (tt)t already forces I to belong to J.

Proof. If I belongs, its component $`r_{\sigma}^I`$ is identity at every type. Conversely, if I does not belong, (3.3) identifies H_I with Bottom in every component, although the two original predicates differ. QED.

This rules out reconstructing an intensional model from all its proper normalized cores, even when their propositional images jointly separate every proposition. It does not rule out contextual reconstruction, a presentation retaining embeddings plus extra original data, or another notion of model morphism. The theorem is exactly about (1.3).

## 4. The type boundary for endpoint cores

Now let J be a nonempty separating family of endpoint-valued Good observers. Each is automatically idempotent. Assume B contains some a different from Bottom and Top.

**Theorem 4.1.** Joint endpoint normalization $`N_{\sigma}`$ is injective exactly for σ=e and for σ=e...et, including σ=t with zero arguments.

Positive direction. Normalization fixes individuals. For an e-only relation f it is simply the pointwise map f[x]->E(f[x]). If f≠g, a tuple of individuals gives distinct values, and a separating E preserves that difference. This is also the special case of Theorem 2.1 in which all argument normalizations are identity.

Negative direction. Suppose $`\tau=\sigma_1\cdots\sigma_nt`$ has a relational argument sigma_j. Let c:sigma_j be the admitted relation constantly equal to a (or c=a if sigma_j=t). By (1.2), $`r_{\sigma_j}^E`$(c) is the relation constantly equal to E(a), which is an endpoint and differs from a. Consequently c is fixed by no E in J. The admitted relation

```math
F[x_1,\ldots,x_n]:=\delta_{\sigma_j}(x_j,c)\tag{4.1}
```

is nonzero, since the argument domains are inhabited. But normalized arguments cannot equal c, so every $`r_{\tau}^E`$(F) is Bottom. QED.

In particular, the failure already occurs at tt, and also at (et)t: a higher predicate can detect which intensional relation it receives, whereas its classical cores inspect only normalized input relations. If B has exactly two elements instead, every endpoint Boolean observer is identity and normalization is faithful at every type. This is the extensional exception, not an omitted case of the theorem.

## 5. One classical second-order structure

For each n≥0 put

```math
K_n=\{R\in D_{e^nt}:\forall\bar x.\,R[\bar x]\in\{\bot,\top\}\}\tag{5.1}
```

Write e^0t=t. The $`K_n`$ are the same fixed domains for every endpoint observer, since individual inputs are never changed. In particular K_0={Bottom,Top}. Identify a member of $`K_n`$ with its extension as a relation on $`D_{e}`$; actual Functionality makes this identification injective. These form the ordinary second-order relational reduct K of the canonical classical Henkin core. Full external powerset domains are not assumed.

For E in J define

```math
\pi_E(R)=\lambda\bar x.\,E(R[\bar x])\in K_n\tag{5.2}
```

Every pi_E is onto $`K_n`$ because it fixes every $`K_n`$-member. The map

```math
R\longmapsto(\pi_E(R))_{E\in J}\tag{5.3}
```

is injective by Theorem 4.1, and each coordinate is surjective. This is a subdirect representation of the relation/application reduct. It is not a homomorphism of the full typed language including relation identity.

THEOREM 5.1 (Parameter truth). Let A be an ordinary relational second-order formula: variables range over individuals and e-only relations, relation variables/constants are used atomically only by application to individuals, and primitive equality is restricted to individuals. Boolean connectives and both individual and relation quantifiers are allowed. No native modal operator or variable taking relations as arguments occurs.

For any original assignment s and any E in J,

```math
E(\llbracket A\rrbracket_{M,s})=\top\quad\Longleftrightarrow\quad K\models A[\pi_E(s)]\tag{5.4}
```

and E([[A]]_M,s)=Bottom otherwise. Individual values are unchanged by pi_E; each relation value is transformed by (5.2). Extensional equality of relations may be expressed using individual quantifiers; literal identity of relation objects is not part of this fragment.

Proof by formula induction. For a relation atom, (5.4) is definition (5.2). Individual equality is crisp and fixed by every E. The Boolean steps use E's Boolean laws. The individual universal step uses

```math
E(Q_eF)=Q_e(E\circ F)
```

and the same individual range $`D_{e}`$. The values E(Fx) are endpoints, so their quantified value is Top exactly when all are Top.

For a relation quantifier of type e^n t, the whole quantifier law gives the same endpoint calculation over the original relation domain. By induction its matrix value depends only on pi_E(R). The map pi_E is onto $`K_n`$, so quantification over the original domain is exactly quantification over $`K_n`$ for that matrix. Duplicates have no effect. Existentials follow dually. This proves (5.4) with all remaining free parameters retained. QED.

**Corollary 5.2.** For any such A and assignment s,

```math
\begin{aligned}\llbracket A\rrbracket_{M,s}=\top&\Longleftrightarrow\forall E\in J.\,K\models A[\pi_E(s)],\\\llbracket A\rrbracket_{M,s}\ne\bot&\Longleftrightarrow\exists E\in J.\,K\models A[\pi_E(s)]\end{aligned}\tag{5.5}
```

These are exactly the native necessity and possibility tests, because J separates B and fixes the endpoints. They do not identify current truth with evaluation at some chosen E. Current truth remains U unless a truth-correct observer is separately supplied.

Thus all modal variation of ordinary second-order formulas with relational parameters is variation of their JOINT parameter interpretations in one fixed classical Henkin structure. The admissible joint profiles need not be a full product: no independent recombination of different parameters' coordinates has been assumed.

If all relation parameters lie in $`K_n`$, every pi_E fixes them. The denotation of A is then the endpoint selected by its classical K truth. This includes pure second-order sentences and parameters consisting of individuals and endpoint-valued e-only relations. Their noncontingency is already an established consequence of C5+Atomicity and earlier parameter versions. The additional result here is the explicit common- core evaluation and subdirect parameter-profile description, not a new No Pure Contingency theorem.

## 6. Recovery using original arguments

For an arbitrary relational type $`\tau=\sigma_1\cdots\sigma_nt`$ define the contextual observation table

```math
\Gamma_\tau(f)(E,a_1,\ldots,a_n):=E(f[a_1,\ldots,a_n])\tag{6.1}
```

Unlike core normalization, this supplies original arguments before observing the output. Its entries are endpoints. The individual sort is retained literally.

**Theorem 6.1.** All tables Gamma_tau are injective if J separates B. Conversely, injectivity at t is exactly that separation condition.

Proof. Distinct f,g have a full argument tuple with different proposition values. Some E separates those values, giving a different table entry. The empty-tuple case is the converse. QED.

These tables recover the whole typed applicative structure. For example, application is slicing:

```math
\Gamma_\tau(f(a))(E,\bar b)=\Gamma_{\sigma\tau}(f)(E,a,\bar b)\tag{6.2}
```

All pointwise Boolean operations are coordinatewise Boolean operations. Every admitted quantifier is recovered by

```math
\Gamma_t(Q_\sigma F)(E)=\top\quad\Longleftrightarrow\quad\forall x\in D_\sigma.\,\Gamma_{\sigma t}(F)(E,x)=\top\tag{6.3}
```

The same holds for trailing arguments and existential quantifiers. Crisp identity is the constant Top table on equal original objects and constant Bottom otherwise; injectivity makes equality of original relational objects precisely equality of their entire tables. Transporting U along Gamma_t recovers actual truth. No additional ultrafilter choice is made.

For a representation without original argument labels, proceed recursively through types: retain $`D_{e}`$, and replace every relational argument a by its already constructed table Gamma_sigma(a). Proper subtypes have already been treated, and injectivity makes (6.1) unambiguous on those labels. Retain exactly the tables arising from admitted original objects. Equation (6.2) supplies application; (6.3) supplies the quantifiers. Lambda denotations are transported by the same interpretation, so no external fullness is introduced. This yields an isomorphic presentation of M, including its original truth predicate and admitted domains.

The result is an observer-table presentation of the familiar intensional set semantics, not a new independent completeness theorem. Its purpose is to identify precisely the missing recovery information: arbitrary off-core input sections. Replacing each such input by its normalization is exactly the information loss quantified in Theorems 2.1, 3.1 and 4.1.

## 7. Sources and contribution

- [The typed-core construction](observer-classical-cores.md), §§1–3, supplies normalization and canonical comparison.
- [Logical-observer hierarchy](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md) and [C5 quantifier reduction](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/modal-selectors-and-quantifier-reduction.md#4-over-c5-q_t-supplies-every-quantifier) supply qualification and endpoint-theory inputs.
- Earlier [extensional-core](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/gallin-extensional-core.md) and [structural-world representation](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) results retain their attribution; §6 is not a new Gallin completeness theorem.

The new contributions are the fixed-input recovery criterion, the identity-operation obstruction, the exact endpoint type boundary, and common-core evaluation with its modal tests. No external fullness, independent recombination of parameter profiles, or unrestricted truth preservation under normalization is asserted.
