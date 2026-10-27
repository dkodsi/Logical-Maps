# A full classical present over any Classicist model

Every general C model can be retained as the old component of a new C model with arbitrary current relations, Strong Actuality, Relational Choice and Transversal Choice. The new model also contains a definable full standard classical hierarchy. Its individual domain can be any nonempty set admitting the specified map to the old individuals.

This construction preserves the original model's intensional operations, quantifiers and lambda interpretation. It does not require BF, Functionality or C5. The accompanying [conservation theorem](classical-present-conservation.md) explains what its current mathematical richness adds to necessary consequences.

## 1. Domains, application and projection

Let $`K`$ be a general C model, choose a nonempty set $`A`$, and fix any map $`h:A\to K_e`$. In the fixed relational grammar every nonindividual type has a unique form $`\tau=\sigma_1\cdots\sigma_nt`$. Define

```math
R_e=A,\qquad
R_\tau=\mathcal P(R_{\sigma_1}\times\cdots\times R_{\sigma_n})\times K_\tau
```

For $`n=0`$, this is $`R_t=2\times K_t`$. A relation has an arbitrary current extension and an unchanged old object. Set $`q_e=h`$ and $`q_\tau(S,k)=k`$ for relational $`\tau`$. Application takes the current row and uses the old application:

```math
(S,k)(x)=(S_x,k(q_\sigma(x)))
```

No extensional identification of old operations is made. Each relational projection is onto, since any old object can be paired with the empty current relation. All domains are nonempty sets in ZFC.

Equivalently, an arrow object comprises a current function $`f_0:R_\sigma\to R_\tau`$ and an old object $`f_1\in K_{\sigma\tau}`$ satisfying

```math
q_\tau(f_0(x))=f_1(q_\sigma(x))\quad(x\in R_\sigma)
```

The equivalence follows by currying the arbitrary current extension. Different old objects are retained even when the current functions agree.

## 2. Logical interpretation and C soundness

Current truth reads the first bit. Give every logical constant its ordinary current extension and its old interpretation. Boolean operations are coordinatewise. For a predicate $`F`$,

```math
Q_\sigma^R(F)=
\left([\forall x\in R_\sigma\, .\,F(x)\text{ is true}],\;
Q_\sigma^K(q_{\sigma t}(F))\right)
```

The second coordinate uses the quantifier of $`K`$ over its entire domain; at $`e`$ it is not restricted to $`h[A]`$. For an abstraction, take its body's current extension and the denotation in $`K`$ of the same abstraction with projected free parameters. Both components are admitted by the product definition. Induction gives, for every term,

```math
q_\tau(T^R(\bar a))=T^K(q(\bar a))
```

At $`e`$, terms are variables or individual constants, since no function type has individual output. This explains why an arbitrary $`h`$ is possible. The abstraction step retains the old lambda interpretation, including when $`K`$ fails Functionality. Beta and eta hold at both components.

Leibniz equality computes as

```math
\delta_\sigma^R(x,y)=
\left([x=y],\delta_\sigma^K(q_\sigma(x),q_\sigma(y))\right)
```

Arbitrary current singleton predicates distinguish distinct root objects, while term projection computes the old equality expression with its original quantifier domain. Thus current equality is actual identity, regardless of whether $`h`$ is onto.

The current classical clauses validate H. An H theorem has old value Top by C's gate in $`K`$, so its whole root value is Top. If H proves an equivalence, its abstractions have identical current extensions and equal old components by the same gate in $`K`$. Their pairs are equal. This verifies exactly C's H-theoremhood restriction, without applying Logical Equivalence to optional premises.

In particular, for $`p=(\epsilon,b)`$,

```math
\Box_Rp=([p=\top_R],\Box_Kb)
```

For a sentence $`B`$ whose constants project correctly,

```math
R\models\Box B\ \Longleftrightarrow\
(R\models B\ \text{and}\ K\models\Box B),
```

```math
R\models\Diamond B\ \Longleftrightarrow\
(R\models B\ \text{or}\ B^K\ne\bot_K)
```

Consequently a failure of necessity in $`K`$ remains a failure in $`R`$.

## 3. Strong Actuality and selection

The proposition $`a=(1,\bot_K)`$ is a true atom beneath every currently true proposition. It witnesses Actuality. It also witnesses Strong Actuality: in

```math
D=\forall p\, .\,(a\le p\lor a\le\neg p),
```

the current bit is 1 by atomhood, and the old component substitutes Bottom for $`a`$, giving Top by C's Boolean identities and quantifier laws. Thus $`D=\top_R`$ and $`\Box D`$ is true.

Every external relation on any finite tuple of current domains is admitted, paired with an old Bottom relation. For a serial relation, external Choice selects one output for each input; its graph is an admitted current subrelation. This proves every Relational Choice instance, including individual outputs. Likewise, an externally selected set of representatives of an actual equivalence relation is an admitted predicate, proving Transversal Choice at every type. These are relation witnesses, not operation representatives. The construction uses ZFC in the metatheory and does not settle Relational Choice ⇒ Transversal Choice over arbitrary C models.

The relational Boolean algebra is the displayed product algebra. Hence it is atomic exactly when the corresponding old algebra is atomic. Root Boolean Completeness, however, holds exactly when that old algebra is externally complete: all external families are now represented by root predicates. An old Henkin model's restricted Boolean Completeness need not imply this. These product criteria extend the earlier construction rather than supply an independent novelty claim.

## 4. A full standard normalized core

Define

```math
n_e(x)=x,\qquad n_t(p)=a\land p,\qquad
n_{\sigma\tau}(f)=\lambda x^\sigma\, .\,n_\tau\bigl(f(n_\sigma(x))\bigr)
```

Again the individual identity is external notation. Every relational normalization is an admitted term. Induction shows that it is idempotent and every normalized relational object has old component Bottom. At an arrow, output normalization makes the old function constantly Bottom, so C's beta–eta and Boolean identities make the whole old arrow Bottom. A second normalization has the same current function by the induction hypotheses, and the same old component. This proves idempotence without ambient Functionality.

Let $`C_e=A`$ and $`C_\tau=\{x:n_\tau(x)=x\}`$ at relational types. Then $`C_t=\{\bot_R,a\}`$, and restriction gives

```math
C_{\sigma\tau}\ \cong\ (C_\tau)^{C_\sigma}
```

A fixed arrow is determined by its values on fixed inputs, since $`f=n_\tau\circ f\circ n_\sigma`$, and its old component is Bottom. This proves injectivity. For any external $`u:C_\sigma\to C_\tau`$, take current function $`x\mapsto u(n_\sigma(x))`$ and old component Bottom. All outputs have old component Bottom, so the pair is coherent and admitted. It is fixed and restricts to $`u`$, proving surjectivity.

The core is therefore the full standard relational hierarchy over $`A`$. Its truth is $`a`$, its falsity is ambient Bottom, and its negation is $`a\land\neg p`$. Normalized equality gives $`a`$ for equal fixed objects and Bottom otherwise. A fixed predicate has the same value range on all inputs as on fixed inputs. Its ambient quantifier has the appropriate current classical value and old value Bottom, so it already gives the required core quantifier. Projecting the whole quantifier operation admits it as a core object. Existential quantification is analogous.

This supplies a definable interpretation of arbitrary full standard higher-order mathematics: relativize relational quantifiers to $`n_\tau(x)=x`$ and use the normalized logical constants. Individual quantifiers are unchanged. Ambient Top and the core truth $`a`$ are different, and arbitrary ambient sentences are not thereby given their standard truth values.

## 5. Standard second-order truth without relativization

There is a stronger statement for the ordinary relational second-order fragment. Allow individual variables, relation variables on finite tuples of individuals, Boolean connectives and their quantifiers. Relations occur only applied to individual arguments; equality is individual equality. Exclude modal operators, native relation identity and higher-order argument positions.

Fix any ordinary relational structure $`\mathcal A`$ on $`A`$. Interpret its signature relations at the root by their $`\mathcal A`$-tables and arbitrary prescribed old denotations. Then

```math
R\models\varphi\quad\Longleftrightarrow\quad
\mathcal A\models_{\mathrm{full\ SO}}\varphi
```

for every sentence in this fragment. For formulas with free variables, associate the ordinary assignment by keeping individuals and taking the current tables of relation objects. Atomic applications and individual equality have their standard truth. Boolean and individual-quantifier cases are immediate. At a relation quantifier, every subset of $`A^n`$ occurs as a current extension, and the induction hypothesis makes intensional duplicates irrelevant. This gives full powerset semantics for both quantifiers.

In particular, standard second-order arithmetic can hold actually and without relativization using zero, successor, addition and multiplication as relations. This is a specified arithmetic presentation on individuals, distinct from the map's pure Frege cardinality interpretation.

## 6. Exactly which current functions are operations

An external function $`f:R_\sigma\to R_\tau`$, with relational output, is represented by an ambient operation exactly when some admitted $`k\in K_{\sigma\tau}`$ satisfies

```math
q_\tau(f(x))=k(q_\sigma(x))\quad\text{for every }x\in R_\sigma
```

Necessity follows from application; sufficiency is the coherent-pair description. Thus projected outputs must be constant on projection fibres, and the resulting rule must extend to an admitted old operation.

For every relational input type, a projection fibre contains distinct current objects. At every relational output type, old Top and Bottom are distinct. Choose a function sending two inputs in one fibre to outputs with those different old values. Its current functional graph is admitted, but no operation represents it. Thus Plenitude fails at every relational-input/relational-output instance. Individual-input instances are governed by $`h`$ and the same criterion, and may behave differently.

For example, an actual truth evaluator would send $`(0,b)`$ and $`(1,b)`$ to ambient Bottom and Top, contradicting this criterion. Its graph exists but its operation does not. Core normalization instead sends them to Bottom and $`a`$, both projecting to old Bottom, so it is admitted.

## 7. Signatures and scope

Every relational constant can have any chosen current table while retaining its old denotation. An individual constant with chosen current value $`c_R`$ requires $`h(c_R)=c_K`$; free individual parameters obey the same rule. If $`h`$ is onto, every old parameter lifts at every type. This onto version is used for the full conservation theorem.

New parameters used solely to describe the normalized core have constrained old values. They cannot be treated as arbitrary original parameters in a conservation assertion. Original relational signature constants, whose current tables and old values are independently chosen, do not have that restriction.

## Sources and contribution

General construction, full standard core, second-order truth and exact operation criterion: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), `general-observer-principles/models.txt`, §§1–8, unpaginated; [source manifest](../evidence/source-manifest.json).

Earlier project arguments supplied special profile roots, strong current packages over selected tails, product Atomicity criteria and special necessary-consequence results. The extension here retains an arbitrary intensional C model with its own lambda and quantifier interpretation, permits arbitrary current individuals with the stated map, and proves full standardness of the recursively normalized hierarchy. The associated conservation theorem is given separately.
