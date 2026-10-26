# Shift models: examples, modal structure and computability

The [shift representation theorem](observer-shift-semantics.md) gives a complete presentation of C + OS by ordinary functions, literal quantifier intersections and internally admitted shifts. Henkin closure still constrains the domains. The following examples identify the role of those domains and compare this presentation with existing action models.

## 1. A finite collapse model

Take $`M=\{1,z\}`$ with $`z^2=z`$, $`B=\mathcal P(M)`$ and a singleton individual domain. Define $`A\sim_t B`$ when they have the same z-membership; use equality at e. Recursively admit all functions preserving the input and output equivalences, and put

```math
f\sim_{\sigma\tau}g\quad\Longleftrightarrow\quad
\forall a\in D_\sigma\, .\,f(a)\sim_\tau g(a).
```

Every domain is finite at each fixed type. Application respects equivalence because $`f\sim g`$ and $`a\sim b`$ imply $`f(a)\sim g(a)\sim g(b)`$. Boolean operations preserve the equivalence at t. Related predicates have the same z-membership at each input, so quantifier intersections respect equivalence too. Induction on terms proves parameterized abstraction closure.

A predicate at any type can have arbitrary 1-membership on its inputs and arbitrary z-membership on their equivalence classes. Hence Leibniz equality is

```math
\delta_\sigma(a,b)=\{1:a=b\}\cup\{z:a\sim_\sigma b\}.
```

The shifts are identity and

```math
R_z(A)=
\begin{cases}M&z\in A,\\\varnothing&z\notin A.\end{cases}
```

They are admitted, preserve all quantifiers and separate the proposition domain. The general soundness theorem gives C + OS. For $`a=\{1\}`$ and $`b=\varnothing`$, their equality has value $`\{z\}`$; their distinctness has value $`\{1\}`$ but its necessity has value $`\varnothing`$. Thus ND at t fails.

The closed pure sentence $`\exists p\, .\,p\ne\top\land p\ne\bot`$ also has value $`\{1\}`$. Its necessity is empty. Shift models therefore allow pure contingency.

## 2. Identification with the existing full two-object chain

This collapse is the full action model on the two-object chain, in a function presentation. Its construction retains Bacon and Dorr's attribution; the explicit identification is the additional result.

Put $`D_\sigma^0=D_\sigma`$, $`D_\sigma^1=D_\sigma/{\sim_\sigma}`$, and let $`q_\sigma`$ be the quotient. At e both domains are singletons. At t there are four root propositions and two quotient propositions; transport records z-membership.

At an arrow type, a full action object on the chain is a pair of functions satisfying

```math
f_0:D_\sigma^0\to D_\tau^0,\qquad
f_1:D_\sigma^1\to D_\tau^1,\qquad
q_\tau\circ f_0=f_1\circ q_\sigma.
```

Since $`q_\sigma`$ is onto, $`f_1`$ is uniquely determined by $`f_0`$ whenever it exists. Existence is exactly preservation of the equivalences. Every $`f_1`$ lifts: choose a representative of each output class, using only finite choice at each type. The quotient at the arrow type is therefore onto, with kernel pointwise output equivalence. This proves the typed correspondence inductively.

Boolean operations agree. Surjectivity makes quantification over representatives agree with quantification over quotient objects. The displayed equality formula agrees as well, so this is an isomorphism of typed logical structures.

The full one-object action model over the idempotent monoid is different. Its nonidentity arrow lands back in the four-proposition domain with a two-element image, whereas the chain's arrow is onto a two-proposition target. The former fails BF at t. Also every one-object action model satisfies No Pure Contingency, while the example above does not. The monoid in a shift model composes proposition tests; it does not specify coherent transport of the entire typed structure.

Existing records: [full two-object chain](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/models/full-two-object-chain.yaml) and [full idempotent-monoid action model](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/models/full-idempotent-monoid.yaml).

## 3. The same monoid and propositions can have different necessity

Keep $`M=\{1,z\}`$, $`B=\mathcal P(M)`$ and the singleton individual domain. In the equivalence-preserving hierarchy above,

```math
\Box\{z\}=\delta_t(\{z\},M)=\{z\}.
```

Instead admit every ordinary function at every allowed arrow type. All required abstractions, quantifiers and shifts are admitted, so this too is a shift model. For distinct $`u,v`$, the admitted predicate which is $`M`$ exactly at $`u`$ and empty elsewhere makes their Leibniz equality empty. Equal objects have equality value $`M`$. Consequently,

```math
\Box\{z\}=\delta_t(\{z\},M)=\varnothing
```

in this second hierarchy. The higher predicates therefore carry modal information absent from the monoid and proposition algebra alone.

There is always the inclusion

```math
\Box A\subseteq K_M(A),\qquad
K_M(A):=\{n\in M:\forall m\in M\, .\,nm\in A\}.
```

If $`n\in\delta_t(A,M)`$, every admitted predicate agrees on $`A,M`$ at $`n`$. Apply this to each $`R_m`$, which sends $`M`$ to itself; then $`nm\in A`$. In the two hierarchies, $`K_M(\{z\})=\{z\}`$, with equality in the first and strict containment in the second. Thus the right-extension test does not generally define native necessity.

## 4. Computability

**Theorem.** In an effective countable relational language, both C-theoremhood and C + OS-theoremhood are $`\Sigma^0_1`$-complete under computable many-one reductions. Validity over all shift models, including the sufficient class on the fixed monoid $`\mathbb N^*`$ with countable domains, has the same complexity.

For the upper bound, enumerate H proofs. This enumerates C's Logical Equivalence instances without deciding H-theoremhood. Types, finite qualification lists and OS formulas are effectively enumerable. Enumerating finite proofs therefore enumerates both theorem sets.

For hardness, take a first-order sentence in a finite relational vocabulary over nonempty domains. Replace each n-ary predicate symbol by a variable of type $`e^nt`$ and each individual constant by an e-variable; universally close those variables. This is an effective translation to a closed pure typed sentence.

A valid first-order sentence has a first-order proof. Typed substitution and generalization give an H proof of its translation. If the sentence is invalid, expand a counterstructure to the full two-valued relational type hierarchy. Identity on propositions preserves every logical operation and separates all unequal relations through their argument values, so the hierarchy validates C + OS. The original relation and individual interpretations refute the universally closed translation. Thus first-order validity reduces to both theorem sets. Shift completeness transfers the conclusion to the stated model-validity problems.

The lower-bound input is the standard completeness result for first-order relational validity; see Mahesh Viswanathan, [*First Order Logic*, Fall 2018](https://courses.grainger.illinois.edu/cs498mv/fa2018/FirstOrderLogic.pdf), §4, Theorem 28, PDF pp. 8–10. The typed reduction is the connecting argument here.

## 5. Remaining model obligations

The completeness theorem is an existence theorem using elementary diagrams and compactness. It does not give an effective normalization algorithm for a supplied computable model. The fixed monoid has computable multiplication, but the Boolean subalgebra and Henkin domains need not be effectively presented.

Every parameterized abstraction must be admitted, every predicate intersection must belong to the proposition algebra, and the quantifier maps and shifts must themselves be admitted. These conditions couple the types. Filling all ordinary function spaces moves to a stronger standard-model regime; full action-model domains instead consist of coherent profiles and need not have the same behavior.

The benefit is a complete ordinary-function/intersection presentation with explicit separating shifts. Constructing particular restricted Henkin domains still requires a closure proof. General action models retain the broader scope of C, including models failing BF, and can remain convenient for constructing examples.

## Sources

Representation, comparison and computational arguments: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), *Shift models for logical observer separation*, §9; *Shift models and action models*, §§1–5; and *Shift-model hidden costs*, §§1–3, all unpaginated. [Source hashes](../evidence/source-manifest.json) · [Review evidence](../evidence/proof-reviews.json). The existing chain and idempotent action constructions retain their original record attribution.
