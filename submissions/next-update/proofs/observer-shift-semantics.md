# Shift models for logical observer separation

Full relational OS over C has a sound and strongly complete semantics using sets and ordinary functions. A monoid indexes proposition tests, and its admitted shifts supply the separating observers. In a countable language, one fixed monoid suffices: finite strings of natural numbers under concatenation.

## 1. Definition

Work in ZFC with the fixed relational types: e, t, and $`\sigma\tau`$ only when $`\tau\ne e`$. A shift model consists of:

- A monoid $`M`$ with identity $`1`$.
- A nonempty individual domain $`D_e`$ and a Boolean subalgebra $`B\subseteq\mathcal P(M)`$, with $`D_t=B`$. Boolean operations are the set operations; Top and Bottom are $`M`$ and $`\varnothing`$.
- Nonempty domains $`D_{\sigma\tau}\subseteq D_\tau^{D_\sigma}`$ of ordinary functions. Application is evaluation. Every permitted lambda abstraction under every parameter assignment belongs to its specified domain, and the logical operations are admitted at their types.
- For each admitted predicate $`F\in D_{\sigma t}`$, the intersection $`Q_\sigma(F):=\bigcap_{a\in D_\sigma}F(a)`$ belongs to $`B`$. The operation $`Q_\sigma`$ itself is admitted at type $`(\sigma t)t`$. Existential quantification is the dual union.
- For each $`m\in M`$, the shift below belongs to $`D_{tt}`$:

```math
R_m(A):=\{n\in M:nm\in A\}
```

- Admitted predicates distinguish different individuals at $`1`$: for distinct $`a,b\in D_e`$, some $`P\in D_{et}`$ has exactly one of $`P(a),P(b)`$ containing $`1`$.

Truth is membership of $`1`$. Equality is determined by the admitted predicates:

```math
\delta_\sigma(a,b):=
\bigcap_{P\in D_{\sigma t}}\bigl(P(a)\leftrightarrow P(b)\bigr),
\qquad \Box A:=\delta_t(A,M)
```

For subsets of $`M`$, $`A\leftrightarrow B`$ denotes the complement of their symmetric difference. The equality intersection is admitted: apply $`Q_{\sigma t}`$ to the lambda-defined predicate $`P\mapsto(P(a)\leftrightarrow P(b))`$. Abstraction also admits the whole equality operation.

These are Henkin domains, closed under the language's operations. They need not contain every external function. No transport on all typed domains is stipulated.

## 2. Soundness for C

**Actual equality lemma.** At every type,

```math
1\in\delta_\sigma(a,b)\quad\Longleftrightarrow\quad a=b
```

Equal objects agree under every predicate. Distinct individuals are separated by the defining condition. If propositions $`A,B`$ differ, choose $`m`$ in their symmetric difference. The admitted predicate $`R_m`$ distinguishes them at $`1`$, since $`1\in R_m(A)`$ exactly when $`m\in A`$.

At an arrow type, distinct functions $`f,g`$ differ at some input $`a`$. Inductively an admitted predicate $`P`$ distinguishes their outputs at $`1`$. Abstraction admits $`h\mapsto P(h(a))`$, which distinguishes the functions. This proves the lemma at all admitted types.

**H soundness.** Every H theorem has value $`M`$ under every assignment. Boolean reasoning is pointwise set reasoning; universal and existential rules are valid for intersections and unions. Beta and eta conversion hold for ordinary functions. Reflexivity, symmetry and transitivity follow from the definition of $`\delta`$. For substitution,

```math
\delta_\sigma(a,b)\subseteq P(a)\leftrightarrow P(b)
```

for every admitted predicate $`P`$. Abstraction provides such a predicate for each formula with parameters, so equality replacement preserves truth at each index. The same argument gives application congruence. Induction on H proofs establishes the claim. At indices other than $`1`$, equality may identify different current objects; H does not demand Functionality of their quotient domains there.

If H proves $`A\leftrightarrow B`$, the two formulas therefore denote the same subset under every assignment. Their abstractions are identical ordinary functions. The actual equality lemma validates the corresponding Logical Equivalence instance. Thus every shift model validates C with its original H-theoremhood restriction.

## 3. Shifts supply full OS

Inverse images preserve Boolean operations and arbitrary intersections. In particular, for each admitted predicate,

```math
R_m(Q_\sigma(F))
=\bigcap_{a\in D_\sigma}R_m(F(a))
=Q_\sigma(\lambda a\, .\,R_m(F(a)))
```

Abstraction admits the predicate on the right. These are equalities of values for every input, hence identities of the whole composite operations in the function domains. Existential preservation follows by duality. The H equality laws have value $`M`$, so their observed versions hold as well. Every shift is thus qualified at every admitted type.

For different propositions, the shift chosen in the actual equality lemma distinguishes their truth values at $`1`$. For different relations, repeatedly choose arguments where their ordinary function values differ until the outputs are propositions; then use that shift. Equal relations cannot be distinguished. This proves every current full relational OS instance, for every finite qualification list.

## 4. The initial reduction from BF

Conversely, take any general Henkin model of C + OS and its actual identity quotients. C makes its proposition domain a Boolean algebra. OS implies BF, which is equivalent to Functionality and Tractarianism. Functionality presents the arrow domains as sets of ordinary functions by recursively taking their current values. BF makes a quantifier the Boolean infimum of its admitted range:

```math
Q_\sigma(F)=\inf_{a\in D_\sigma}F(a)
```

Instantiation gives the lower-bound direction. If $`b\le F(a)`$ for every $`a`$, then each $`b\to F(a)`$ is Top. BF gives the necessity of their universal closure; C's fixed-parameter distribution law yields $`b\le Q_\sigma(F)`$. The H equivalence between identity and agreement under all predicates gives the corresponding algebraic formula for $`\delta`$.

These reductions already hold over C + BF. The further OS argument represents all the needed infima simultaneously by set intersections and all the chosen observers by admitted shifts.

## 5. Realizing uniformly qualified observers

**Lemma.** Every general Henkin C + OS model has an elementary extension in which each nonzero proposition is accepted by an admitted observer preserving Boolean operations and every typed quantifier operation.

Use the many-sorted first-order Henkin presentation: one sort per type, application and logical operations, a truth predicate at t, and abstraction operations for lambda-term patterns with their parameter arguments. Include ordinary truth clauses, actual identity, conversion, and C's original axiom schema. Every original formula, qualification and OS instance has a finitary translation, so elementary diagrams and compactness apply.

For every nonzero $`b`$ in a model $`N_i`$, add a constant $`E_b^{tt}`$, all its Boolean and typed quantifier preservation identities, and the assertion that $`E_b(b)`$ is true. Every finite part is realized in $`N_i`$: its type requirements fit in one finite list, and OS separates $`b`$ from Bottom with an observer qualified at that list. Since Bottom is rejected, $`b`$ is accepted. Finitely many new observers can be chosen independently.

Compactness gives an elementary extension $`N_{i+1}`$ containing all these witnesses. Repeat for $`i=0,1,\ldots`$ and take the elementary union $`N`$. Every proposition appears at some stage; its next-stage witness remains qualified at all types in the union by elementarity. In a countable language, a countable starting model and the countable Henkin construction keep all stages countable.

The collection of uniformly qualified observers is an external set. No admitted predicate listing that collection is required.

## 6. Representation and strong completeness

In $`N`$, let $`M`$ be the monoid of all uniformly qualified admitted observers, with $`mn=m\circ n`$. Abstraction admits composition and identity; the preservation laws are closed under composition. Put

```math
\phi(b):=\{m\in M:m(b)\text{ is true in }N\}
```

Boolean preservation makes $`\phi`$ a Boolean homomorphism. If $`b\ne c`$, their symmetric difference is nonzero; the lemma supplies an observer accepting that difference and hence distinguishing them. Thus $`\phi`$ is injective.

For every admitted predicate and every $`m\in M`$, quantifier preservation and actual quantifier truth give

```math
m(Q_\sigma(F))\text{ is true}
\quad\Longleftrightarrow\quad
\forall a\in D_\sigma\, .\,m(F(a))\text{ is true}
```

Consequently,

```math
\phi(Q_\sigma(F))=\bigcap_{a\in D_\sigma}\phi(F(a))
```

Transport the higher domains recursively along $`\phi`$ at t and identity at e. If the type bijections are $`j_\sigma,j_\tau`$, represent $`f`$ by $`j_\tau\circ f\circ j_\sigma^{-1}`$. These transports preserve application, abstraction and logical operations. The displayed equation makes quantifiers literal intersections. The identity observer preserves current truth:

```math
1\in\phi(b)\quad\Longleftrightarrow\quad b\text{ is true in }N
```

The transported observer $`m`$ is exactly the required shift:

```math
\phi(m(b))=\{n:n(m(b))\text{ is true}\}
=\{n:nm\in\phi(b)\}=R_m(\phi(b))
```

Haecceities distinguish different current individuals. Equality is preserved by its predicate characterization. All the defining shift-model conditions therefore hold.

**Representation theorem.** Every C + OS Henkin model has an elementary extension isomorphic, as a current typed structure with its logical operations, to a shift model.

**Strong completeness theorem.** For any set $`\Gamma`$ of sentences,

```math
\Gamma\vdash_{\mathrm C+\mathrm{OS}} A
\quad\Longleftrightarrow\quad
\text{every shift model satisfying }\Gamma\text{ satisfies }A
```

Soundness was proved above. If the deduction fails, general Henkin completeness supplies a C + OS model of $`\Gamma\cup\{\neg A\}`$. The elementary extension and representation preserve those sentences and give a shift countermodel. Neither the optional premises nor OS are automatically necessitated. The theorem concerns current OS, not ☐OS.

## 7. One fixed monoid in a countable language

Choose the initial countermodel and the extension countable. The resulting monoid is a subset of the countable tt-domain. Enumerate it as $`(m_k)`$, allowing repetitions. Mapping each natural-number letter $`k`$ to $`m_k`$ extends to a surjective homomorphism

```math
\pi:\mathbb N^*\longrightarrow M,
```

where $`\mathbb N^*`$ is the monoid of finite words under concatenation. Replace $`\phi(b)`$ by $`\pi^{-1}(\phi(b))`$ and transport all higher domains along the resulting bijection onto the new proposition domain. Surjectivity makes inverse image injective on subsets of $`M`$, and inverse image preserves every intersection and Boolean operation. Moreover,

```math
R_u(\pi^{-1}(A))=\pi^{-1}(R_{\pi(u)}(A))
```

Thus each word shift is admitted, and truth at the empty word agrees with truth at $`1`$. All domains remain countable. Countable-domain shift models on this single fixed monoid are strongly complete, also with a countable signature of additional constants. It suffices to require admission of the one-letter shifts: composition supplies the rest. The indices are metatheoretic objects and introduce no new object-language type.

## 8. Scope and sources

Henkin closure is essential; full function domains impose stronger principles. The representation may require an elementary extension, rather than representing the original model itself. Quantifier intersections are infima of admitted ranges, not Boolean Completeness for every admitted predicate's current extension. The [comparison and examples](observer-shift-boundaries.md) show why the indexing monoid does not by itself determine native necessity or an action on the entire typed structure.

Construction and completeness proof: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), *Shift models for logical observer separation*, §§1–10, unpaginated. This presentation retains the full completeness argument; its concrete example is in the linked companion. [Source hashes](../evidence/source-manifest.json) · [Review evidence](../evidence/proof-reviews.json).

The BF/Functionality/Tractarianism equivalences are Bacon and Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.1 and n. 27, pp. 20–21. The [existing OS recovery proof](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observers.md#3-os-entails-c-and-bf-over-h) supplies OS ⇒ BF. For general completeness and comparison with action models, see Bacon and Dorr, [*Classicism*, draft of 1 July 2022](https://andrew-bacon.github.io/papers/Classicism.pdf), §3.1, Theorem 3.2 and n. 64, PDF pp. 44–45; §3.4, Theorem 3.23; and §3.5, PDF p. 58. That draft has different pagination from the database's 2023 draft. The observer extension and shift representation are the new arguments here.
