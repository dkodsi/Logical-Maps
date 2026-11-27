# Relational Choice for well-ordered quotients

Suppose an equivalence relation $E$ on a represented set $X$ of type $\sigma$ has a represented strict ordering $<$ of its equivalence classes. If the actual ordered quotient has the order type of a computable well-order, local Relational Choice supplies a transversal. This covers every ordinal below the Church–Kleene ordinal $\omega_1^{\rm CK}$. The order type is an external hypothesis on this particular instance. The unrestricted [Relational Choice question](relational-choice-r-implies-transversal-choice-r.html) remains open.

### Comparing two well-orders

Suppose first that some represented subset $D$ of an admitted type $\tau$ carries an actual strict well-order $\prec$ isomorphic externally to $X/E$. Each point of $D$ is an individual entity of its type. There is an admitted relation that assigns each member of $X$ its unique point in the corresponding position of $D$.

To construct it, for an admitted relation $R$ define the following current condition on $x\in X$ and $d\in D$, taking it false off that product.

$$
\Phi(R)(x,d)\ \longleftrightarrow\
  \bigl(\forall y<x\,\exists b\prec d\,R(y,b)\bigr)
  \ \land\
  \bigl(\forall b\prec d\,\exists y<x\,R(y,b)\bigr).
$$

The variable $y$ ranges over $X$ and $b$ over $D$. This operation is monotone for inclusion of current extensions. Comprehension gives $L(x,d)$ asserting that $R(x,d)$ holds for every admitted $R$ with $\Phi(R)\subseteq R$, using current inclusion. For each such $R$, monotonicity gives $\Phi(L)\subseteq \Phi(R)\subseteq R$. Hence $\Phi(L)\subseteq L$. Applying monotonicity again shows that the admitted relation $\Phi(L)$ itself qualifies in the definition of $L$. Thus $L$ and $\Phi(L)$ have the same current extension.

Induct externally on the ordinal position of the class of $x$. The two clauses of $\Phi(L)$ say that the positions of the proper predecessors of $[x]$ and of $d$ form the same set. By the induction hypothesis, every match used in those clauses identifies equal predecessor positions. Two ordinals with precisely the same smaller ordinals are equal. This proves that $L(x,d)$ holds exactly when $[x]$ and $d$ occupy the same position.

Apply Relational Choice at $(\tau,\sigma)$ to select one $x$ for each $d\in D$ with $L(x,d)$, allowing arbitrary outputs off $D$. The range restricted to $D$ is an admitted property and contains exactly one member of every $E$-class. This argument uses the external isomorphism only to compare ordinal positions. The admissible relation $L$ was constructed within the model.

### When the comparison order can be represented in arithmetic

For a finite quotient, take one representative of each class and the finite disjunction of their haecceities. Now suppose $X/E$ is an externally infinite well-order. The classes that have only finitely many predecessors form its first segment of type $\omega$. This segment is definable on representatives. An $x$ belongs to it just if every nonleast class up to and including $[x]$ has an immediate predecessor. Every infinite closed initial segment contains the class in position $\omega$, which violates this test.

Let $N_\sigma$ be the Frege finite cardinalities. Define an admitted predicate $T$ of such cardinalities by requiring that, for some $x$ in this first segment, there be a property counted by $n$ whose extension consists of precisely one representative of each class strictly below $[x]$ and nothing else. Each of these finitely many representatives can be supplied by a finite disjunction of haecceities, including the empty property at the least class. If $[x]$ has precisely $j$ predecessors, every such choice has external size $j$, and hence is counted by the standard $j$th numeral. Two Frege finite cardinalities counting the same property coincide. Thus $T$ contains exactly the external standard numeral denotations. They are pairwise distinct since $X$ contains arbitrarily large finite sets. [Frege cardinality and arithmetic](../index.html#background/arithmetic)

The actual predicate $T$ contains zero and is closed under successor. The impredicative definition of $N_\sigma$ therefore gives $N_\sigma\subseteq T$. All the current numbers are standard. In particular the current sum and product have their ordinary values, by their defining recursion. Every computable presentation of a well-order on a subset of the natural numbers can now be represented at this point by its arithmetic definitions of the field and the order. Applying the comparison argument with $\tau=(\sigma t)t$ proves the result. It also applies to orderings computable relative to any admitted predicate of these numbers.

There is a related distinction in constructive type theory. Carlström proves that intensional choice, excluded middle and a weak extensionality principle yield extensional choice for setoids. The extensionality hypothesis concerns boolean-valued functions. His theorem is in a different theory from C. [Jesper Carlström, *EM + Ext⁻ + ACint ⇔ ACext*](https://www2.math.su.se/reports/2003/14/2003-14.pdf)

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, obtained this restriction on 27 November 2026. Two other GPT-6 research agents independently checked the fixed-point construction, the standard-number argument and the use of local choice.
