# Full Gallin semantics and external atomic joins

Original mathematical argument, direct source misc; unpaginated.

## 1. Target, signatures, metatheory, and completeness

Fix a well-founded ambient universe $V$ of sets with ZFC as the metatheory. All occurrences of “all subsets,” “all functions,” “finite,” and “well-founded proof tree” are external in this fixed universe. Assertions of *ZFC-provability* are distinguished from truth in that universe. We do not assert that ZFC proves its own global soundness.

The object language remains C's relational language:

$$
e,\quad t,\quad \sigma\to\tau\ \text{only when }\tau\ne e.
$$

There are no object-language type quantifiers and no functions returning individuals. In particular, graphs used to represent successor or arithmetic operations have admitted relational types. Application below is explicitly parenthesized or written with a tuple.

For arbitrary infinite sets $E,W\in V$, put

$$
D_e=E,\qquad D_t=\mathcal P^V(W),\qquad
D_{\sigma\tau}=(D_\tau)^{D_\sigma}.
$$

All functions on the right belong to $V$. Interpret lambda by actual abstraction, application by evaluation, and propositional operations by set operations. Quantification is pointwise:

$$
w\in\llbracket\forall x^\sigma A\rrbracket
\ \Longleftrightarrow\
\forall a\in D_\sigma\;w\in\llbracket A\rrbracket_{x:=a}.
$$

Identity at *every* type is literal equality, represented by $W$ when true and $\varnothing$ otherwise. Thus C's definition $\Box p:=(p=\top)$ gives universal-world necessity.

A signature $\Sigma$ supplies constants at admitted types, interpreted arbitrarily in their domains. Distinct symbols need not have distinct values. The **pure** language has no nonlogical constants. Its validity is unchanged if an unused relational constant is added to meet the bundle's signature-admissibility convention. Complexity statements use an effectively presented countable signature; the strongest lower bounds already concern closed pure sentences. The noncompactness example uses the explicitly specified admitted signature $\{P^{et}\}$.

Write $\mathcal G^\Sigma_\infty(V)$ for these pointed models, including every interpretation of $\Sigma$, every infinite cardinal pair $(|E|,|W|)$, and every $w\in W$. Define **local consequence**

$$
\Gamma\models_{\mathrm{full},\infty}^{V,\Sigma} A
\quad\Longleftrightarrow\quad
\forall(G,w)\in\mathcal G^\Sigma_\infty(V)
\bigl[(\forall B\in\Gamma\;G,w\models B)\Rightarrow G,w\models A\bigr].
$$

All premises hold at the *same* point and under the same constant interpretation. Global-premise consequence instead requires every premise at every world; equivalently use $\{\Box B:B\in\Gamma\}$ as local premises.

The target validity theory is
$\mathrm{Val}_{\mathrm{full},\infty}^{V,\Sigma}
=\{A:\varnothing\models_{\mathrm{full},\infty}^{V,\Sigma}A\}$.
Weak completeness means capturing this set. Strong completeness means capturing consequence for arbitrary sets $\Gamma$ of sentences in the fixed signature. They are different requirements.

Put

$$
CC=C+\Box FC+I_e+I_t,
$$

where $I_e,I_t$ are the **quantified Frege Axioms of Infinity**, not merely the finite-lower-bound schemata. In the full models above, $I_e$ is equivalent to external infinitude of $E$, and $I_t$ to external infinitude of $W$. The latter follows because its counted domain is $\mathcal P(W)$, finite exactly when $W$ is finite. The finite-cardinality lemma in §3 establishes the required standardness.

All these models satisfy CC. C-soundness is the ordinary compositional argument, respecting the H-theoremhood condition on Logical Equivalence. A locally serial relation has an external selecting function by metatheoretic Choice; fullness admits that function at every permitted relational output type. Hence every closed FC instance is true at every world. This use of ZFC must not be exported to a choiceless metatheory.

The existing reconstruction of CC concerns **choice-closed general/Henkin Gallin hierarchies**. It does not establish completeness for the narrower full class. Its original source arguments are preserved; see the local-source list in §12.

## 2. A sharp reduction: full second-order validity

The following gives a useful calibration of the whole target, beyond its arithmetic fragment.

**Theorem 2.1.** Over ZFC, full Gallin validity for closed pure C sentences with infinite $E,W$ and ordinary full second-order logical validity over arbitrary nonempty domains are computably many-one reducible to one another.

This concerns **validity**, allowing changes of the auxiliary domain in the reduction. It does not claim that second-order formulas over a fixed domain express every higher-type property over that same domain.

### 2.1 Full second-order logic to pure C

First put the input second-order sentence $\psi$ in relational form. Replace function symbols and function quantifiers by total single-valued graphs, guarding the relevant quantifiers by their graph conditions. Replace equality of relations by coextension. This is an effective translation preserving full semantics.

Introduce a variable $D^{et}$ to mark a nonempty local subdomain of individuals. Relativize first-order quantifiers to $D$. Represent each $r$-ary relation by an original variable of type $e\cdots et$, using only its extension on $D^r$ at the evaluation world. Relativized relation equality means coextension on $D^r$, not original identity between intensions. Universally bind $D$ and all variables standing for nonlogical symbols; guard individual constants by membership in $D$. Call the resulting closed pure C sentence $R(\psi)$. Its form is “every nonempty $D$, with every interpretation of the relationalized signature on $D$, satisfies $\psi$.”

At a fixed world of a full hierarchy, every external subset of $D^r$ is the local extension of an admitted relation. Induction on $\psi$ therefore proves that a full-valid $\psi$ makes $R(\psi)$ true everywhere.

Conversely, let a nonempty structure with domain $A$ refute $\psi$. Take $E$ to be a tagged disjoint union of $A$ and $\omega$, and take $W=\omega$. Interpret $D$ rigidly as the copy of $A$, and interpret its relations and constant variables by the given structure, also rigidly. At every world the relativized translation has exactly its original second-order semantics. It refutes $R(\psi)$. Both Infinity axioms remain true. Thus

$$
\psi\in\mathrm{Val}_{SO}
\quad\Longleftrightarrow\quad
R(\psi)\in\mathrm{Val}_{\mathrm{full},\infty}^{V,\mathrm{pure}}.
$$

The relativized subdomain is essential: merely using $E$ as the second-order domain would lose finite countermodels.

### 2.2 Pure C to full second-order logic

A finite C sentence $A$ uses finitely many types. Include all their subtypes and the types of the logical constants actually occurring in the term syntax. Use an auxiliary one-sorted second-order language with disjoint unary predicates for these typed domains and a world domain $U_s$. Introduce:

- a binary relation $\operatorname{Ev}(p,w)$ between $U_t$ and $U_s$;
- a ternary application graph $\operatorname{App}_{\sigma\tau}(f,x,y)$ for every required arrow type;
- appropriately sorted symbols for the finitely many constants and logical operations actually needed.

Let $\operatorname{Hierarchy}_A$ assert nonemptiness, the sort conditions, total single-valued application, extensionality, and the following **full second-order** clauses:

$$
\forall X\subseteq U_s\;\exists p\in U_t\;
  \forall w\in U_s\,
  \bigl(\operatorname{Ev}(p,w)\leftrightarrow Xw\bigr),
\tag{2.1}
$$

with extensionality for $U_t$, and

$$
\forall R\bigl[
 \operatorname{Function}_{U_\sigma,U_\tau}(R)\to
 \exists f\in U_{\sigma\tau}\,
 \forall x\in U_\sigma\,\forall y\in U_\tau\,
   (\operatorname{App}_{\sigma\tau}(f,x,y)\leftrightarrow R(x,y))
 \bigr].
\tag{2.2}
$$

Here a graph in $\operatorname{Function}_{U_\sigma,U_\tau}$ is supported on that product and gives each input exactly one output. All subsets and graphs are quantified in *full second-order semantics*. Add that $U_e,U_s$ are infinite, expressed, in ZFC, by existence of an injective nonsurjective graph on each. This is auxiliary second-order notation, not a forbidden original type $ee$.

Include in $\operatorname{Hierarchy}_A$ the defining graph clauses for each logical constant occurring in $A$, including when it occurs as a first-class value. Negation and conjunction act pointwise on evaluation. The equality constant at any type returns the proposition $U_s$ or $\varnothing$ according to literal sorted equality of its arguments. The universal-quantifier constant takes a predicate $P$ to the proposition $q$ specified by

$$
\forall w\in U_s\,
 [\operatorname{Ev}(q,w)\leftrightarrow
   \forall x\in U_\sigma\,\exists r\in U_t\,
     (\operatorname{App}_{\sigma t}(P,x,r)\land\operatorname{Ev}(r,w))].
$$

Here logical constants of curried type have their full curried graph constrained, at every argument, rather than being treated as uninterpreted operations.

For explicit term translation, define a first-order formula
$\operatorname{Den}_a(\bar x,u)$ recursively for each subterm $a$. A variable uses identity with its assigned value; a constant uses its constrained interpretation. Application existentially combines the two subterm denotations with the appropriate application graph. A lambda term $\lambda x^\sigma.b^\tau$ uses
$$
\forall x\in U_\sigma\,\forall v\in U_\tau\,
 [\operatorname{App}_{\sigma\tau}(u,x,v)
   \leftrightarrow \operatorname{Den}_b(\bar x,x,v)].
$$
Structural induction proves existence and uniqueness of every denotation: totality handles application, graph-fullness handles lambda abstraction, and the defining clauses plus (2.1)–(2.2) give all the logical constants. Extensionality proves uniqueness in the function cases. For a sentence $A:t$, take
$$
A^*(w):=\exists p\in U_t\,
  (\operatorname{Den}_A(p)\land\operatorname{Ev}(p,w)).
$$
All these formulas are finite and first-order in the auxiliary sorted presentation. Thus no table of truths of arbitrary formulas is added to the translation.

Let

$$
S(A):=\operatorname{Hierarchy}_A\to
             \forall w\in U_s\,A^*(w).
$$

Auxiliary predicates and constants may be treated as nonlogical symbols whose interpretations vary when testing validity. They may instead be universally quantified after relationalization.

Every full Gallin hierarchy, restricted to these finitely many sorts and represented by tagged disjoint copies, satisfies $\operatorname{Hierarchy}_A$. Conversely, (2.1) identifies $U_t$ with the full powerset of $U_s$; induction on type complexity using (2.2) identifies every arrow domain with the full function set between its already identified input and output domains. This finite full hierarchy extends to all omitted admitted types by the same recursive construction. Induction on syntax preserves $A$. Therefore

$$
A\in\mathrm{Val}_{\mathrm{full},\infty}^{V,\mathrm{pure}}
\quad\Longleftrightarrow\quad S(A)\in\mathrm{Val}_{SO}.
$$

All syntax transformations are effective. This proves Theorem 2.1. The same forward reduction handles any fixed effectively coded admitted signature because each sentence mentions only finitely many constants.

**Interpretation.** Fullness does not acquire a simpler validity problem merely by being presented in C's relational language with worlds. Conversely the modal packaging causes no additional weak-validity obstacle beyond ordinary full second-order logic. This is a finite-type powerset-coding adaptation, related to the reductions discussed in Väänänen, §8, pp. 17–18; it is not a new attribution to Gallin.

Väänänen's Theorem 4(1), p. 18, states that full second-order validity is a complete $\Pi_2$ set of natural numbers in the **set-theoretic Lévy hierarchy**. Together with Theorem 2.1 this transfers that calibration to the present weak-validity problem, in the source's completeness convention for parameter-free number predicates. Computable substitutions preserve the defining level and transfer the hardness reductions. No arbitrary truth-set parameter is allowed. This $\Pi_2$ is not the analytical-hierarchy notation $\Pi^1_2$. The elementary obstruction below does not depend on using the published sharper classification.

## 3. Noncompactness while retaining both Infinity axioms

Work in $\Sigma_0=\{P^{et}\}$, and put $\nu=(et)t$. Use exactly the bundle's definitions of $\mathbf0_e,\operatorname{Suc}_e,\operatorname{FiniteCardinality}_e$. Define

$$
\begin{aligned}
\operatorname{Fin}(P)&:=
  \exists Z^\nu\,
    (\operatorname{FiniteCardinality}_e(Z)\land ZP),\\
L_n(P)&:=
  \exists x_1^e\cdots x_n^e\,
   \left(\bigwedge_i Px_i\land\bigwedge_{i<j}x_i\ne x_j\right).
\end{aligned}
$$

**Lemma 3.1.** In a full hierarchy,
$G,w\models\operatorname{Fin}(P)$ iff
$P_w=\{a\in E:w\in P(a)\}$ is externally finite.

**Proof.** Let $z_n=\operatorname{Suc}_e^n(\mathbf0_e)$, and let
$N=\{z_n:n<\omega\}$, an external set of objects of type $\nu$.
Fullness at $\nu t$ supplies its rigid characteristic predicate, with value $W$ on $N$ and $\varnothing$ elsewhere. This predicate contains zero and is successor-closed, so the impredicative definition of $\operatorname{FiniteCardinality}_e$ excludes every object outside $N$. Conversely, at any world, external finite induction puts each $z_n$ in every predicate locally containing zero and closed under successor. Thus the local extension of numberhood is exactly $N$.

A second induction proves
$$
w\in z_n(X)\quad\Longleftrightarrow\quad
|\{a\in E:w\in X(a)\}|=n.
$$
The zero clause says the extension is empty. The successor clause removes a member using literal individual inequality; an $(n+1)$-element extension has such a removal, and a removal leaving $n$ members makes the original size $n+1$. Combining the two inductions proves the lemma. The same proof works at any counting type, with its actual domain in place of $E$. $\square$

Now put
$$
\Gamma=\{\operatorname{Fin}(P)\}\cup\{L_n(P):1\le n<\omega\}.
$$

Every finite $\Gamma_0\subseteq\Gamma$ has a full model with **$E=W=\omega$**: choose a finite set of individuals of size at least the largest displayed bound and interpret $P$ rigidly as that set. Both quantified Infinity axioms and all of $\Box FC$ hold. The whole $\Gamma$ has no full model by Lemma 3.1.

**Theorem 3.2.** The specified local full consequence relation is noncompact. Hence no finitary calculus, even with a non-effective axiom set, is both sound and strongly complete for it.

Indeed a finite proof of contradiction from $\Gamma$ uses only a finite subset, contradicting the full models just constructed. Boxing every displayed premise also proves noncompactness for global-premise consequence.

This is **not** the old $\operatorname{Fin}_e$ assertion that the entire individual domain is finite. Only the named property's extension is finite. Nor does this argument establish noncompactness for pure *sentences* without parameters: existentially closing $P$ separately in the premises would destroy their shared witness.

It also follows that no ordinary first-order theory in added sorts or symbols has exactly this full class as its reduct class. First-order compactness applied to that theory together with $\Gamma$ would give an impossible full reduct.

## 4. Weak-validity obstructions, including countable proof trees

### 4.1 An explicit arithmetic reduction

For a first- or second-order arithmetic sentence $\psi$, use relational second-order Peano arithmetic on
$$
z^e,\quad S^{eet},\quad A^{eeet},\quad M^{eeet}.
$$
Its finite sentence $PA_2(z,S,A,M)$ asserts a total single-valued injective successor with zero outside its range, induction over every $et$-property, and total single-valued addition/multiplication graphs satisfying the usual recursion equations.

Put
$$
V_\psi:=
\forall z,S,A,M\,
  (PA_2(z,S,A,M)\to\psi^\dagger(z,S,A,M)).
\tag{4.1}
$$

For second-order arithmetic, translate number-set membership by application and set equality by
$\forall x(Xx\leftrightarrow Yx)$.
**Do not use primitive $et$-identity:** it compares entire world intensions, not their extensions at one world.

At any world, fullness makes the induction range all subsets of $E$. The external successor orbit of zero is an available inductive subset, so it exhausts $E$. Injectivity and exclusion of zero identify this orbit with $\omega$; the recursion equations then fix the standard arithmetic graphs. All subsequent set quantifiers range extensionally over $\mathcal P(\omega)$. Consequently

$$
V_\psi\in\mathrm{Val}_{\mathrm{full},\infty}^{V,\mathrm{pure}}
\quad\Longleftrightarrow\quad
(\omega,\mathcal P^V(\omega))\models\psi.
\tag{4.2}
$$

For the reverse implication's counterexample take $E=W=\omega$ and the rigid usual arithmetic graphs. This explicitly retains both Infinity axioms.

Already first-order arithmetic in (4.2) proves that full validity is not c.e. If it were, its computable preimage would enumerate true arithmetic. Racing a sentence and its negation would decide arithmetic truth, contrary to its undefinability/undecidability.

The second-order version gives more. The set of all true second-order arithmetic sentences is **not lightface projective**. If a parameter-free second-order arithmetic formula $\theta(n)$ defined that whole truth set, the diagonal lemma would give a sentence $\delta$ equivalent in the standard structure to $\neg\theta(\ulcorner\delta\urcorner)$, a contradiction. Every lightface projective definition is such a formula. Thus full Gallin validity is not lightface projective either.

### 4.2 What this rules out for infinitary proof systems

**Theorem 4.3.** Suppose proofs are countable well-founded rooted trees, coded by reals, with arithmetically specified local correctness, natural-number-coded conclusions, and no nonprojective oracle hidden in the axiom/rule conditions. Such a system cannot be both sound and weakly complete for the target.

**Proof.** Its theorem predicate has the form
$$
\exists T\,
 [\operatorname{Root}(T,n)\land
  \operatorname{LocalCorrect}(T)\land\operatorname{WF}(T)].
$$
Local correctness is arithmetical and well-foundedness is $\Pi^1_1$, so this is $\Sigma^1_2$. It is projective, contradicting §4.1 if it equals full validity. Uniformly hyperarithmetical local data give the same projective obstruction. $\square$

For a standard presentation with number-indexed rule instances and arithmetical axiom and premise relations, a sharper bound comes from the least rule-closed set:
$$
n\in D\quad\Longleftrightarrow\quad
\forall X\subseteq\omega\,
  [X\text{ contains the axioms and is rule-closed}\to n\in X].
$$
The bracketed condition is arithmetical in $X$, giving a $\Pi^1_1$ upper bound. Transfinite generation ranks yield well-founded derivation trees; induction on trees gives the converse. The broader $\Sigma^1_2$ bound suffices here.

These are precise restrictions on proof formats. They do not exclude arbitrary non-effective calculi, uncountable set-labelled certificates, or more complex side conditions. Such resources would have to be stated openly and justified.

## 5. The omega-rule: useful and insufficient

At any fixed counting type $\sigma$, let
$z_n^\sigma=\operatorname{Suc}_\sigma^n(\mathbf0_\sigma)$.
The rule, denoted $(\omega_\sigma)$,

$$
\frac{\{\Gamma\vdash B(z_n^\sigma):n<\omega\}}
 {\Gamma\vdash
   \forall Z\,(\operatorname{FiniteCardinality}_\sigma(Z)\to B(Z))}
\tag{5.1}
$$

is sound for full local consequence. Lemma 3.1 says exactly that every object satisfying the quantified numberhood predicate is one of these numeral objects. $B$ may contain higher-type parameters and modalities. The same assignment and premise context must be maintained in every premise.

This rule refutes the $\Gamma$ of §3: for each standard $n$, $L_{n+1}(P)$ gives $\neg z_n(P)$; the rule yields that no finite cardinality applies to $P$, contradicting $\operatorname{Fin}(P)$.

For ordinary first-order arithmetic, the unrestricted omega-rule really is complete. Use negation normal form and true closed arithmetic literals as decidable initial sequents. Induct on formula complexity: select a true disjunct or an existential numeral witness; use both conjuncts; at a universal number quantifier use all numeral instances. Every premise has smaller formula complexity, producing a countable well-founded proof. This is a fragment theorem, not a full higher-type completeness argument. Frittaion's directly consulted paper gives substantially stronger recursive and primitive-recursive coding results; see §12.

There is a structural reason to keep the scope clear. Start with the full hierarchy over $E=W=\omega$, in its countable many-sorted first-order presentation, and name every base element. A countable elementary substructure retains both bases, comprehension, Choice, both quantified Infinity axioms, and every standard numeral. It has no nonstandard Frege numbers: any element of the substructure satisfying numberhood also satisfies it in the full source, hence is a numeral. All rules $(\omega_\sigma)$ remain semantically sound there. Yet its proposition domain is countable and omits most of $\mathcal P(\omega)$.

This example proves that standard arithmetic plus internal choice/comprehension does not *force external fullness*. Because it is elementary in a full model, it satisfies all full validities; it does **not by itself** prove weak incompleteness. Theorem 4.3 supplies that different conclusion for the specified proof systems, including ZFC with an ordinary number omega-rule when given in that proof format.

## 6. A natural exact condition: external atomic joins

Consider a general Gallin hierarchy with literal identity, extensional application, pointwise logic, and lambda closure. Assume its represented worlds are **principal**: each $w\in W$ has the singleton proposition $\delta_w$. This follows in the auxiliary Gallin presentation from world equality and comprehension. In CC's reconstructed presentation the worlds are propositional atoms; the representation and boxed Actuality supply the same condition.

For $\tau=\sigma_1\cdots\sigma_n t$, including $n=0$, let
$$
X_\tau=W\times D_{\sigma_1}\times\cdots\times D_{\sigma_n},
\qquad
\beta_\tau(f)=
\{(w,\bar a):w\in f[\bar a]\}.
$$

Repeated extensionality identifies $D_\tau$ with a Boolean subalgebra
$B_\tau\subseteq\mathcal P(X_\tau)$. Its order is C's algebraic order, and its Boolean operations are the set operations on these supports. For every point $(w,\bar a)$, lambda and literal identity supply
$$
\lambda\bar x.\ \delta_w\land\bigwedge_i x_i=a_i.
$$
Its support is that singleton. Hence the atoms of $B_\tau$ are precisely the singleton points.

**Theorem 6.1.** Under these hypotheses, the following are equivalent:

1. The hierarchy is full on its actual $E,W$.
2. Every $B_\tau$, for every admitted relational $\tau$, has joins of every external set of its elements.
3. Every $B_\tau$ has joins of every external set of its atoms.

**Proof.** Fullness gives the powerset representation at every relational type, so (1) implies (2), and (2) implies (3).

Assume (3). For an arbitrary external $A\subseteq X_\tau$, let $b$ be the join in $B_\tau$ of $\{\{x\}:x\in A\}$. Certainly $A\subseteq b$. If $x\in b\setminus A$, then $b\setminus\{x\}\in B_\tau$ is a strictly smaller upper bound of the same family, contradicting leastness. Thus $b=A$. Therefore $B_\tau=\mathcal P(X_\tau)$.

At $t$ this gives $D_t=\mathcal P(W)$. For an arrow $\sigma\tau$, an arbitrary actual function $F:D_\sigma\to D_\tau$ determines a support on $X_{\sigma\tau}$ by the supports of its values. Surjectivity of $\beta_{\sigma\tau}$ supplies an operation with that support; injectivity of $\beta_\tau$ makes its value at each input equal to $F$'s. Thus every such $F$ is admitted. This proves (1). $\square$

The principal-world hypothesis is necessary for this argument. Abstract complete atomic Boolean algebras can have Stone representations containing extra nonprincipal ultrafilter points; their joins need not be represented as unions at those points. The intended Gallin/CC reconstruction avoids that problem explicitly.

### 6.1 The corresponding infinitary axiom scheme

For every set $I$ and every relational type $\tau$, consider the axiom $J^\tau_I$:

$$
\forall(a_i^\tau)_{i\in I}\,
\left[
 \bigwedge_{i\in I}\operatorname{Atom}_\tau(a_i)
 \to
 \exists b^\tau\left(
   \bigwedge_{i\in I}a_i\le b\ \land\
   \forall c^\tau\left[
       \bigwedge_{i\in I}a_i\le c\to b\le c
   \right]\right)
\right].
\tag{6.1}
$$

For $I=\varnothing$, the join is bottom. Quantification over the tuple $(a_i)_{i\in I}$ ranges over *every external assignment* to that tuple. All conjunctions and the quantifier block are genuinely set-indexed. This is an auxiliary infinitary language of $L_{\infty,\infty}$ character, not a previously available finitary C formula or an internal quantifier over family codes.

**Proved semantic characterization.** General Gallin models of CC satisfying all $J^\tau_I$ are exactly the full-standard target models, up to the specified representation. Theorem 6.1 proves the fullness assertion; Lemma 3.1 then makes the two Infinity axioms exactly the desired external base conditions.

This is a uniform structural axiom scheme. It does not say “every full validity is an axiom.” But a semantic characterization in a stronger logic is **not yet a complete proof system for that logic**. No unrestricted completeness theorem for this scheme is asserted here.

### 6.2 Why the existing Boolean Completeness axiom is insufficient

The recorded Boolean Completeness principle quantifies over an *available property*
$X^{\tau t}$. It gives joins/meets of families internally represented by such $X$. $J^\tau_I$ ranges instead over arbitrary external families, whether or not an internal family object exists.

A fresh proved-only Engine query, with
$\{\Box FC,I_e,I_t\}$ in the queried premises and empty background, confirms that CC already entails C5, Atomicity, boxed Actuality, and boxed Boolean Completeness. The relevant paths include:

- necessary-functional-choice-r-implies-necessary-plenitude-r;
- necessary-plenitude-r-implies-necessary-distinctness-necessary-r;
- necessary-plenitude-r-implies-atomicity-r;
- necessary-plenitude-r-implies-necessary-actuality;
- c5-and-atomicity-imply-necessary-completeness.

Thus adding the existing BC record again cannot perform the missing task. External indexing is the new strength.

## 7. No fixed bounded-join condition forces full domains

**Theorem 7.1.** For every infinite regular cardinal $\kappa$, ZFC gives a non-full general Gallin model of CC whose relational Boolean algebras are closed under every external join of fewer than $\kappa$ elements, at every admitted type.

**Proof.** Choose an infinite $\mu\ge\kappa$, and let $\lambda=2^\mu$. Then
$\lambda^{<\kappa}=\lambda$. Form the full hierarchy $F$ on
$E=W=\lambda$. Choose regular $\theta$ large enough that the entire coded hierarchy, its domains and structural operations belong to $H_\theta$.

There is $M\prec H_\theta$ with
$$
|M|=\lambda,\quad \lambda\subseteq M,\quad
\lambda,F\in M,\quad M^{<\kappa}\subseteq M.
$$
For completeness, construct an elementary chain of length $\kappa$. At each successor stage add every sequence of length less than $\kappa$ from the preceding stage and take a Skolem hull. The size remains $\lambda$ by $\lambda^{<\kappa}=\lambda$. Regularity of $\kappa$ puts every short sequence from the final union inside some stage, so it is added at the next. The union is elementary. Include the finitely tagged base sorts and all countably many type-domain objects in the initial hull.

Intersect each applicative sort of $F$ with $M$. This is an elementary substructure in the ordinary many-sorted presentation, by the Tarski–Vaught criterion with $F$ as parameter. **Recursively restrict and transport** arrow objects to the reduced argument domains; do not regard an old function with its old domain as already a function on the new domain. This representation is injective: elementarity supplies a distinguishing argument in $M$ for any two distinct old functions in $M$. Application and all logical operations transport correctly. Both base domains remain $\lambda$.

An external family of fewer than $\kappa$ reduced objects lifts uniquely to a family of old objects in $M$. An enumeration of that family belongs to $M$ by sequence closure. Its join in the old full sort is uniquely definable from the family, the hierarchy and its type, so belongs to $M$. Restriction takes this join to the pointwise union of the reduced family. Thus all the required joins exist after transport.

Elementarity preserves Choice and both quantified Infinity axioms. But the proposition domain is $\mathcal P(\lambda)\cap M$, of size exactly $\lambda$: the upper bound is $|M|$, and its singleton propositions give the lower bound. Cantor's theorem gives $\lambda<2^\lambda$, so this domain is not full. $\square$

This includes closure under all countable joins by taking $\kappa=\omega_1$. It also explains why repeatedly strengthening countable family rules need not force all external subsets.

**Scope limitation.** These particular models are elementary in full models and therefore satisfy every finitary full-valid sentence. Theorem 7.1 refutes the proposed *structural characterization* by any fixed bounded-join requirement. It does not, by itself, show weak incompleteness of every calculus with bounded branching. Theorem 4.3 gives a separate proof-theoretic obstruction under its precise hypotheses.

## 8. Two positive completeness results

### 8.1 A first-order modal fragment over arbitrary infinite bases

Let $\mathcal F$ consist of formulas built from individual equality, individual constants, relational constants $R:e\cdots et$ applied only to individuals, Boolean connectives, individual quantifiers, and $\Box$. Propositional constants are allowed as nullary relations. There is **no quantification over relations**, no comparison of arbitrary relational intensions by identity, and no higher-type arguments.

Introduce ordinary first-order sorts $E,W$, a distinguished $w_0$, and a relation $R^*(w,\bar x)$ for each original $R$. Define the standard translation:
$$
\begin{aligned}
\operatorname{ST}_w(R[\bar x])&=R^*(w,\bar x),\\
\operatorname{ST}_w(x=y)&=(x=y),\\
\operatorname{ST}_w(\forall x^e B)&=\forall x^E\,\operatorname{ST}_w(B),\\
\operatorname{ST}_w(\Box B)&=\forall v^W\,\operatorname{ST}_v(B),
\end{aligned}
$$
commuting with Boolean connectives. Let $T_\infty$ contain all ordinary first-order finite lower bounds on both sorts.

**Theorem 8.1.** For any $\Gamma\cup\{A\}\subseteq\mathcal F$,
$$
\Gamma\models_{\mathrm{full},\infty}^{V,\Sigma} A
\quad\Longleftrightarrow\quad
T_\infty\cup\{\operatorname{ST}_{w_0}(B):B\in\Gamma\}
\vdash_{FO}\operatorname{ST}_{w_0}(A).
$$

**Proof.** Every full hierarchy yields the indicated first-order structure. Conversely, every first-order structure with infinite $E,W$ expands to a full hierarchy by taking all external function spaces and assigning each relational constant its given support. Syntax induction gives the truth equivalence. Ordinary first-order completeness proves the displayed equivalence. $\square$

Thus there is a c.e. sound **strongly complete** calculus for this precise fragment. It does not contradict §3 because $\operatorname{Fin}(P)$ uses higher-type quantification.

For validity alone, a finite leading universal block of relation variables may also be admitted: replace them by arbitrary fresh relation symbols before applying the translation. This additional observation is not a strong-completeness claim for premises with such universal higher-order prefixes.

### 8.2 A specified hierarchy has a complete infinitary diagram calculus

Fix one full hierarchy $G$, its signature interpretation, and a point $w$. In its many-sorted relational presentation name every domain element, including all worlds and higher-type objects. Supply the **atomic diagram**, namely the primitive application, membership/evaluation and equality facts about these named elements, together with their true negations. Logical constructors and lambda can be eliminated by their defining relational formulas as in §2.2; an oracle for arbitrary sentence truth is not an initial axiom.

In addition to the usual Boolean rules and existential witness introduction, allow at every sort $s$ the rule $U_s^G$:
$$
\frac{\{B(c_a):a\in D_s^G\}}{\forall x^s B(x)}.
\tag{8.2}
$$

**Theorem 8.2.** For each finitary sentence $A$ in this presentation,
$$
G\models A\quad\Longleftrightarrow\quad
A\text{ has a well-founded set-sized proof from its atomic diagram}.
$$

**Proof.** Soundness is induction up the proof tree. For completeness put $A$ in negation normal form and induct on its logical complexity with named parameter values. A true literal is in the diagram (ground application terms can first be evaluated using primitive tables). A true existential has a named witness; a true disjunction has a true disjunct; a conjunction has both true conjuncts. A universal has a true instance for every named domain element, so apply $U_s^G$. The height decreases with formula complexity, and each branching set is a set. ZFC Choice chooses the needed family of witness subproofs. $\square$

This theorem is useful but its resource cost is explicit. The names and atomic data include the actual external hierarchy and need not be countable or algorithmically checkable. It is a completeness theorem for **truth in one supplied structure**, not for validity across every cardinal pair and interpretation.

Applying this separately for every full $G$ does not produce a uniform proof of a validity. A rule demanding proofs for *all* such $G$, without a syntactic way to verify that coverage, would merely repackage the semantic target.

Nor is it correct to conclude that proper-class-sized proofs are unavoidable in every possible solution. In a fixed countable language the set of sentence codes is a set; taking the supremum of least countermodel sizes gives some set-sized weak countermodel bound in $V$. A similar supremum can be taken over all sets of premises in that fixed language. **Defining a bound by the very countermodels whose existence is at issue is semantic information, not an independently supplied completeness proof or effective bound.**

## 12. Sources, attribution, and checks

### Primary literature directly consulted

1. **Jouko Väänänen, “Second order logic and set theory.”** [Author's PDF](https://www.mv.helsinki.fi/home/jvaanane/Vaananen_Compass.pdf), §§3–4, pp. 4–8; §8, especially Theorems 3–4, pp. 17–19; §9, pp. 19–21. Theorem 4(1) gives the set-theoretic $\Pi_2$ validity classification. The powerset coding motivates the explicit adaptation in §2, whose details and signature restrictions are proved here. Its references identify Hintikka and Montague's earlier reductions; those originals were not directly inspected. The paper's “weak/strong logical consequence” terminology differs from *weak/strong completeness* as defined in §1.
2. **Emanuele Frittaion, “Completeness of the primitive recursive omega-rule.”** [Author's arXiv paper](https://arxiv.org/pdf/2110.01270), Definition 1.1, pp. 3–4; Theorem 2.2, p. 7; Corollary 3.9, pp. 16–17. This establishes arithmetic completeness with carefully distinguished proof encodings. It is not a completeness theorem for all external higher-type domains.
3. **Guillermo Badia and John L. Bell, “A parametrized axiomatization for a large number of restricted second-order logics.”** [Published article](https://doi.org/10.1093/logcom/exad050); [author manuscript](https://arxiv.org/pdf/2207.02709), §2 rule R3, pp. 2–3; Theorems 8–9, pp. 6–7. Their infinitary system is strongly complete for countable premises when predicate ranges are generated by a specified countable collection of defining formulas with parameters. It does not range over every external subset. Transferring it unchanged would replace the user's full-standard target.
4. **Ryota Akiyoshi and Grigori Mints, “Analysis and Extension of Omega-Rule.”** [Author manuscript](https://arxiv.org/pdf/0904.4742), abstract and introduction, pp. 1–3. Its extended capital-$\Omega$ rule concerns cut elimination for a specified subsystem of analysis. “Complete cut elimination” there is not full-standard semantic completeness.

The proofs in §§2–8 were checked for fixed relational types, local versus global truth, both Infinity axioms, extensional versus intensional identity, and external versus internally represented families. A focused read-only agent independently audited the two validity reductions, noncompactness lemma, proof-complexity obstruction, principal-world qualification, and bounded-join construction. This does not substitute for a human referee or a formal proof.

Existing source proofs and records were not changed. No Lean compiler, deployment, or database rebuild was requested or used.
