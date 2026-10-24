# External joins and limits of set coded proofs

Original mathematical argument, direct source misc; unpaginated.

## 1 An explicit atomic join rule

Use an auxiliary infinitary sequent language over the principal-world general Gallin presentation. It has the fixed C types, a world sort and evaluation relation for the presentation, and conjunctions indexed by arbitrary sets. The world sort is auxiliary; it does not add a type to the original C language. Each individual formula, context, and proof remains a set. Quantification and singleton-world existence have their ordinary Gallin meanings.

For an externally indexed family of terms $\bar a=(a_i^\tau)_{i\in I}$, define

$$
J_I^\tau(b;\bar a):=
 \left(\bigwedge_{i\in I}a_i\le_\tau b\right)
 \land
 \forall c^\tau\left[
   \left(\bigwedge_{i\in I}a_i\le_\tau c\right)\to b\le_\tau c
 \right].
$$

The atomic-join witness rule is

$$
\frac{
 \{\Gamma\vdash\mathrm{Atom}_\tau(a_i):i\in I\}
 \qquad
 \Gamma,J_I^\tau(b;\bar a)\vdash A
}{\Gamma\vdash A}
\quad(\mathrm{AJ}),
$$

where $b$ is fresh in $\Gamma,A,\bar a$. It is existential-witness elimination for a join, including the empty join when $I=\varnothing$. It does not require an internal property coding the family.

Combine AJ with the ordinary sequent rules for equality, quantifiers and infinitary conjunction, retaining their eigenvariable conditions, and the general Gallin/CC axioms. C's Logical Equivalence rule retains its H-theoremhood restriction: a local certificate supplies the required finite H-derivation. The proofs are well-founded trees with set-sized branching. Call this the **syntactic AJ calculus**. The incompleteness argument below applies to any implementation of these rules satisfying the explicit coding conditions in §3, so it does not depend on choices of harmless syntactic coding.

**Proposition 1.1.** AJ is sound at every pointed full-standard model, with local premises and arbitrary external index sets.

**Proof.** Fix a full model and an assignment satisfying $\Gamma$. The first premises make each interpreted $a_i$ an atom. At the relational type $\tau$, the full Boolean algebra has a join of their external set. Extend the assignment by interpreting the fresh variable $b$ as that join. Then $J_I^\tau(b;\bar a)$ holds, so the remaining premise gives $A$. Freshness makes the truth of $\Gamma$ and $A$ independent of this extension. The argument uses neither a bound on $I$ nor a cardinal restriction on the infinite bases. $\square$

This is a genuine inference rule. Its soundness does not provide a model-existence or completeness theorem.

## 2 Refuting the noncompactness premises

Retain the shared $P^{et}$, designated world $w$, counting type $\nu=(et)t$, Frege numerals $z_n^\nu$, and premises from [the preceding note, §3](full-gallin.md):

$$
\Gamma=\{\mathrm{Fin}(P)\}\cup\{L_n(P):n\ge1\}.
$$

Here $L_n(P)$ says that $P$ has at least $n$ distinct instances at the current world, and

$$
\mathrm{Fin}(P):=\exists Z^\nu\,
  (\mathrm{FiniteCardinality}_e(Z)\land Z(P)).
$$

The following gives an infinitary deduction from these premises, rather than appealing to the full-model cardinality lemma to assert that they are inconsistent.

In the auxiliary presentation choose a fresh $q=\delta_w$, using singleton-world existence and existential elimination. Its defining axiom is

$$
\forall v\,[\mathrm{Eval}(q,v)\leftrightarrow v=w].
$$

Thus current truth $\chi(w)$ gives the global algebraic inequality $q\le_t\chi$. This step is essential. A direct presentation in C would have to supply the corresponding actual-atom condition, including $\forall p(p\to q\le_t p)$, from CC's principal-world reconstruction. Atomicity alone is not being used as an unexplained substitute.

Define

$$
a_n:=\lambda Z^\nu.\ q\land Z=z_n.
$$

Each $a_n$ is an atom at $\nu t$: its support consists exactly of $(w,z_n)$. The rigid predicate $\lambda Z.Z=z_n$ without $q$ would not be an atom when there is more than one world.

The atom premises have finitary derivations. For $R\le a_n$, split on the truth of $R(z_n)$ at $w$. In the true case the singleton-world axiom and literal identity give $a_n\le R$, hence $R=a_n$; in the false case they give $R=\bot$. Also $a_n(z_n)$ holds at $w$, so $a_n\ne\bot$. These are ordinary equality, quantifier and extensionality deductions; no semantic completeness principle is invoked.

Apply AJ to the countable family $(a_n)_{n<\omega}$. In the fresh-witness subderivation assume $J_\omega^{\nu t}(b;\bar a)$.

First, $a_0\le b$ gives $b(z_0)$ at $w$. Define

$$
c_s:=\lambda Z.\ q\land b(\mathrm{Suc}Z).
$$

For each $n$, $a_{n+1}\le b$, together with the defining numeral identity $\mathrm{Suc}z_n=z_{n+1}$, gives $a_n\le c_s$. Infinitary conjunction introduction collects these inequalities. Join leastness yields $b\le c_s$. At $w$, therefore, $b$ contains zero and is closed under successor. Applying the defining impredicative induction condition for Frege numberhood gives

$$
\mathrm{FiniteCardinality}_e(Z)\to b(Z)
$$

at $w$.

Second, the finite counting argument for each fixed $n$ gives

$$
L_{n+1}(P)\to\neg z_n(P).
$$

It is the ordinary induction on the finite numeral from the earlier cardinality calculation, and does not assume an externally full number domain. Let

$$
c_P:=\lambda Z.\ q\land\neg Z(P).
$$

For each $n$, the local premise $L_{n+1}(P)$ and the singleton-world axiom give $a_n\le c_P$. Collect these inequalities and apply join leastness: $b\le c_P$.

Finally $\mathrm{Fin}(P)$ supplies a $Z$ with numberhood and $Z(P)$. The first part gives $b(Z)$, and the second gives $\neg Z(P)$. Discharge the fresh join witness using AJ and the singleton-world witness by existential elimination. This derives contradiction from $\Gamma$.

All countably many lower-bound premises refer to the same $P,w$. Neither base is made finite. The deduction is an ordinary mathematical derivation in the auxiliary calculus, not a Lean certificate. It shows that AJ addresses the concrete failure of compactness; it does not establish full completeness.

## 3 The complexity of set coded proofs

The hierarchy in this section is the **set-theoretic Lévy hierarchy**, not the analytical hierarchy. Bounded quantifiers are of the form $\forall x\in a$ or $\exists x\in a$.

**Theorem 3.1.** Suppose a calculus has natural-number codes for its finite conclusions and satisfies all of the following conditions:

1. An entire proof, including its tree, labels, contexts, indexed families and auxiliary syntax, is a set.
2. Proof trees are well-founded in the premise direction.
3. Axioms, syntax and local rule checks are uniformly $\Delta_1$-definable in set theory, with no arbitrary fixed set parameters. All restrictions on acceptable proofs are included in these checks.

Then its theorem predicate on finite conclusion codes is $\Sigma_1$, with no cardinal bound on proof size or branching.

**Proof.** First suppose the local checks are bounded. Supply a set $T$ coding a proof, an ordinal $\alpha$, and a rank function

$$
r:\mathrm{Nodes}(T)\longrightarrow\alpha
$$

strictly decreasing from each conclusion node to each of its premise nodes. Such a rank exists for every set-sized well-founded relation by well-founded recursion and Replacement. Conversely, rank descent certifies well-foundedness. The condition that $\alpha$ is an ordinal and the function, edge and rank conditions are all bounded once the indicated sets have been supplied.

The local checks quantify only over the supplied nodes, edges, labels and index sets. Well-founded formula codes are treated by an additional syntax rank and the associated finite collection of decoding tables. Thus proof existence has an existential set quantifier block followed by a bounded matrix.

For uniformly $\Delta_1$ checks, use their uniform $\Sigma_1$ presentations. Collection gathers witnesses for the set of local checks into one further set; after that, verification is bounded. Equivalently, a condition $\forall u\in T\,\exists z\,\theta(u,z)$, with bounded $\theta$, is equivalent in ZFC to $\exists B\,\forall u\in T\,\exists z\in B\,\theta(u,z)$. Every positive local check can therefore be included in the same existential certificate. This proves the claim. $\square$

The syntactic AJ rule satisfies these conditions. The full indexed family is included in the node label; checking its premise list ranges over that supplied family. Freshness, substitution and syntactic matching are uniform absolute operations. Supplying the finite H-proof needed for Logical Equivalence is also an existential certificate. Arbitrary set-sized conjunctions, transfinite proof heights, and unbounded branching do not change the conclusion.

The proof in fact needs only a **uniform $\Sigma_1$ checker** for all the positive admissibility conditions. Separate low-complexity descriptions of each individual rule do not suffice if recognizing the permitted rules has greater complexity. Arbitrary sets supplied existentially within certificates are permitted; a fixed external set parameter containing semantic answers is not.

By contrast, the condition “this supplied set contains **every external subset** of $X$” is not a bounded check on the supplied data. It has a universal quantifier over candidate sets outside those data. An exhaustion condition of this kind cannot be smuggled into the hypotheses of Theorem 3.1 as an ordinary syntax check.

## 4 Incompleteness in the fixed ambient universe

The preceding note proves computable many-one equivalence between pure full Gallin validity, with both bases infinite, and full second-order validity. Väänänen's [Proposition 8, p. 112, in *Second order logic or set theory?* (2012)](https://www.mv.helsinki.fi/home/jvaanane/second_order_logic_or_set_theory.pdf#page=22) supplies the effective reduction establishing $\Pi_2$-completeness of full second-order validity. Its proof gives the formula-to-sentence transformation and the truth equivalence in $V$, so the use here concerns actual parameter-free number predicates in the specified universe. The same classification is summarized in [Theorem 4(1), §8, printed p. 18, of *Second order logic and set theory*](https://www.mv.helsinki.fi/home/jvaanane/Vaananen_Compass.pdf).

**Theorem 4.1.** A calculus satisfying Theorem 3.1 cannot be both sound and weakly complete for pure full Gallin validity in the fixed ambient universe $V$.

**Proof.** Let $U(e,n)$ be a universal parameter-free $\Sigma_1$ predicate of set theory on natural-number codes: every parameter-free $\Sigma_1$ number predicate is defined by $U(e,\cdot)$ for some finite formula code $e$. Uniform satisfaction for bounded formulas, followed by existential witness quantification, supplies this universal predicate. Put

$$
B(n):=\neg U(n,n).
$$

Then $B$ is $\Pi_1$, hence $\Pi_2$, but not $\Sigma_1$ in this same $V$. If code $e$ defined it as a $\Sigma_1$ predicate, evaluating at $e$ would give $B(e)\leftrightarrow\neg B(e)$.

By the cited $\Pi_2$-completeness result and the earlier computable reduction to Gallin validity, there is a computable function $f$ such that

$$
B(n)\quad\longleftrightarrow\quad
\mathrm{FullVal}_\infty(f(n)).
$$

If $D$ were the sound and complete theorem predicate of the proposed calculus, then

$$
B(n)\quad\longleftrightarrow\quad D(f(n)).
$$

Theorem 3.1 makes $D$ a $\Sigma_1$ predicate. Composition with a total computable function preserves that class, contradicting the diagonal argument. $\square$

This rules out equality in the specified $V$; it is stronger than a statement that ZFC cannot prove uniform completeness. The parameter restriction matters: allowing the validity set itself as a fixed set parameter would trivialize theoremhood. No claim excluding arbitrary semantic or set-theoretic parameters is made.

When working internally to an inner model $M$, the same argument compares its proof predicate with **its own internally full validity**. It does not identify internally full domains with all powersets and functions of the surrounding universe.

**Corollary 4.2.** Given an explicit parameter-free $\Sigma_1$ formula $D(x)$ for theoremhood, one can effectively produce a finite C sentence code $A$ such that

$$
\mathrm{FullVal}_\infty(A)\quad\longleftrightarrow\quad\neg D(A).
$$

If the calculus is sound, this sentence is valid and underivable.

**Proof.** Fix the universal $U$ and reduction $f$ from Theorem 4.1. Effectively compile an index $e$ for the $\Sigma_1$ predicate $n\mapsto D(f(n))$, so $U(e,n)\leftrightarrow D(f(n))$. Set $A=f(e)$. Then

$$
\mathrm{FullVal}_\infty(f(e))
\leftrightarrow\neg U(e,e)
\leftrightarrow\neg D(f(e)).
$$

Soundness makes $D(A)$ imply validity, and hence $\neg D(A)$, a contradiction. Thus $\neg D(A)$, and the displayed equivalence gives validity. No recursion theorem is needed. $\square$

Effectiveness here means a procedure on the supplied defining formula's code. It does not decide soundness, recover a definition from an opaque predicate, or promise a short or illuminating expanded C sentence. The translation procedure is specified mathematically; no executable implementation or numeral for a particular missing sentence is claimed.

## 6 Sources and status

- **Original proofs and adaptations:** §§1–5 of this note, 23 October 2026, `misc`, unpaginated. Agent review is not human verification and is not a database certificate.
- **Exact framework, computable reductions, finite-cardinality calculations and fullness theorem:** [Full standard Gallin axiomatization note](full-gallin.md), §§1–3 and 6, 23 October 2026, `misc`, unpaginated.
- **Published complexity input:** Jouko Väänänen, *Second order logic or set theory?*, *Bulletin of Symbolic Logic* 18(1), 2012, pp. 91–121, Proposition 8 and its proof, p. 112, [author's PDF](https://www.mv.helsinki.fi/home/jvaanane/second_order_logic_or_set_theory.pdf#page=22). See also *Second order logic and set theory*, §8, Theorem 4(1), printed p. 18, [author's PDF](https://www.mv.helsinki.fi/home/jvaanane/Vaananen_Compass.pdf). The set-proof coding lemma, diagonal application and AJ rule above are not attributed to those sources.

No complete calculus is claimed. No database record or Lean status is promoted by this mathematical note.
