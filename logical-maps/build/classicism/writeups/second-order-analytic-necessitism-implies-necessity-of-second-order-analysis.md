# Second-Order Analytic Necessitism implies the Necessity of Second-Order Analysis

Composed by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October 2026, extending the write-up of
analytic-necessitism-implies-necessity-of-analysis, after Theorem 7 of Neil Barton and Zachary Goodsell,
*Continuum Contingency* (draft of 14 October 2026), with Proposition C.3 and Lemma C.3 of Andrew Bacon,
*Could the truths of mathematics have been different?* (draft of 9 October 2025). Revised by Claude
Fable 5.2 (Anthropic), prompted by Zachary Goodsell, 26 November 2026, for real number structures as
numbers and reals with a membership relation. Informal, not Lean-verified.

**Setting.** Work in C at a type $\sigma$. Fix a second-order analytical sentence $A$ and let $n$ be
the largest arity of a relation variable in it. If no real number structure at $\sigma$ is possible,
the instance holds vacuously. Otherwise the instance of Second-Order Analytic Necessitism for $n$
supplies a rigid real number structure $\mathfrak R=(N,0,S,X,E)$ with necessarily distinct numbers and
reals, $\Box\operatorname{Real}_\sigma(\mathfrak R)$, and for each $k\le n$ a represented power
$\mathcal P_k$: a rigid property of rigid $k$-ary relations holding only of tuples of numbers and reals
of $\mathfrak R$, such that necessarily every $k$-ary relation agrees on such tuples with an instance
of $\mathcal P_k$. Write $D$ for the property of being a number or a real of $\mathfrak R$.

**Lemma 1′ (atomic facts).** Lemma 1 of the first-order write-up applies to an instance $Q$ of some
$\mathcal P_k$: $Q\bar u\to\Box Q\bar u$ and $\neg Q\bar u\to\Box\neg Q\bar u$ for $\bar u$ from $D$.
$Q$ is rigid and holds only of tuples of instances of $D$, which are necessarily distinct.

**Lemma 2′ (formulas with parameters).** For every second-order analytical formula
$\varphi(\bar v,\bar V)$, all numbers and reals $\bar u$ of $\mathfrak R$ for $\bar v$ and every tuple
$\bar Q$ of instances of the $\mathcal P_k$ of the arities of $\bar V$: $\varphi(\bar u,\bar Q)\to
\Box\varphi(\bar u,\bar Q)$ and $\neg\varphi(\bar u,\bar Q)\to\Box\neg\varphi(\bar u,\bar Q)$.

*Proof.* Induction on $\varphi$. The atomic, connective and first-order quantifier cases are those of
the first-order write-up, with Lemma 1′ for the atomic formulas $V\bar u$. For a relation quantifier
$\forall R\,\psi(R,\bar u,\bar Q)$ of arity $k$, first note that necessarily
$\forall R\,\psi(R,\bar u,\bar Q)\leftrightarrow\forall R(\mathcal P_kR\to\psi(R,\bar u,\bar Q))$. The
left-to-right direction is trivial. For the converse, at any world, a relation $R$ agrees on tuples of
instances of $D$ with some instance $Q$ of $\mathcal P_k$, by the representation clause, and
$\psi(Q,\bar u,\bar Q)\to\psi(R,\bar u,\bar Q)$ because an analytical formula applies its relation
variables only to terms denoting numbers and reals of the structure (its first-order variables are
restricted to $N$ and $X$, and $0$ is a number), so it cannot distinguish relations agreeing on such
tuples: this is Bacon's Proposition C.3, Analytic Extensionality, a theorem schema of the non-modal
fragment, whose necessitation holds. It therefore suffices to show that
$\forall R(\mathcal P_kR\to\psi(R,\bar u,\bar Q))$ is necessary if true and impossible if false, and this
is the first-order quantifier case with $\mathcal P_k$ as restrictor: if it holds, each instance $Q$ of
$\mathcal P_k$ has $\psi(Q,\bar u,\bar Q)$, hence $\Box\psi(Q,\bar u,\bar Q)$ by the induction hypothesis
(the parameters $Q,\bar Q$ being instances of the $\mathcal P$'s), and inextensibility of $\mathcal P_k$
at $\lambda R\, .\,\psi(R,\bar u,\bar Q)$ gives $\Box\forall R(\mathcal P_kR\to\psi(R,\bar u,\bar Q))$;
if it fails, some instance $Q$ has $\neg\psi(Q,\bar u,\bar Q)$, so $\Box\neg\psi(Q,\bar u,\bar Q)$ by the
induction hypothesis and $\Box\mathcal P_kQ$ by persistence, whence the negation is necessary by K.
$\square$

**Lemma 3′ (categoricity).** $\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to
(A(\mathfrak R')\leftrightarrow A(\mathfrak R)))$: any two real number structures are isomorphic, and
second-order analytical sentences are invariant under isomorphism, since an isomorphism transports
relations by λ-abstraction (Background, the lemma that real number structures are isomorphic; Bacon's
Lemma C.3 for complete ordered fields). Both are theorems of the non-modal fragment, necessitated.

**Proof of the implication.** As in the first-order case: Lemma 2′ at $A$ gives $\Box A(\mathfrak R)$
or $\Box\neg A(\mathfrak R)$, and Lemma 3′ turns either into the corresponding disjunct of the
instance. $\square$

**Remarks.** The represented powers enter only through the relation quantifiers, where the
representation clause makes the restricted and unrestricted quantifiers necessarily equivalent and
the rigidity of $\mathcal P_k$ makes the restricted one non-contingent. Under Rigid Comprehension the
rigid relations holding only of tuples of numbers and reals represent every relation, and Barton and
Goodsell's Second-Order Continuum Necessitism, that the property of rigid properties of reals is rigid,
is the arity-one represented power of the reals; relations of higher arity reduce to properties there by
pairing. The continuum hypothesis is a second-order analytical sentence, so the Non-contingency of the
Continuum Hypothesis follows (necessity-of-second-order-analysis-implies-non-contingency-of-ch).

## Paper references

- **Proof: Continuum Contingency.** Barton, Neil, and Zachary Goodsell. Continuum Contingency. Draft dated 14 October 2026, 47 pages. Stitches a ground model of set theory to the canonical model of a forcing extension to show that Classicism with □Rigid Comprehension, □Relational Choice and an axiom of infinity is consistent with first- and second-order continuum contingency, together with □Atomicity at type t (Theorem 21) or with Recombination (Theorem 22, which refutes Atomicity at type t, Corollary 23); formalizes the coin-toss argument (Theorem 9). Read directly on 19 October 2026; locators refer to this draft. — §5.9, Theorem 7
- **Proof: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — Appendix C.2, Proposition C.3 and Lemma C.3. Analytical formulas do not distinguish relations that agree on the structure's elements, which lets the represented powers stand in for all relations; and categoricity across structures.
