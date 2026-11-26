# C5 and □Rigid Comprehension imply Second-Order Analytic Necessitism

The connection from □Plenitude is Zachary Goodsell's (23 October 2026); the proof is by Claude Fable 5.1
(Anthropic), prompted by Zachary Goodsell, after the S5 part of Corollary 5.1 of Andrew Bacon, *Could
the truths of mathematics have been different?* (draft of 9 October 2025). Revised by Claude Fable 5.2
(Anthropic), prompted by Zachary Goodsell, 26 November 2026, for real number structures as numbers and
reals with a membership relation: fullness and the leastness of the numbers take the place of
completeness. Informal, not Lean-verified.

**Setting.** C5 is C with □ND at every relational type. On the map it gives B and 5, ND at every type
(Prior), and BF at every type (necessary-nd-implies-bf); the write-up of c5-implies-necessity-of-arithmetic
lists the Lean proofs. Assume also □Rigid Comprehension: at every world, every relation is coextensive
with a rigid one. Fix a type $\sigma$ and $n\ge1$, and suppose
$\Diamond\exists\mathfrak R\operatorname{Real}_\sigma\mathfrak R$: at some world $w$ there is a real number
structure $\mathfrak R=(N,0,S,X,E)$. Everything below uses the Background's definitions of
$\operatorname{Rigid}$ (persistent and inextensible, each with its leading box) and of real number
structures.

**Lemma 1 (rigidity travels).** If $Y$ is rigid at $w$, it is rigid at the actual world. Rigidity is
$\Box\operatorname{WeaklyRigid}(Y)$, so at the actual world $\Diamond\Box\operatorname{WeaklyRigid}(Y)$,
and $\Diamond\Box p\to\Box p$ holds under 5 (and $\Diamond\Box p\to p$ under B). The same transfers any
necessary fact between $w$ and the actual world, in either direction.

**Lemma 2 (first-order facts).** For rigid relations with necessarily distinct instances, every
first-order fact with parameters from the instances is necessary if true and impossible if false: this
is Lemmas 1 and 3 of the write-up of analytic-necessitism-implies-necessity-of-analysis, which use only
persistence, inextensibility, the necessity of identity and necessary distinctness. ND gives the
necessary distinctness of all instances at every type. A quantifier not restricted to one of these
relations is covered as well: the universal property of a type is rigid, by BF.

**The rigidified structure.** At $w$, Rigid Comprehension gives rigid $Y_N$, $Y_S$, $Y_X$, $Y_E$
coextensive there with $N$, $S$, $X$, $E$. Write $\mathfrak Y=(Y_N,0,Y_S,Y_X,Y_E)$. By Lemma 1 its
relations are rigid at the actual world, and by ND its numbers and reals are necessarily distinct; so
$\operatorname{RigidStr}(\mathfrak Y)$. At $w$ every instance of $Y_S$ is a pair of instances of $Y_N$,
which are necessarily instances of it, so by the inextensibility of $Y_S$ it necessarily holds only of
instances of $Y_N$; likewise $Y_E$ necessarily holds only of an instance of $Y_N$ and an instance of
$Y_X$.

**$\mathfrak Y$ is necessarily a real number structure.** The clauses on zero and successor other than
leastness, and extensionality, are first-order facts about $\mathfrak Y$; they hold at $w$, where
$\mathfrak Y$ agrees with $\mathfrak R$, so by Lemma 2 they are necessary. Leastness of $Y_N$ and
fullness quantify over properties, and are handled at an arbitrary world $u$ (accessible from the
actual world, hence, under 5, from $w$ and seeing $w$). Let $F$ be a property at $u$, and let $F'$ be a
rigid property coextensive at $u$ with $\lambda v\, .\,Y_Nv\land Fv$ (Rigid Comprehension at $u$). "Some
instance of $Y_X$ has just the instances of $F'$ for its members" is a first-order fact about rigid
relations; it is true at $w$, by the fullness of $\mathfrak R$ there, hence true at $u$ by Lemma 2 and
Lemma 1. So at $u$ some real has as its members just the numbers $F$ holds of. Leastness of $Y_N$ is the
same argument: if $F$ holds of $0$ and is closed under $Y_S$ at $u$, then so is $F'$, which is a
first-order fact about rigid relations and so holds at $w$; there $Y_N$ is least, so every instance of
$Y_N$ is one of $F'$, a first-order fact again, which therefore holds at $u$. Hence
$\Box\operatorname{Real}_\sigma(\mathfrak Y)$.

**Represented powers.** For $k\le n$ let $\mathcal P_k$ be the property of rigid $k$-ary relations
holding only of tuples of numbers and reals of $\mathfrak Y$, that is, of instances of
$D:=\lambda v\, .\,Y_Nv\lor Y_Xv$. Its instances are rigid by definition. It is persistent, since both
conjuncts are necessary if true (rigidity carries a box, and $Q$ holding only of tuples of instances of
$D$ is a first-order fact about rigid $Q$, $Y_N$ and $Y_X$). It is inextensible: given $G$ with
$\forall Q(\mathcal P_kQ\to\Box GQ)$ at a world $u$, for every $Q$ at $u$ either $\mathcal P_kQ$, so
$\Box GQ$, or $\neg\mathcal P_kQ$, and then $\Box\neg\mathcal P_kQ$, rigidity being non-contingent under
5 by Lemma 1 and the other conjunct by Lemma 2; so $\forall Q\,\Box(\mathcal P_kQ\to GQ)$, and BF at the
type of $Q$ gives $\Box\forall Q(\mathcal P_kQ\to GQ)$, which is $\mathcal P_k\le G$. And necessarily every
$k$-ary relation $R$ agrees on the numbers and reals with an instance: at any world, Rigid
Comprehension gives a rigid relation coextensive with $\lambda\bar v\, .\,R\bar v\land\bigwedge_iDv_i$,
which lies in $\mathcal P_k$. So the instance of Second-Order Analytic Necessitism at $\sigma$ and $n$
holds. $\square$

**Remarks.** Atomicity is not used. Bacon's Corollary 5.1 derives the sentence-level Necessity of
Second-Order Analysis from the same premises through Theorem 5.2, whose proof uses the Leibniz
Biconditionals to show that a rigid real number structure, for him a complete ordered field, stays
complete at every accessible world; under S5 the world $w$ of the given structure stays accessible, and
fullness, which does the work of completeness here, is read off there. The rigid coextensions exist by
□Rigid Comprehension, and 5 and BF do the rest, so □Plenitude, which gives C5 and □Rigid Comprehension
on the map, gives the conclusion.
