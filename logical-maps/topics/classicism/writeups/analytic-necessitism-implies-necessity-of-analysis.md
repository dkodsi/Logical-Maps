# Analytic Necessitism implies the Necessity of Analysis

Composed by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October 2026, after Theorem 7 of Neil Barton and Zachary
Goodsell, *Continuum Contingency* (draft of 14 October 2026), and Lemmas C.1 and C.3 of Andrew Bacon,
*Could the truths of mathematics have been different?* (draft of 9 October 2025). Revised by Claude
Fable 5.2 (Anthropic), prompted by Zachary Goodsell, 26 November 2026, for real number structures as
numbers and reals with a membership relation: Lemmas 1 and 3 are stated for any rigid relations, and
Lemma 2, on sum and product, is new. Informal, not Lean-verified.

**Setting.** Work in C at a type $\sigma$, with the definitions of the Background's paragraph on
analysis. Fix an instance of the Necessity of Analysis: a first-order analytical sentence $A$, and the
disjunction
$\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to A(\mathfrak R'))\lor
\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to\neg A(\mathfrak R'))$,
to which the instance is equivalent, the antecedent of each of its disjuncts being redundant.
If $\neg\Diamond\exists\mathfrak R'\operatorname{Real}_\sigma\mathfrak R'$, both disjuncts hold
vacuously. Otherwise Analytic Necessitism supplies $\mathfrak R=(N,0,S,X,E)$ with $N$, $S$, $X$ and
$E$ rigid, its numbers and reals necessarily distinct, and
$\Box\operatorname{Real}_\sigma(\mathfrak R)$. Recall that $\operatorname{Rigid}(Y)$ is
$\operatorname{Persistent}(Y)\land\operatorname{Inextensible}(Y)$, where
$\operatorname{Persistent}(Y)$ is $\Box\forall\bar y(Y\bar y\to\Box Y\bar y)$ and
$\operatorname{Inextensible}(Y)$ is $\Box\forall Z((\forall\bar y\, .\,Y\bar y\to\Box Z\bar y)\to
Y\le Z)$, with $Y\le Z$ the necessary pointwise implication. Both are used at the actual world by T.

**Lemma 1 (atomic facts of a rigid relation).** Let $D$ be a property whose instances are necessarily
distinct, $\forall u\,v(Du\land Dv\land u\ne v\to\Box\,u\ne v)$, and let $Q$ be a rigid relation that
holds only of tuples of instances of $D$. Then for every tuple $\bar u$ of instances of $D$ of the
right length, $Q\bar u\to\Box Q\bar u$ and $\neg Q\bar u\to\Box\neg Q\bar u$. Likewise
$u=v\to\Box u=v$ and $u\ne v\to\Box u\ne v$ for instances $u,v$ of $D$.

*Proof.* The first claim is persistence of $Q$. For the second, suppose $\neg Q\bar u$, and let
$Z:=\lambda\bar y\, .\,\bar y\ne\bar u$, where $\bar y\ne\bar u$ is the disjunction of the coordinatewise
distinctnesses. Every $\bar y$ with $Q\bar y$ is a tuple of instances of $D$ differing from $\bar u$ in
some coordinate, so $\Box(\bar y\ne\bar u)$ by the necessary distinctness of the instances of $D$. Hence
$\forall\bar y(Q\bar y\to\Box Z\bar y)$, and inextensibility of $Q$ gives $Q\le Z$, that is
$\Box\forall\bar y(Q\bar y\to\bar y\ne\bar u)$, which is $\Box\neg Q\bar u$. For identity, the first
claim is the necessity of identity, a theorem of C, and the second is necessary distinctness. $\square$

With the numbers and reals of $\mathfrak R$ for the instances of $D$, the lemma covers the atomic
formulas $Smn$, $Enx$, $m=n$ and $x=y$ at numbers and reals of $\mathfrak R$. The term $0$ denotes a
fixed number.

**Lemma 2 (sum and product).** For numbers $m,n,k$ of $\mathfrak R$, each of
$\operatorname{Sum}(m,n,k)$ and $\operatorname{Prod}(m,n,k)$ is necessary if true and impossible if
false.

*Proof.* By its definition $\operatorname{Sum}$ holds of $m,0,m$, and of $m,n',k'$ whenever it holds of
$m,n,k$ and $n'$, $k'$ are the successors of $n$, $k$; these are theorems of C for any $0$ and $S$. In
a real number structure it is moreover the graph of a function on the numbers, by the recursion theorem,
a theorem of the non-modal fragment; so necessarily it is one in $\mathfrak R$. Fix $m$, and let $W$
hold of the numbers $n$ for which some number $k$ has $\Box\operatorname{Sum}(m,n,k)$. $W$ holds of $0$, with
$k:=m$. If it holds of $n$ with $k$, and $n'$, $k'$ are the successors of $n$, $k$, then $\Box Snn'$
and $\Box Skk'$ by the persistence of $S$, so $\Box\operatorname{Sum}(m,n',k')$, and $W$ holds of $n'$.
$N$ being least, $W$ holds of every number. So a true $\operatorname{Sum}(m,n,k)$ is necessary: the
$k_0$ with $\Box\operatorname{Sum}(m,n,k_0)$ is $k$, the sum being a function. And a false one is
impossible: $k_0\ne k$, so $\Box\,k_0\ne k$, and necessarily at most one number is the sum. The product
is the same, with the sum in place of the successor of $k$. $\square$

**Lemma 3 (formulas with parameters).** Let $D_1,\ldots,D_r$ be rigid properties, and consider the
formulas built by $\neg$, $\land$, $\lor$ and quantifiers $\forall v\in D_i$ from atomic formulas that
are necessary if true and impossible if false at all instances of the $D_i$ for their variables. Every
such formula $\varphi(\bar v)$ is necessary if true and impossible if false at instances $\bar u$ of
the $D_i$: $\varphi(\bar u)\to\Box\varphi(\bar u)$ and $\neg\varphi(\bar u)\to\Box\neg\varphi(\bar u)$.

*Proof.* By induction on $\varphi$. Negation, conjunction and disjunction: if $\varphi$ and $\psi$ are
each necessary if true and impossible if false, so are $\neg\varphi$, $\varphi\land\psi$ and
$\varphi\lor\psi$, by K; these are the steps nc_neg, nc_conj and nc_disj of the Lean proof of
c5-implies-necessity-of-arithmetic, derived in C. Universal quantifier
$\forall v\in D_i\, .\,\psi(v,\bar u)$: if it holds, then by the induction hypothesis
$\forall v(D_iv\to\Box\psi(v,\bar u))$, and inextensibility of $D_i$ at
$Z:=\lambda v\, .\,\psi(v,\bar u)$ gives $D_i\le Z$, that is $\Box\forall v(D_iv\to\psi(v,\bar u))$. If
it fails, some $v$ with $D_iv$ has $\neg\psi(v,\bar u)$; the induction hypothesis gives
$\Box\neg\psi(v,\bar u)$ and persistence of $D_i$ gives $\Box D_iv$, so
$\Box\exists v(D_iv\land\neg\psi(v,\bar u))$ by K, which is
$\Box\neg\forall v\in D_i\, .\,\psi(v,\bar u)$. $\square$

With $N$ and $X$ for the $D_i$, and Lemmas 1 and 2 for the atomic formulas, every first-order
analytical formula is necessary if true and impossible if false at numbers and reals of $\mathfrak R$.
Lemmas 1 and 3 apply in the same way to a rigid complete ordered field with its natural numbers, whose
atomic formulas are those of its rigid relations; that is the case the Background's lemma on real
number structures and complete ordered fields uses.

**Lemma 4 (categoricity).** $\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to
(A(\mathfrak R')\leftrightarrow A(\mathfrak R)))$.

*Proof.* Any two real number structures at $\sigma$ are isomorphic, and isomorphic structures agree on
every analytical sentence; both are theorems of the non-modal fragment of C (Background, the lemma
that real number structures are isomorphic; Bacon's Lemma C.3 for complete ordered fields, after
Huntington), so their necessitations hold. Combine with $\Box\operatorname{Real}_\sigma(\mathfrak R)$
by K. $\square$

**Proof of the implication.** By Lemma 3 at the sentence $A$, either $\Box A(\mathfrak R)$ or
$\Box\neg A(\mathfrak R)$. In the first case Lemma 4 and K give
$\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to A(\mathfrak R'))$; in the second,
the disjunct with $\neg A$. $\square$

**Remarks.** The argument uses K, T and 4 only, the last two through the boxes that persistence and
inextensibility carry; neither B, BF, Rigid Comprehension nor any choice principle. The rigidity of
successor and membership is needed and not only that of the numbers and the reals: Lemma 1 for $S$ and
$E$ is where it enters, and rigid numbers and reals alone could be differently related at another
world. Barton and Goodsell's Theorem 7 is the case in which the reals are the rigid properties of
natural numbers, under Rigid Comprehension and their axiom of Infinity; the quantifier case is the
same, with their rigid restrictor in place of the given structure's. The second-order case, with the
represented powers, is the write-up of
second-order-analytic-necessitism-implies-necessity-of-second-order-analysis.
