# Second-Order Analytic Necessitism in the finite-support permutation model

Construction and verification by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell,
23 October 2026, for the model finite-support-permutations: the one-object ideally full action
model of *Classicism*, Proposition D.5, part 1, whose arrows are the permutations of $\mathbb N$,
with the ideal of finite sets, and its generated variants (one individual; Σ true atom). It shows
that Second-Order Analytic Necessitism, and so Analytic Necessitism, hold there, although Rigid
Comprehension fails: a rigid real number structure need not be made of rigid properties of
numbers. Revised by Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell, 26 November 2026, for
real number structures as numbers and reals with a membership relation: the structure is the $Y^A$
with the sets $A$ for their members, where it was the real numbers carried onto them by a bijection.

## Setting

Write $G$ for the arrows, the permutations of $\mathbb N$. An entity of a relational type at the
one object is an intension $Y$, assigning to each arrow $j$ a set $Y_j$ of tuples of entities of
its argument types; $Y$ holds of a tuple $\bar a$ at the arrow $k$ iff $k\cdot\bar a\in Y_k$, and
transport along $k$ is $(k\cdot Y)_j:=Y_{j\circ k}$. The intension $Y$ is *pinned down by* a
finite $N\subseteq\mathbb N$ when $Y_j=Y_{j'}$ whenever $j$ and $j'$ agree on $N$, and the
domain of each relational type consists of the intensions pinned down by some finite set
(finitely-pinned-domains). The individuals are $\mathbb N$, acted on by the arrows, or in the
variant a single individual fixed by every arrow; in either case $k\cdot$ is a bijection of every
domain, with inverse $k^{-1}\cdot$, since $k^{-1}\cdot(k\cdot Y)=Y$.

Rigidity is as in the Background: $\operatorname{Rigid}(X)$ is
$\Box\forall x\,.\,(Xx\to\Box Xx)\land(\neg Xx\to\Box\neg Xx)$, which at the evaluation point
says that for all arrows $k,j$ and all $x$, $k\cdot x\in X_k$ iff $(j\circ k)\cdot x\in
X_{j\circ k}$.

**Lemma 1.** An intension $X$ is rigid iff $X_j=j\cdot X_1$ for every arrow $j$, where
$j\cdot X_1=\{j\cdot x:x\in X_1\}$; a rigid $X$ then has necessarily distinct instances, and at
every arrow $k$ it holds of exactly the members of $X_1$.

*Proof.* If $X$ is rigid, the clause at $k=1$ gives $x\in X_1$ iff $j\cdot x\in X_j$, so
$X_j\supseteq j\cdot X_1$, and for $z\in X_j$, $z=j\cdot(j^{-1}\cdot z)$ with $j^{-1}\cdot z\in
X_1$, so $X_j\subseteq j\cdot X_1$. Conversely if $X_j=j\cdot X_1$ for all $j$, then $k\cdot
x\in X_k$ iff $x\in X_1$ iff $(j\circ k)\cdot x\in X_{j\circ k}$, transport being injective.
Necessary distinctness is the injectivity of transport, and at $k$, $X$ holds of $x$ iff $k\cdot
x\in k\cdot X_1$ iff $x\in X_1$. $\blacksquare$

The same holds for relations, with tuples in place of $x$.

## The structure

Fix a relational type $\sigma=\bar\tau t$ and a tuple $\bar u$ of entities of types $\bar\tau$.
For $A\subseteq\mathbb N$ let $Y^A$ be the intension of type $\sigma$ with $Y^A_j:=\{\bar u\}$ if
$j0\in A$ and $Y^A_j:=\emptyset$ otherwise. It is pinned down by $\{0\}$, so in the domain, the
$Y^A$ are pairwise distinct, and $(k\cdot Y^A)_j=Y^A_{j\circ k}$ is $\{\bar u\}$ iff $j(k0)\in A$,
so $k\cdot Y^A$ is pinned down by $\{k0\}$, its value at $j$ depending only on $j(k0)$.
Let $P:=\{Y^A:A\subseteq\mathbb N\}$, and write $\hat n$ for $Y^{\{n\}}$.

Define the intensions
$$X_j:=j\cdot P,\qquad
N_j:=\{j\cdot\hat n:n\in\mathbb N\},\qquad
S_j:=\{(j\cdot\hat m,j\cdot\hat n):n=m+1\},\qquad
E_j:=\{(j\cdot\hat n,j\cdot Y^A):n\in A\},$$
and the entity $0:=\hat 0$ of $P$.

**Lemma 2.** These intensions are in the domain, pinned down by $\{0\}$.

*Proof.* $j\cdot Y^A$ depends on $j$ only through $j0$, so each of $X_j$, $N_j$, $S_j$ and $E_j$
depends only on $j0$. $\blacksquare$

**Lemma 3.** $\mathfrak R:=(N,0,S,X,E)$ is a rigid real number structure, necessarily
a real number structure: $\operatorname{RigidStr}(\mathfrak R)\land\Box\operatorname{Real}_\sigma
(\mathfrak R)$ holds at the evaluation point.

*Proof.* By construction $X_j=j\cdot X_1$ and likewise for $N$, $S$ and $E$, so by Lemma 1 all are
rigid with necessarily distinct instances, and at every arrow $k$ the reals are the members of
$P$ and the numbers the $\hat n$, while $S$ holds at $k$ of $\hat m$ and $\hat n$ iff $n=m+1$, and
$E$ of $\hat n$ and $Y^A$ iff $n\in A$. So at every arrow the structure is a copy of the natural
numbers with their sets: the numbers $\hat n$ satisfy the conditions on zero and successor, and
there is one real $Y^A$ for each set $A$, whose members are the $\hat n$ with $n\in A$, so that
reals with the same members are identical. Fullness at $k$: a property $Y$ has among the numbers
the instances $\hat n$ with $k\cdot\hat n\in Y_k$, and these are the members of $Y^A$ for
$A:=\{n:k\cdot\hat n\in Y_k\}$. And $N$ is the least property containing $0$ and closed under $S$
at $k$: a property that holds there of $\hat 0$, and of $\hat n$'s successor whenever it holds of
$\hat n$, holds of every $\hat n$, by induction on $n$. $\blacksquare$

## Represented powers

For $m\ge1$ and $T\subseteq P^m$ let $\rho(T)$ be the relation of type $\sigma^m t$ with
$\rho(T)_j:=j\cdot T=\{(j\cdot x_1,\ldots,j\cdot x_m):\bar x\in T\}$. It is pinned down by
$\{0\}$ (Lemma 2), rigid by Lemma 1 with $\rho(T)_j=j\cdot\rho(T)_1$, holds at every arrow of
exactly the tuples in $T$, which are tuples of reals, the numbers being among them, and $k\cdot\rho(T)=\rho(k\cdot
T)$, since $(k\cdot\rho(T))_j=(j\circ k)\cdot T=j\cdot(k\cdot T)$.

Let $\mathcal P^0:=\{\rho(T):T\subseteq P^m\}$ and define $\mathcal P_m$ of type $(\sigma^m t)t$
by $(\mathcal P_m)_k:=k\cdot\mathcal P^0$. Then $(\mathcal P_m)_k=\{\rho(T'):T'\subseteq(k\cdot
P)^m\}$ depends on $k$ only through $k0$, so $\mathcal P_m$ is in the domain; it is rigid by
Lemma 1, and at every arrow it holds of exactly the members of $\mathcal P^0$, rigid relations
holding only of tuples of numbers and reals. Representation: at an arrow $k$ and for any relation
$R$ of type $\sigma^m t$, let $T:=\{\bar x\in P^m:k\cdot\bar x\in R_k\}$. Then $\rho(T)\in\mathcal
P^0$, so $\mathcal P_m$ holds of it at $k$, and for $\bar x\in P^m$, $\rho(T)$ holds of $\bar x$
at $k$ iff $\bar x\in T$ iff $R$ holds of $\bar x$ at $k$. So
$\operatorname{RepPower}_m(\mathcal P_m,\mathfrak R)$ holds for every $m$, and with Lemma 3 the consequent
of Second-Order Analytic Necessitism holds at $\sigma$ for every $n$.

## Type $e$

At type $e$ the antecedent fails: a real number structure of individuals would need continuum
many individuals at some world, and the individuals are the natural numbers, or one, at the only
object. So every instance of Second-Order Analytic Necessitism holds, and with it Analytic
Necessitism. The interpretation of Σ plays no part.

## Remark

The construction uses only that the arrows form a group acting on the pinning points and that
every finitely pinned intension is present; it does not use the full strength of the
permutation group. The other finite-support models were once recorded as failing Analytic
Necessitism, because some arrow identifies two points and no entity of type $tt$ is determined by
its transport along it. That argument was withdrawn on 29 October 2026. The numbers and reals of a
rigid structure only need to be transported injectively, and the constant intensions, fixed by every arrow, give one in each
of them (the general argument analytic-necessitism-codomain-fixed). So Analytic Necessitism holds
there as well.

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, Proposition D.5(1), pp. 74–75; construction pp. 75–76; p. 79 (No Pure Contingency)
