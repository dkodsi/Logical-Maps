# Cardinality, arithmetic and analysis

The Axiom of Infinity is stated with Frege's cardinality apparatus. At a type
$\sigma$, a *cardinality* is an entity of type $(\sigma t)t$, and:

$$
\begin{aligned}
\mathbf{0}_\sigma&:=\lambda X^{\sigma t}\, .\,\forall u^\sigma\, .\,\neg Xu,\\
\operatorname{Suc}_\sigma(Z)&:=\lambda X^{\sigma t}\, .\,\exists y^\sigma\, .\,
  Xy\land Z(\lambda u^\sigma\, .\,Xu\land u\ne y),\\
\operatorname{FiniteCardinality}_\sigma(Z)&:=\forall W^{((\sigma t)t)t}\, .\,
  \bigl(W\mathbf{0}_\sigma\land\forall Y\, .\,WY\to W(\operatorname{Suc}_\sigma Y)\bigr)\to WZ.
\end{aligned}
$$

So $\mathbf{0}_\sigma$ is the cardinality of the empty property,
$\operatorname{Suc}_\sigma$ adds one to a cardinality, and
$\operatorname{FiniteCardinality}_\sigma$ collects the cardinalities reached from
$\mathbf{0}_\sigma$ by finitely many successors, in the impredicative sense
that they fall under every property of cardinalities that holds of
$\mathbf{0}_\sigma$ and of a successor whenever it holds of the cardinality
succeeded. In C, $\mathbf{0}_\sigma$ and the successor of a finite cardinality are
finite cardinalities, and a finite cardinality that holds of a property holds of every
property coextensive with it
{lean: Classicism.finiteCardinality_zero, Classicism.finiteCardinality_suc, Classicism.finiteCardinality_coext}.
Every type used here ends
in $t$, so all of them are admitted, and no type $\sigma\sigma$ is needed;
that is why the axiom is not put in the Dedekind form, which would ask for an
injective non-surjective operation from $\sigma$ to $\sigma$.

Countable Boolean Completeness and the Necessity of Arithmetic follow
Goodsell, *Arithmetic is Necessary*, which leaves the type $\nu$ of numbers,
zero and successor as parameters. The map takes them, at each type $\sigma$,
to be $\nu_\sigma:=(\sigma t)t$, $\mathbf{0}_\sigma$ and
$\operatorname{Suc}_\sigma$, and states both principles as schemata in
$\sigma$; the paper displays the instance $\sigma=e$ in its eqs. (24)–(25)
without assuming it. Natural numberhood $\mathbb N_\sigma$ is then
$\operatorname{FiniteCardinality}_\sigma$. Write
$\forall n\in\mathbb N_\sigma\, .\,A$ for
$\forall n^{\nu_\sigma}\, .\,\mathbb N_\sigma n\to A$, and likewise for
$\exists$. With these, for a type $\sigma$ and a relational type $\tau$:

$$
\begin{aligned}
\operatorname{Ctbl}_{\sigma,\tau}(X)&:=\exists R^{\tau\nu_\sigma t}\, .\,\forall y^\tau z^\tau\, .\,
  Xy\land Xz\to\bigl((\exists n\in\mathbb N_\sigma\, .\,Ryn\land Rzn)\leftrightarrow y=z\bigr),\\
I^*_\sigma&:=\forall m\,n\in\mathbb N_\sigma\, .\,\mathbf{0}_\sigma\ne\operatorname{Suc}_\sigma m\land
  (\operatorname{Suc}_\sigma m=\operatorname{Suc}_\sigma n\to m=n),\qquad I_\sigma:=\Diamond I^*_\sigma,\\
\operatorname{Sum}_\sigma(m,n,o)&:=\forall R^{\nu_\sigma\nu_\sigma t}\, .\,R\mathbf{0}_\sigma m\to
  (\forall i\,j\in\mathbb N_\sigma\, .\,Rij\to R(\operatorname{Suc}_\sigma i)(\operatorname{Suc}_\sigma j))\to Rno,\\
\operatorname{Prod}_\sigma(m,n,o)&:=\forall R^{\nu_\sigma\nu_\sigma t}\, .\,R\mathbf{0}_\sigma\mathbf{0}_\sigma\to
  (\forall i\,j\,k\in\mathbb N_\sigma\, .\,Rij\to\operatorname{Sum}_\sigma(m,j,k)\to R(\operatorname{Suc}_\sigma i)k)\to Rno.
\end{aligned}
$$

So $X$ is countable (relative to $\sigma$) when it injects into the natural
numbers counted at $\sigma$, and $I_\sigma$ says that possibly zero is not a
successor and successor is injective on numbers. In C the first conjunct of
$I^*_\sigma$ is a theorem, since $\mathbf{0}_\sigma$ and a successor differ at
$\lambda x^\sigma\, .\,\bot$, and $I_\sigma$ and $I^*_\sigma$ are equivalent to each
other and to Potential Infinity at $\sigma$ ([[potential-infinity-forms]]). An *arithmetical sentence* at $\sigma$ is a
closed formula built from atomic formulas $\mathbb N_\sigma\mathbf n$,
$\operatorname{Sum}_\sigma(\mathbf m,\mathbf n,\mathbf o)$,
$\operatorname{Prod}_\sigma(\mathbf m,\mathbf n,\mathbf o)$ and $\mathbf m=\mathbf n$,
whose terms are variables of type $\nu_\sigma$, $\mathbf{0}_\sigma$ and
successors of terms, by $\neg$, $\lor$, $\land$ and quantifiers
$\forall v\in\mathbb N_\sigma$. These are Definitions 3–8 of Goodsell's
draft. Where the type is fixed by context the subscript $\sigma$ is dropped.

**Analysis.** A *real number structure* at a type $\sigma$ is a natural-number
structure on entities of type $\sigma$ together with entities of type $\sigma$
that stand for the sets of its numbers, one for each. It is a tuple
$\mathfrak R=(N^{\sigma t},0^\sigma,S^{\sigma\sigma t},X^{\sigma t},E^{\sigma\sigma t})$
such that:

- *numbers.* $0$ is an instance of $N$; $S$ holds only of instances of $N$,
  and each instance of $N$ bears it to exactly one thing; $0$ is no
  successor, and distinct instances of $N$ have distinct successors; and $N$
  is the least property containing $0$ and closed under $S$.
- *membership.* $E$ holds only of an instance of $N$ and an instance of $X$,
  in that order.
- *extensional.* Instances of $X$ with the same members are identical:
  $\forall x\,y\in X\, .\,(\forall n\, .\,Enx\leftrightarrow Eny)\to x=y$.
- *full.* For every property, some instance of $X$ has as its members just
  the numbers the property holds of:
  $\forall Y^{\sigma t}\,\exists x\in X\,\forall n\in N\, .\,Enx\leftrightarrow Yn$.

Write $\operatorname{Real}_\sigma(\mathfrak R)$. The instances of $N$ are the
structure's *numbers* and those of $X$ its *reals*, and $Enx$ says that the
number $n$ is a *member* of the real $x$: a real stands for a set of
numbers, and there is exactly one real for each. Numbers and reals are
entities of the one type $\sigma$, and nothing more is assumed about which
entities they are; a number may also be a real. The structure's *sum* and
*product* are defined from its zero and successor as
$\operatorname{Sum}_\sigma$ and $\operatorname{Prod}_\sigma$ are above:

$$
\begin{aligned}
\operatorname{Sum}_{\mathfrak R}(m,n,k)&:=\forall R^{\sigma\sigma t}\, .\,R0m\to
  (\forall i\,j\,i'\,j'\, .\,Rij\land Sii'\land Sjj'\to Ri'j')\to Rnk,\\
\operatorname{Prod}_{\mathfrak R}(m,n,k)&:=\forall R^{\sigma\sigma t}\, .\,R00\to
  (\forall i\,j\,i'\,j'\, .\,Rij\land Sii'\land\operatorname{Sum}_{\mathfrak R}(m,j,j')\to Ri'j')\to Rnk.
\end{aligned}
$$

Any two real number structures, at one type or at two, are isomorphic, a
theorem of the non-modal fragment ([[real-structures-isomorphic]]). A
*first-order analytical sentence* is a closed formula in the variables of a
real number structure built from the atomic formulas $Smn$,
$\operatorname{Sum}(m,n,k)$, $\operatorname{Prod}(m,n,k)$, $Enx$, $m=n$ and
$x=y$, in which $m,n,k$ are number terms, $0$ or number variables, and $x,y$
are real variables, all of type $\sigma$, by $\neg$, $\lor$, $\land$ and quantifiers
$\forall n\in N$ and $\forall x\in X$: a sentence of second-order
arithmetic. A *second-order analytical sentence* may also use variables $R$
for relations of any finite arity, each place of a variable being for
numbers or for reals, in atomic formulas $R\bar u$ whose terms are of those
kinds, and unrestricted quantifiers $\forall R$. For a sentence $A$,
$A(\mathfrak R)$ is its reading in $\mathfrak R$.

The definition by a membership relation is Zachary Goodsell's (26 November
2026): the reals of a structure are whatever entities stand, extensionally
and fully, for the sets of its numbers. Barton and Goodsell's analytical
sentences (*Continuum Contingency*, §5.7) are read with the rigid properties
of natural numbers for the reals and instantiation for membership
([[rigid-power-of-the-numbers]]). Bacon's second-order analysis (*Could the
truths of mathematics have been different?*, Appendix C.2) presents the same
theory through a complete ordered field with its natural numbers, as the map
did until 26 November 2026. The field is bookkeeping: the two kinds of
structure define each other at each type, and rigidly so, so that each
principle of analysis says of each type what it said of complete ordered
fields ([[real-structures-and-fields]]). Bacon restricts the second-order
quantifiers to rigid properties, which makes no difference under Rigid
Comprehension (his Proposition C.3).

The *continuum hypothesis* $\operatorname{CH}(\mathfrak R)$ is the
second-order analytical sentence
$\forall Y^{\sigma t}\, .\,(\forall x\, .\,Yx\to Xx)\to
(Y\precsim N\lor Y\approx X)$: every collection of reals injects into the
numbers or is in bijection with the reals. Here $Y\precsim Z$ says that some
relation is an injection from the $Y$s into the $Z$s and $Y\approx Z$ that
some relation is a bijection between them. Write $Du$ for $Nu\lor Xu$. A
real number structure is *rigid*, $\operatorname{RigidStr}(\mathfrak R)$,
when $N$, $S$, $X$ and $E$ are rigid and its numbers and reals are
necessarily distinct,
$\forall u\,v\, .\,Du\land Dv\land u\ne v\to\Box\,u\ne v$. A *represented
power* of arity $k$ for $\mathfrak R$,
$\operatorname{RepPower}_k(\mathcal P,\mathfrak R)$, is a rigid property
$\mathcal P$ of rigid $k$-ary relations holding only of numbers and reals of
$\mathfrak R$, such that necessarily every $k$-ary relation agrees on them
with an instance of $\mathcal P$:
$\operatorname{Rigid}(\mathcal P)\land
(\forall Q\, .\,\mathcal PQ\to\operatorname{Rigid}(Q)\land\forall\bar u\, .\,Q\bar u\to\textstyle\bigwedge_iDu_i)\land
\Box\forall R\,\exists Q\, .\,\mathcal PQ\land\forall\bar u\, .\,\textstyle\bigwedge_iDu_i\to(Q\bar u\leftrightarrow R\bar u)$.

The schematic $\sigma$ is what lets the principles say what they intend
whatever the size of a given type. Where $\sigma$ necessarily has only
finitely many members, $\mathbb N_\sigma$ is finite, a property countable
relative to $\sigma$ is finite and so has a least upper bound in C, and
$I_\sigma$ is necessarily false; those instances are trivial.

::: lemma {#necessary-infinity-injective-successor}
title: necessary infinity makes successor injective
credit: Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 30 October 2026
---
At each type $\sigma$, $\Box\operatorname{AxInf}_\sigma\to\Box I^*_\sigma$, where
$\operatorname{AxInf}_\sigma$ is the Axiom of Infinity at $\sigma$: no finite cardinality holds
of $\lambda u^\sigma\, .\,\top$. So the boxed Axiom of Infinity at $\sigma$ is Barton and
Goodsell's Infinity, eq. (22), at $\sigma$, and discharges the antecedent of Arithmetic
Necessitism at $\sigma$.

*Proof.* The first conjunct of $I^*_\sigma$ is a theorem of C. By 4 it is enough to derive
injectivity at a world from $\Box\operatorname{AxInf}_\sigma$ there. Three facts about finite
cardinalities $Z$ are proved by induction along $\operatorname{FiniteCardinality}_\sigma$,
quantifying over the other variables:

1. $Z$ is $\mathbf 0_\sigma$ or $\operatorname{Suc}_\sigma Z'$ for a finite cardinality $Z'$.
2. $Z$ respects exchange: if $Xz$, $\neg Xy$ and $ZX$, then $Z$ holds of $X$ with $z$ replaced
   by $y$.
3. Hence, if $\neg Xy$, then $\operatorname{Suc}_\sigma Z$ holds of $X$ with $y$ added iff $ZX$.
   For the left-to-right direction, a witness $z\ne y$ is exchanged for $y$ by fact 2.

Finite cardinalities are necessarily finite cardinalities, and the three facts are theorems, so
they hold at every world. Now show, by induction on $m$, that $\operatorname{Suc}m=\operatorname{Suc}n$
gives $m=n$ for every finite cardinality $n$, using fact 1 for each of $m$ and $n$.

- *A zero and a successor of a successor.* $\operatorname{Suc}\mathbf 0$ holds of a singleton
  $\lambda x\, .\,x=a$ (Existence), and $\operatorname{Suc}\operatorname{Suc}n'$ does not.
- *Two successors of successors.* Suppose $\operatorname{Suc}\operatorname{Suc}m'=\operatorname{Suc}\operatorname{Suc}n'$.
  At any world and for any $X$:
  - if some $y$ has $\neg Xy$, fact 3 applied twice gives
    $\operatorname{Suc}m'X\leftrightarrow\operatorname{Suc}\operatorname{Suc}m'(X+y)\leftrightarrow
    \operatorname{Suc}\operatorname{Suc}n'(X+y)\leftrightarrow\operatorname{Suc}n'X$;
  - otherwise $X$ is coextensive with $\lambda u\, .\,\top$, and by $\operatorname{AxInf}_\sigma$
    at that world neither $\operatorname{Suc}m'$ nor $\operatorname{Suc}n'$ holds of it.

  So $\operatorname{Suc}m'$ and $\operatorname{Suc}n'$ are necessarily coextensive, hence identical
  by Intensionality, and the induction hypothesis gives $m'=n'$.

The box on the Axiom is used in the last case, at every world. $\square$
:::

**Potential infinity.** *Potential Infinity* at a type $\sigma$ says that every number counted at
$\sigma$ could be the number of some property's instances, so that for each number there could be at
least that many entities of type $\sigma$:

$$
\operatorname{PotInf}_\sigma:=\forall n\in\mathbb N_\sigma\, .\,\Diamond\exists X^{\sigma t}\, .\,nX.
$$

It is equivalent in C to $I^*_\sigma$ and to $I_\sigma$ ([[potential-infinity-forms]]), and its
necessitation is Barton and Goodsell's axiom of Infinity. The Axiom of Infinity at $\sigma$ implies
it, since then every number holds of some property outright. It is weaker: it holds wherever there
could be ever more entities of the type, whether or not any one possibility has infinitely many.

The *at-least numbers* at $\sigma$ are counted from
$\mathbf 0^{\ge}_\sigma:=\lambda X^{\sigma t}\, .\,\top$ by the same successor:
$\operatorname{LowerNat}_\sigma(Z):=\forall W^{((\sigma t)t)t}\, .\,
\bigl(W\mathbf 0^{\ge}_\sigma\land\forall Y\, .\,WY\to W(\operatorname{Suc}_\sigma Y)\bigr)\to WZ$.
Where $\mathbf 0_\sigma$ holds of the properties with no instance,
$\mathbf 0^{\ge}_\sigma$ holds of every property, and the $n$th at-least number holds of the
properties with at least $n$ instances. The at-least numbers are Bacon's: his formalization of the
cardinal continuum hypothesis counts with them, and its infinity premise is the Peano conditions on
them, his lower-Peano conditions, which are a form of Potential Infinity ([[at-least-numbers]]).

::: lemma {#finite-cardinality-arithmetic}
title: exchange, removal, addition and subproperties
lean: [Classicism.finiteCardinality_exchange, Classicism.finiteCardinality_remove, Classicism.finiteCardinality_add, Classicism.finiteCardinality_subset]
credit: Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell, 24 November 2026
---
In C, for a finite cardinality $Z$ at $\sigma$, properties $X,X^\prime$ and entities $a,b,y$ of
type $\sigma$:

1. *Exchange.* If $Xa$, $\neg Xb$ and $ZX$, then $Z$ holds of $X$ with $a$ replaced by $b$,
   $\lambda u\, .\,(Xu\land u\ne a)\lor u=b$.
2. *Removal.* If $\operatorname{Suc}_\sigma Z$ holds of $X$ and $Xy$, then $Z(X-y)$.
3. *Addition.* If $ZX$ and $\neg Xy$, then $\operatorname{Suc}_\sigma Z$ holds of $X$ with $y$ added,
   $\lambda u\, .\,Xu\lor u=y$.
4. *No proper subproperty has the same cardinality.* If $ZX$, $ZX^\prime$ and $X^\prime\subseteq X$,
   then $X\subseteq X^\prime$.

Part 1 is the second fact, and parts 2 and 3 the third, in the proof of
[[necessary-infinity-injective-successor]].

*Proof.* Throughout, a finite cardinality that holds of a property holds of every property
coextensive with it.

1. By induction on $Z$. For $\mathbf 0_\sigma$ there is nothing to show, $X$ having the instance
   $a$. Let $Z=\operatorname{Suc}Y$ with $Y$ finite and satisfying exchange, and let $Xy$ and $Y(X-y)$.
   If $y=a$, then $b$ is an instance of the new property, which less $b$ is coextensive with
   $X-a$, as $\neg Xb$. If $y\ne a$, then $a$ is an instance of $X-y$ and $b$ is not, so $Y$ holds of
   $X-y$ with $a$ replaced by $b$; and that is coextensive with the new property less $y$, since
   $b\ne y$. Either way $\operatorname{Suc}Y$ holds of the new property.
2. Let $Xz$ and $Z(X-z)$. If $z=y$ we are done. Otherwise $y$ is an instance of $X-z$ and $z$ is
   not, and $X-z$ with $y$ replaced by $z$ is coextensive with $X-y$; apply part 1.
3. The witness is $y$: the new property less $y$ is coextensive with $X$.
4. By induction on $Z$. For $\mathbf 0_\sigma$, $X$ has no instance. Let $Z=\operatorname{Suc}Y$, and
   let $X^\prime y$ and $Y(X^\prime-y)$. Then $Xy$, so $Y(X-y)$ by part 2, and
   $X^\prime-y\subseteq X-y$; by the induction hypothesis $X-y\subseteq X^\prime-y$. So an instance
   of $X$ is $y$ or an instance of $X^\prime-y$, and in either case an instance of $X^\prime$. $\square$
:::

::: lemma {#numbers-with-a-common-instance}
title: numbers that could hold of one property are identical
lean: [Classicism.finiteCardinality_eq_of_dia_common]
credit: Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell, 24 November 2026
---
In C, for $m,n\in\mathbb N_\sigma$: if $\Diamond\exists X^{\sigma t}\, .\,mX\land nX$, then $m=n$.

So numbers are identical whenever they could be the number of one and the same property, with no
assumption of infinity; that distinct numbers are necessarily distinct needs $\Box I^*_\sigma$.

*Proof.* By induction on $m$, for every number $n$; a number is $\mathbf 0_\sigma$ or the successor
of a number.

- $m=\mathbf 0$. If $n=\operatorname{Suc}k$, then no property has both cardinalities: the first
  allows it no instance and the second requires one. That is a theorem, so necessary, against the
  hypothesis. So $n=\mathbf 0$.
- $m=\operatorname{Suc}m^\prime$. Likewise $n$ is not $\mathbf 0$; let $n=\operatorname{Suc}k$, with $k$
  a number, necessarily so. Necessarily, if $\operatorname{Suc}m^\prime$ and $\operatorname{Suc}k$ both
  hold of $X$, then, for $y$ with $Xy$ and $m^\prime(X-y)$, also $k(X-y)$, by removal
  ([[finite-cardinality-arithmetic]]). So $\Diamond\exists X\, .\,m^\prime X\land kX$, and the
  induction hypothesis gives $m^\prime=k$, whence $m=n$. $\square$
:::

::: lemma {#potential-infinity-forms}
title: the forms of Potential Infinity
lean: [Classicism.iStar_of_potentialInfinity, Classicism.potentialInfinity_of_iStar, Classicism.potentialInfinity_of_dia, Classicism.potentialInfinity_of_axiomOfInfinity]
credit: Zachary Goodsell (that Potential Infinity is $I^*$, 24 November 2026); proofs by Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell
---
In C, at each type $\sigma$:

1. $\operatorname{PotInf}_\sigma\leftrightarrow I^*_\sigma$.
2. $\Diamond\operatorname{PotInf}_\sigma\to\operatorname{PotInf}_\sigma$. Hence $I_\sigma$, which is
   $\Diamond I^*_\sigma$, is equivalent to both, and none of the three is possible without being
   true.
3. $\operatorname{AxInf}_\sigma\to\operatorname{PotInf}_\sigma$, where $\operatorname{AxInf}_\sigma$
   is the Axiom of Infinity at $\sigma$.

Their necessitations are theorems too, so $\Box\operatorname{PotInf}_\sigma$ is equivalent to
$\Box I^*_\sigma$ and follows from $\Box\operatorname{AxInf}_\sigma$
(compare [[necessary-infinity-injective-successor]]), and $\Diamond\operatorname{AxInf}_\sigma$
gives $\operatorname{PotInf}_\sigma$.

*Proof.* 1, left to right. The first conjunct of $I^*_\sigma$ is a theorem. Let $m,n$ be numbers
with $\operatorname{Suc}m=\operatorname{Suc}n$. By $\operatorname{PotInf}_\sigma$ at
$\operatorname{Suc}m$, possibly $\operatorname{Suc}m$ holds of some $X$. Necessarily
$\operatorname{Suc}m=\operatorname{Suc}n$ and $n$ is a number, so there $\operatorname{Suc}n$ holds of
$X$ too, and for $y$ with $Xy$ and $m(X-y)$ we have $n(X-y)$ by removal. So
$\Diamond\exists X\, .\,mX\land nX$, and $m=n$ ([[numbers-with-a-common-instance]]).

1, right to left. By induction, every number $n$ has $\Diamond\exists X\, .\,nX$. The empty property
has cardinality $\mathbf 0$. Suppose $\Diamond\exists X\, .\,kX$ but not
$\Diamond\exists X\, .\,\operatorname{Suc}kX$, for a number $k$. Then necessarily no property has
cardinality $\operatorname{Suc}k$, and so necessarily none has cardinality
$\operatorname{Suc}\operatorname{Suc}k$, since such a property less a suitable instance has
cardinality $\operatorname{Suc}k$. So $\operatorname{Suc}k$ and $\operatorname{Suc}\operatorname{Suc}k$
are necessarily coextensive, hence identical (Intensionality), and $k=\operatorname{Suc}k$ by
$I^*_\sigma$. But $k$ possibly holds of some property, and $\operatorname{Suc}k$ cannot.

2. If $n$ is a number and $\neg\Diamond\exists X\, .\,nX$, then necessarily $n$ is a number, and
necessarily $\neg\Diamond\exists X\, .\,nX$ by 4. So necessarily $\operatorname{PotInf}_\sigma$
fails. For $I_\sigma$: $\Diamond I^*_\sigma$ gives $\Diamond\operatorname{PotInf}_\sigma$ by the
necessitation of part 1, so $\operatorname{PotInf}_\sigma$, so $I^*_\sigma$, which gives
$\Diamond I^*_\sigma$ by T.

3. By induction every number holds of some property. The empty property has cardinality
$\mathbf 0$. If $kX$, then $X$ is not coextensive with $\lambda u\, .\,\top$, of which no number holds;
so $\neg Xy$ for some $y$, and $\operatorname{Suc}k$ holds of $X$ with $y$ added, by addition
([[finite-cardinality-arithmetic]]). $\square$
:::

::: lemma {#at-least-numbers}
title: the Peano conditions on the at-least numbers
lean: [Classicism.lowerPeano_of_iStar, Classicism.iStar_of_lowerPeano]
credit: Andrew Bacon with GPT-6 Astra Pro (OpenAI), 28 October 2026 (that the conditions on the at-least numbers imply $I^*_\sigma$, and the correspondence between the numbers and the at-least numbers; Lean-verified as exactPeano_of_lowerPeano and exactLowerBijection_of_lowerPeano in pull request 19 of the map's repository); the converse, and the proof given here, by Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell, who suggested that the lower-Peano conditions are Potential Infinity (24 November 2026)
---
In C, at each type $\sigma$, $I^*_\sigma$ is equivalent to the same conditions on the at-least
numbers,

$$
\forall m\,n\in\operatorname{LowerNat}_\sigma\, .\,\mathbf 0^{\ge}_\sigma\ne\operatorname{Suc}_\sigma m\land
(\operatorname{Suc}_\sigma m=\operatorname{Suc}_\sigma n\to m=n),
$$

so these are a form of Potential Infinity ([[potential-infinity-forms]]), and their necessitation,
Bacon's necessary lower-Peano, of its necessitation.

*Proof.* For a cardinality $n$ let $n^{\ge}:=\lambda X\, .\,\exists X^\prime\subseteq X\, .\,nX^\prime$,
at least $n$. Each identity below holds by Intensionality, the two sides being necessarily
coextensive.

- $\mathbf 0^{\ge}=\mathbf 0^{\ge}_\sigma$: every property includes the empty property.
- $(\operatorname{Suc}n)^{\ge}=\operatorname{Suc}(n^{\ge})$ for a number $n$. If $X^\prime\subseteq X$,
  $X^\prime y$ and $n(X^\prime-y)$, then $Xy$ and $X^\prime-y\subseteq X-y$. If $Xy$,
  $X^\prime\subseteq X-y$ and $nX^\prime$, then $X^\prime$ with $y$ added is included in $X$ and has
  cardinality $\operatorname{Suc}n$, by addition ([[finite-cardinality-arithmetic]]).
- So $n^{\ge}$ is an at-least number for every number $n$, and every at-least number is $n^{\ge}$ for
  some number $n$, by the two inductions.
- $n=\lambda X\, .\,n^{\ge}X\land\neg\operatorname{Suc}(n^{\ge})X$ for a number $n$: exactly $n$ is at
  least $n$ and not at least its successor. If $nX$, then $X$ includes itself, and no $X^\prime\subseteq
  X-y$ with $Xy$ has $nX^\prime$, by part 4 of [[finite-cardinality-arithmetic]]. Conversely let
  $X^\prime\subseteq X$ with $nX^\prime$: either $X\subseteq X^\prime$, and $nX$, or some instance $y$
  of $X$ is not one of $X^\prime$, and then $X^\prime\subseteq X-y$ and $\operatorname{Suc}(n^{\ge})X$.
  Hence $m^{\ge}=n^{\ge}$ implies $m=n$, for numbers $m,n$.

Now $\mathbf 0^{\ge}_\sigma$ differs from every successor at the empty property. Given $I^*_\sigma$
and at-least numbers $m^{\ge},n^{\ge}$ with the same successor,
$(\operatorname{Suc}m)^{\ge}=(\operatorname{Suc}n)^{\ge}$, so
$\operatorname{Suc}m=\operatorname{Suc}n$, so $m=n$ and $m^{\ge}=n^{\ge}$. Conversely, given the conditions on the at-least
numbers and numbers $m,n$ with $\operatorname{Suc}m=\operatorname{Suc}n$,
$\operatorname{Suc}(m^{\ge})=\operatorname{Suc}(n^{\ge})$, so $m^{\ge}=n^{\ge}$, so $m=n$. $\square$
:::

**Weakly inextensible numbers.** The numbers at $\sigma$ are persistent in C: a number is
necessarily a number {lean: Classicism.finiteCardinality_box}. They need not be inextensible. A
possible world may have numbers that are not ours, and then what is necessarily true of each
of our numbers need not be true of every number there. $\mathbb N_\sigma$ is *weakly
inextensible* ([[weak-rigidity-predicates]]) when
$\forall X\, .\,(\forall n\in\mathbb N_\sigma\, .\,\Box Xn)\to\Box\forall n\in\mathbb N_\sigma\, .\,Xn$.
Equivalently, a number that could have some feature is one of our numbers that could have it:
$\Diamond\exists n\in\mathbb N_\sigma\, .\,Xn\to\exists n\in\mathbb N_\sigma\, .\,\Diamond Xn$.
Arithmetic Necessitism at $\sigma$ says that $\Box I^*_\sigma$ makes the numbers rigid, which
includes this at every world.

::: lemma {#weakly-inextensible-numbers}
title: Countable Boolean Completeness makes the numbers weakly inextensible
lean: [Classicism.Proofs.finiteCardinality_weaklyInextensible_of_cbc, Classicism.Proofs.finiteCardinality_weaklyInextensible_of_rc]
credit: Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell, 25 November 2026; from Rigid Comprehension, Barton and Goodsell's Theorem 3 as proved for the map by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr
---
In C, Countable Boolean Completeness at $\sigma$ and $\tau=((\sigma t)t)t$ gives
$\operatorname{WeaklyInextensible}(\mathbb N_\sigma)$. So do Boolean Completeness, Weak Rigid
Comprehension and Rigid Comprehension, which imply it; Rigid Comprehension also does so directly.

*Proof.* Write $H_n:=\lambda x^{(\sigma t)t}\, .\,x=n$ for the haecceity of a cardinality. The
haecceities of the numbers, $\lambda Y\, .\,\exists n\in\mathbb N_\sigma\, .\,Y=H_n$, are
countable relative to $\sigma$: the relation $Y=H_n$ between $Y$ and $n$ witnesses it. Let $Z$ be
their least upper bound.

- For each number $n$, $H_n\le Z$, that is, $\Box Zn$. In particular $\Box Z\mathbf 0_\sigma$.
- $\lambda x\, .\,Z(\operatorname{Suc}_\sigma x)$ is an upper bound of the haecceities too, since
  $\Box Z(\operatorname{Suc}n)$ for each number $n$. So $Z$ lies below it: necessarily, $Z$ is
  closed under successor.
- So necessarily every number is $Z$, by the induction the numbers provide: $\mathbb N_\sigma\le Z$.
- If $\Box Xn$ for each number $n$, then $X$ is an upper bound of the haecceities, so $Z\le X$,
  and $\mathbb N_\sigma\le X$. $\square$
:::

::: lemma {#potential-infinity-and-possible-infinity}
title: weakly inextensible numbers carry Potential Infinity to Possible Infinity at type t
lean: [Classicism.possibleInfinity_of_weaklyInextensible, Classicism.counts_bounded, Classicism.reach_comparable]
credit: Zachary Goodsell (the argument, 24–25 November 2026); the role of weak inextensibility, and the proof as written out, by Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell
---
In C: if $\mathbb N_t$ is weakly inextensible, then
$\operatorname{PotInf}_t\to\Diamond\operatorname{AxInf}_t$.

*Proof.* Write $U$ for $\lambda p^t\, .\,\top$, so that $nU$ says that there are exactly $n$
propositions, and say that $b$ is *reached from* $a$ when $b$ has every property of cardinalities
that $a$ has and that passes to successors. Suppose $\operatorname{PotInf}_t$ and, for a
contradiction, that necessarily some number holds of $U$.

1. *Every possible count is one of our numbers.* For a number $b$, Potential Infinity gives
   $\Diamond\exists X\, .\,bX$; there some number holds of $U$; so by weak inextensibility some
   number $n$ of ours has $\Diamond(nU\land\exists X\, .\,bX)$.
2. *The possible counts are bounded.* Claim: for a property $Y$ of propositions with a finite
   cardinality, some number $b$ is reached from $\operatorname{Suc}n$ for every number $n$ with
   $\Diamond nU$ and $Y(nU)$. By induction on the cardinality. If $Y$ has no instance, any $b$ will
   do. Otherwise remove an instance $p$ and take a bound $b^\prime$ for the rest. If $p$ is
   $sU$ for a number $s$ with $\Diamond sU$, then $s$ is the only such number, numbers that could
   hold of one property being identical ([[numbers-with-a-common-instance]]); of two numbers one
   is reached from the other, so take whichever of $b^\prime$ and $\operatorname{Suc}s$ is reached
   from the other. If $p$ is no such proposition, keep $b^\prime$. Now apply the claim to $U$
   itself, which some number holds of: some $b$ is reached from $\operatorname{Suc}n$ for every
   number $n$ with $\Diamond nU$.
3. *Contradiction.* By step 1 at that $b$, some number $n$ has $\Diamond(nU\land\exists X\, .\,bX)$,
   and $b$ is reached from $\operatorname{Suc}n$, necessarily so. At such a world a property with
   cardinality $b$ has a subproperty with cardinality $\operatorname{Suc}n$, though $U$, which
   includes it, has cardinality $n$: impossible, since no proper subproperty has the same finite
   cardinality ([[finite-cardinality-arithmetic]]). $\square$

Weak inextensibility is used in step 1 only, and the argument does not go through without it:
that every possible world has finitely many propositions gives each a count that is a number
there, and the propositions $nU$ of step 2 are indexed by our numbers. At type $e$ nothing
of the kind holds, the propositions that there are exactly $n$ individuals being no obstacle
to there being finitely many individuals.
:::

::: lemma {#real-structures-isomorphic}
title: real number structures are isomorphic
credit: Dedekind's categoricity theorem for the numbers, carried to the reals by extensionality and fullness; written out by Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell, 26 November 2026
---
In the non-modal fragment of C. Let $\mathfrak R=(N,0,S,X,E)$ and
$\mathfrak R'=(N',0',S',X',E')$ be real number structures, at types $\sigma$ and $\sigma'$.
Then there are relations $f$ and $g$ of type $\sigma\sigma' t$ such that $f$ is a bijection
between the numbers of $\mathfrak R$ and those of $\mathfrak R'$ taking $0$ to $0'$ and
successors to successors, $g$ is a bijection between their reals, and
$Enx\leftrightarrow E'n'x'$ whenever $fnn'$ and $gxx'$. So every analytical sentence,
first-order or second-order, has the same truth value in the two.

*Proof.* Let $f$ be the least relation holding of $0$ and $0'$ and of the successors of any
$m$ and $m'$ it holds of:
$fnn':=\forall F^{\sigma\sigma' t}\, .\,(F00'\land\forall m\,m'\,k\,k'\, .\,Fmm'\land Smk\land S'm'k'\to Fkk')\to Fnn'$.

- By the induction that $N$ provides, every number of $\mathfrak R$ bears $f$ to a number of
  $\mathfrak R'$, and to one only. $0$ bears it to $0'$ alone: $0$ is no successor, so $f$
  without the pairs of $0$ with the other numbers of $\mathfrak R'$ still holds of $0$ and $0'$
  and of successors, and $f$ is the least such relation. And if $m$ bears $f$ to $m'$ alone,
  the successor of $m$ bears it to the successor of $m'$ alone, by the same argument and the
  injectivity of $S$.
- The same with the structures exchanged: every number of $\mathfrak R'$ has $f$ borne to it by
  exactly one number of $\mathfrak R$.
- $f$ takes sums to sums and products to products, these being defined in both structures by
  the same recursion on zero and successor.
- Let $gxx':=Xx\land X'x'\land\forall n\,n'\, .\,fnn'\to(Enx\leftrightarrow E'n'x')$. For a real
  $x$ of $\mathfrak R$, some real $x'$ of $\mathfrak R'$ has as its members just the numbers
  $n'$ with $\exists n\, .\,fnn'\land Enx$, by fullness, and then $gxx'$. A second such real has
  the same members as $x'$ and so is $x'$, by extensionality. The same with the structures
  exchanged makes $g$ a bijection.
- An analytical sentence keeps its truth value, by induction on formulas: a relation among the
  numbers and reals of one structure is carried to one among those of the other by
  $\lambda$-abstraction, along $f$ in its places for numbers and along $g$ in its places for
  reals, and back. $\square$
:::

::: lemma {#real-structures-and-fields}
title: real number structures and complete ordered fields
credit: Zachary Goodsell, 26 November 2026 (that the field is bookkeeping, and the definition of real number structures by a membership relation); written out by Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell
---
Call $\mathfrak F=(X^{\sigma t},\le,+,\times,0,1,N^{\sigma t})$ a *complete ordered field
with its natural numbers* at $\sigma$ when $\le$, $+$ and $\times$ hold only of instances of
$X$, $X$ with them and with $0$ and $1$ is an ordered field, $+$ and $\times$ being
functional on $X$, every nonempty subproperty of $X$ with an upper bound in $X$ has a least
upper bound in $X$, and $N$ is the least subproperty of $X$ containing $0$ and closed under
adding $1$. These are Bacon's real number structures, and were the map's until 26 November
2026. Its first-order analytical sentences were the first-order sentences of the language of
$\mathfrak F$, and its second-order ones added relation variables among the instances of
$X$. $\mathfrak F$ was rigid when $X$, $\le$, $+$, $\times$ and $N$ are rigid and the
instances of $X$ necessarily distinct, and a represented power of arity $k$ for it was a rigid
property of rigid $k$-ary relations among the instances of $X$ with which every $k$-ary
relation necessarily agrees on them.

1. *Each defines the other.* In the non-modal fragment of C, a complete ordered field with
   its natural numbers $\mathfrak F$ at $\sigma$ defines a real number structure
   $\mathfrak F^\ast$ at $\sigma$ by first-order formulas of its language, and a real number
   structure $\mathfrak R$ at $\sigma$ defines a complete ordered field with its natural
   numbers $\mathfrak R^\circ$ at $\sigma$ by first-order analytical formulas.
2. *Rigidly.* In C, if $\mathfrak F$ is rigid and necessarily a complete ordered field with
   its natural numbers, then $\mathfrak F^\ast$ is rigid and necessarily a real number
   structure. If $\mathfrak R$ is rigid and necessarily a real number structure, then
   $\mathfrak R^\circ$ is rigid and necessarily a complete ordered field with its natural
   numbers.
3. *With their powers.* In either case of 2, a represented power of arity $k$ for the given
   structure restricts to one for the structure it defines.

So each principle of analysis is equivalent in C, type by type, to what it said of complete
ordered fields. There could be a real number structure at $\sigma$ just in case there could
be a complete ordered field with its natural numbers at $\sigma$, by 1; and there is a rigid
one that is necessarily a real number structure, with represented powers or without, just in
case there is such a field, by 2 and 3. Those are the instances at $\sigma$ of Analytic
Necessitism and of its second-order form. For the necessity schemas, an analytical sentence
read in $\mathfrak F^\ast$ is equivalent to a sentence of the language of $\mathfrak F$ of the
same order, the sum and product of $\mathfrak F^\ast$ being $+$ and $\times$ on $N$, and a
sentence of that language read in $\mathfrak R^\circ$ is equivalent to an analytical sentence of
the same order; and within a world all the structures of either kind agree on each of these, being
isomorphic ([[real-structures-isomorphic]]; Huntington's theorem for the fields). The
continuum hypothesis of $\mathfrak F^\ast$ is equivalent to that of $\mathfrak F$ as it was
stated, every subproperty of $X$ injecting into $N$ or being in bijection with $X$: the reals
of $\mathfrak F^\ast$ are in bijection with the instances of $X$, by the Cantor–Bernstein
theorem.

*Proof.* 1, from a field. The numbers of $\mathfrak F^\ast$ are $N$, with $0$ and adding $1$.
A complete ordered field is Archimedean, and the powers of $4$ are first-order definable on
$N$ from $+$ and $\times$ (Gödel's coding of finite sequences). For $0\le x<1$ and $n\in N$,
the *$n$th digit* of $x$ is the remainder on division by $4$ of the greatest $k\in N$ with
$k\le 4^{n+1}\times x$. The reals of $\mathfrak F^\ast$ are the $x$ with $0\le x<1$ all of
whose digits are $0$ or $1$, and $n$ is a member of such an $x$ when its $n$th digit is $1$.
*Extensional.* Two of them with the same members have the same digits, so they differ by less
than $4^{-n}$ for every $n\in N$, and are identical. *Full.* For a property $Y$, let $s_n$ be
the sum of the $4^{-(k+1)}$ for the $k<n$ with $Yk$, defined by recursion on $N$. The $s_n$
are less than $1$, so they have a least upper bound $x$; and since the terms after the
$n$th add up to less than $4^{-(n+1)}$, the $n$th digit of $x$ is $1$ if $Yn$ and $0$ if not.

1, from a real number structure. Code pairs of numbers by numbers with a pairing function
defined from sum and product, and with it the rationals. The elements of $\mathfrak R^\circ$
are the reals whose members are the codes of a Dedekind cut: of a nonempty set of rationals,
closed downwards and with no greatest member, that omits some rational. Its order is
inclusion of members; its sum, product, $0$ and $1$ are those of cuts, given by formulas that
quantify over numbers only; and its natural numbers are the cuts of the rationals below a
number. The sum and the product of two cuts are the members of a real, by fullness, and with
that the field axioms are proved as in second-order arithmetic. *Complete.* For a nonempty
subproperty $P$ of the elements with an upper bound, some real has as its members just the
codes that are members of an instance of $P$, by fullness; it is a cut, and the least upper
bound of $P$. *Natural numbers.* A subproperty containing the cut of $0$ and closed under
adding $1$ contains the cut of every number, by the leastness of $N$.

2. By the induction of [[analytic-necessitism-implies-necessity-of-analysis]], every
first-order formula of the language of a rigid $\mathfrak F$ is necessary if true and
impossible if false at instances of $X$, and so is every first-order analytical formula at
numbers and reals of a rigid $\mathfrak R$ that is necessarily a real number structure. A
relation $Q$ defined by such a formula among the instances of rigid properties
$D_1,\ldots,D_k$ is rigid. It is persistent, its facts being necessary if true. It is
inextensible by the inextensibility of $D_k,\ldots,D_1$ in turn: if every instance of $Q$
necessarily has $Z$, then for $u_1,\ldots,u_{k-1}$ in $D_1,\ldots,D_{k-1}$ each instance
$u_k$ of $D_k$ necessarily has $Q\bar u\to Z\bar u$, whichever way $Q\bar u$ is settled, so
necessarily every instance of $D_k$ has it; and so on down to $D_1$. This holds at every world
as at the actual one, which is what the leading boxes of persistence and inextensibility ask:
the hypotheses are necessary if true, rigidity by [[rigid-necessary]], being necessarily of its
kind by 4, and the necessary distinctness of the instances of rigid properties by 4 and their
inextensibility. The successor, reals and
membership of $\mathfrak F^\ast$ are so defined among instances of $N$ and $X$, and the
elements, order, sum, product and natural numbers of $\mathfrak R^\circ$ among instances of
its $X$. Necessary distinctness is inherited, the numbers and reals of $\mathfrak F^\ast$
being instances of $X$ and the elements of $\mathfrak R^\circ$ reals of $\mathfrak R$. That
the defined structure is necessarily of its kind is 1, necessitated; the zero and one of
$\mathfrak R^\circ$, reals picked out by their members, have those members necessarily.

3. Let $\mathcal P$ be a represented power of arity $k$ for the given structure, and $D'$ the
property of being a number or a real, or an element, of the structure it defines. The
instances of $D'$ are among the elements, or the numbers and reals, of the given structure,
and of each of those it is necessary or impossible that it is an instance of $D'$: by 2, and
because a number of $\mathfrak R$ that is not a real is necessarily not one, by the
inextensibility of $X$, every real being necessarily distinct from it. So the restrictions
$\lambda\bar u\, .\,Q\bar u\land\bigwedge_iD'u_i$ of the instances $Q$ of $\mathcal P$ are
rigid, at every world as in 2: persistent with $Q$, and inextensible by the inextensibility of $Q$, each tuple it holds
of being necessarily one of instances of $D'$ or necessarily not. The property of being such a
restriction is persistent by the persistence of $\mathcal P$ and the necessity of identity, and
inextensible by the inextensibility of $\mathcal P$. And a relation that agrees
with $R$ on the given structure agrees with it on the instances of $D'$. $\square$
:::

::: lemma {#rigid-power-of-the-numbers}
title: the rigid properties of the numbers are the reals of a real number structure
credit: Zachary Goodsell, 26 November 2026 (that with real number structures defined by membership the passage from Bacon's cardinal continuum hypothesis is immediate); written out by Claude Fable 5.2 (Anthropic), prompted by Zachary Goodsell
---
In C, at a type $\tau$. Write $\nu$ for $\nu_\tau$, $N$ for the at-least numbers at $\tau$,
$\operatorname{LowerNat}_\tau$, $0$ for $\mathbf 0^{\ge}_\tau$, and $\mathcal P_rN$ for the rigid
properties of numbers, $\lambda A^{\nu t}\, .\,\operatorname{Rigid}(A)\land\forall n\, .\,An\to Nn$.
Suppose that the Peano conditions hold on the at-least numbers, which is Potential Infinity at
$\tau$ ([[at-least-numbers]]), and that every property of type $\nu t$ is coextensive with a
rigid one, which is Rigid Comprehension at that type. Then the rigid properties of numbers are
the reals of a real number structure at $\nu t$, with instantiation for membership. A number
$n$ is represented in it by the property $\{n\}:=\lambda m^\nu\, .\,m=n$ of being $n$:

- its numbers are $\hat N:=\lambda a^{\nu t}\, .\,\exists n\, .\,Nn\land a=\{n\}$, with zero
  $\{0\}$ and successor
  $\hat S:=\lambda a\,b\, .\,\exists n\, .\,Nn\land a=\{n\}\land b=\{\operatorname{Suc}_\tau n\}$;
- its reals are $\mathcal P_rN$, with membership
  $\hat E:=\lambda a\,A\, .\,\exists n\, .\,Nn\land a=\{n\}\land\mathcal P_rN(A)\land An$.

The same holds of the numbers $\mathbb N_\tau$ with $\mathbf 0_\tau$.

*Proof.* *Numbers.* $\{m\}=\{n\}$ only if $m=n$, so the conditions on $\hat N$, $\{0\}$ and
$\hat S$ are those on $N$, $0$ and successor. $0$ is an at-least number and the successor of
one is one, by the definition of $N$, which is also why $\hat N$ is least: a property that
holds of $\{0\}$ and of $\{\operatorname{Suc}_\tau n\}$ whenever it holds of $\{n\}$ holds of
$\{n\}$ for every at-least number $n$. $0$ is no successor and distinct at-least numbers have
distinct successors, by the Peano conditions. *Membership.* By the definition of $\hat E$,
under which $\{n\}$ is a member of a real $A$ just in case $An$. *Extensional.* Let $A$ and
$B$ be rigid properties of numbers with the same members, and so the same instances. Each
instance of $A$ is an instance of $B$, and necessarily one, $B$ being persistent; so by the
inextensibility of $A$, necessarily every instance of $A$ is one of $B$. Likewise necessarily
every instance of $B$ is one of $A$. So $A=B$, by Intensionality. *Full.* For a property $Y$
of type $(\nu t)t$, Rigid Comprehension gives a rigid $Z$ coextensive with
$\lambda n\, .\,Nn\land Y\{n\}$. It holds only of numbers, so it is a rigid property of
numbers, and $\{n\}$ is a member of it just in case $Y\{n\}$, for every number $n$. $\square$

At $\tau=e$ the continuum hypothesis of this structure says that every collection of rigid
properties of at-least numbers over individuals injects into the at-least numbers, by way of
the properties $\{n\}$, or is in bijection with the rigid properties of them. That is the
cardinal continuum hypothesis of Bacon's forcing argument, whose conclusions are therefore the possibility of the continuum hypothesis, and of its failure,
in a real number structure, so that Non-contingency of the Continuum Hypothesis fails
([[mathematical-possibilism-and-relational-choice-incompatible-with-non-contingency-of-ch]]).
:::
