# □Rigid Comprehension, Rigid Power and □Axiom of Infinity imply the Necessity of Second-Order Analysis

The idea is Cian Dorr's (30 October 2026). If the numbers are rigid, Rigid Power makes the rigid
properties of numbers, the reals, a rigid property, and then makes the rigid properties of reals a rigid
property. Under □Rigid Comprehension every real, and every class of reals, at any world is one of these,
so there can be no new reals and no new sets of reals.

The argument is Barton and Goodsell's (*Continuum Contingency*, §§5.6–5.9, Theorems 2–7). In their CR∞,
□Rigid Comprehension with their axiom of Infinity, the one missing ingredient is the inextensibility of
the reals and of the classes of reals; Rigid Power supplies it. Written out by Claude Opus 5.5
(Anthropic), prompted by Cian Dorr. Not Lean-verified.

§4 and two sentences of §5 were revised by Claude Fable 5.2 (Anthropic), prompted by Zachary
Goodsell, 26 November 2026, for real number structures as numbers and reals with a membership relation:
the canonical structure is the reals of §2 with the numbers, where it was a field of Dedekind cuts
among them.

Fix the type $\sigma$ of the infinity premise ($e$ here, $t$ in the companion record), and write
$\mathbb N:=\mathbb N_\sigma$ for the finite cardinalities at $\sigma$, of type $\nu_\sigma$. Assume
□Rigid Comprehension, Rigid Power, and $\Box\operatorname{AxInf}_\sigma$. "At every world" means at
every world accessible from the actual one. Rigid Power is used only at the actual world, and only at
two instances.

## 1. The numbers

$\Box\operatorname{AxInf}_\sigma$ gives $\Box I^*_\sigma$ ([[necessary-infinity-injective-successor]]).
So □Rigid Comprehension gives Arithmetic Necessitism at $\sigma$
([[necessary-rigid-comprehension-implies-arithmetic-necessitism]], Barton and Goodsell's Theorem 3):
$\mathbb N$ is rigid and its members are necessarily distinct. Arithmetical sentences are then
non-contingent, and all the second-order Peano axioms hold at every world, by their Theorem 2.

## 2. The reals

Let $R:=\lambda X^{\nu_\sigma t}\, .\,\operatorname{Rigid}(X)\land X\le\mathbb N$, the rigid properties of
numbers. Rigid Power at the rigid $\mathbb N$ says that $R$ is rigid.

Distinct reals are necessarily distinct (Barton and Goodsell's Theorem 4). Two coextensive rigid
properties are identical (Background), so distinct reals $X,Y$ differ on some number $n$, say $Xn$ and
$\neg Yn$. Then $\Box Xn$, by persistence. And $\Box\neg Yn$: every instance of $Y$ is a number other
than $n$, hence necessarily other than $n$, so weak inextensibility puts $Y$ below
$\lambda x\, .\,x\ne n$.

**No new reals.** At any world $u$, take a property $G$ of numbers. By Rigid Comprehension at $u$, $G$
is coextensive there with a rigid $X$. The instances of $X$ are numbers, and numbers are necessarily
numbers, so weak inextensibility at $u$ gives $X\le\mathbb N$, and $RX$ holds at $u$. Since $R$ is
rigid, $X$ is one of the actual reals. So at every world, every property of numbers is coextensive with
an actual real.

## 3. Classes of reals, and relations among them

Let $\mathcal P R:=\lambda Y\, .\,\operatorname{Rigid}(Y)\land Y\le R$. Rigid Power at the rigid $R$
says that $\mathcal P R$ is rigid. Its members are necessarily distinct, by the argument of §2 using the
necessary distinctness of reals (their Theorem 6). The argument of §2, one type up, shows that at every
world every property of reals agrees on the reals with an actual member of $\mathcal P R$.

Relations reduce to classes, as in Barton and Goodsell's §5.7:
- Pairs of reals are coded by reals: $X\oplus Y$ holds of $2n$ iff $Xn$ and of $2n+1$ iff $Yn$. At each
  world this is a property of numbers, so it is coextensive with a real, by §2.
- Numbers are coded by reals, as singletons.

So at every world, every relation of finite arity among reals and numbers agrees on them with a relation
coded by an actual member of $\mathcal P R$.

## 4. The canonical real number structure

Its reals are the members of $R$. Its numbers are the properties $\{n\}:=\lambda m\, .\,m=n$ of being
a given number $n$ in $\mathbb N$, with $\{\mathbf 0\}$ for zero and $\{\operatorname{Suc} n\}$ for the
successor of $\{n\}$; and $\{n\}$ is a member of a real $X$ when $Xn$ (Background,
[[rigid-power-of-the-numbers]]).

**It is necessarily a real number structure.**
- At any world its numbers satisfy the conditions on zero and successor, by §1.
- It is extensional there: reals with the same members are coextensive rigid properties, so identical
  (Background).
- It is full there. A property of the $\{n\}$ picks out a property of numbers, which by §2 is
  coextensive with an actual real.

**Its components are rigid.** They are defined from rigid properties by formulas whose atomic parts are
non-contingent, and they are restricted to rigid domains. Its numbers are among its reals, which are
necessarily distinct (§2).

## 5. Non-contingency

Take a second-order analytical sentence $A$.
- By §3, at every world, $A$ read in the canonical structure is equivalent to a sentence $A^*$ of
  Barton and Goodsell's second order. Its first-order variables range over $\mathbb N$ and $R$, its
  second-order variables over $\mathcal P R$, and its atomic formulas are memberships and identities,
  with the sums and products of numbers, which §1 makes non-contingent.
- By their Theorem 7, $\Box A^*\lor\Box\neg A^*$:
  - the atomic formulas are non-contingent, by rigidity and necessary distinctness;
  - Boolean combinations of non-contingent formulas are non-contingent;
  - a quantifier restricted to a rigid property with a non-contingent matrix gives a non-contingent
    formula.
- So $A$ is non-contingent in the canonical structure.

Finally, compare with an arbitrary real number structure. At any world, any real number structure, at
any type, is isomorphic to the canonical one there (Background, [[real-structures-isomorphic]], in the
non-modal fragment).
Isomorphic structures agree on second-order analytical sentences, because relations transfer along the
isomorphism by composition, which Ordinary Comprehension supplies. Hence
$\Box\forall\mathfrak R\, .\,\operatorname{Real}(\mathfrak R)\to A(\mathfrak R)$ or the same with
$\neg A$. $\square$

## Remarks

- **Only one infinite type is needed.** Every comparison of structures is made within a world, so one
  type with necessarily infinitely many members suffices. That is why the record holds with
  □Axiom of Infinity at $e$ and, by the same proof, at $t$. The two premises are independent.
- **The box on Rigid Comprehension is needed.** With Rigid Comprehension only at the actual world, a
  world can have a property of numbers coextensive with no rigid property there: a new real that Rigid
  Power does not constrain. [[full-boolean-valued-atom-and-atomless]] has Rigid Comprehension, Rigid
  Power, □Rigid Power and Arithmetic Necessitism, and refutes the Non-contingency of CH.
- **Rigid Power is needed.** Barton and Goodsell's stitched models satisfy □Rigid Comprehension, their
  Infinity and Arithmetic Necessitism, and refute it, as they must.
- **The infinity premise may not be.** Whether it can be dropped is open. Bacon's Theorem 5.2 gets the
  same conclusion from Atomicity and □Rigid Comprehension with no infinity premise, by relativizing to
  worlds with a natural number structure, and its use of Atomicity is essentially to get Rigid Power.

## Paper references

- **Proof: Continuum Contingency.** Barton, Neil, and Zachary Goodsell. Continuum Contingency. Draft dated 14 October 2026, 47 pages. Stitches a ground model of set theory to the canonical model of a forcing extension to show that Classicism with □Rigid Comprehension, □Relational Choice and an axiom of infinity is consistent with first- and second-order continuum contingency, together with □Atomicity at type t (Theorem 21) or with Recombination (Theorem 22, which refutes Atomicity at type t, Corollary 23); formalizes the coin-toss argument (Theorem 9). Read directly on 19 October 2026; locators refer to this draft. — §§5.6–5.9, Theorems 3–7 and eqs. (22)–(33), pp. 16–21. Their reals are the rigid properties of numbers, R = PN, and their Theorem 7 derives the non-contingency of analytical sentences from continuum necessitism; Rigid Power at N and at R is that necessitism.
