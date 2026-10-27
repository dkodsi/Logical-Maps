# Relational Choice and propositional completeness imply Actuality over C5

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated.

## 1. Statement and proof idea

In the fixed finitary relational language,

```math
\boxed{C5+BC_t+RC_{t,t}\ \Longrightarrow\ \mathrm{Actuality}}
\tag{1}
```

Here RC_{t,t} is the single Relational Choice instance whose inputs and outputs are propositions. BC_t is current Boolean completeness of propositions. Neither premise is boxed. The proof does not assume OS, all-type RC, BC_tt, an admitted strict splitting operation, or a crisp wellorder of all propositions.

The argument uses two applications of RC_{t,t}. The first gives an admitted operation presenting a partition of every positive proposition in a true interval into proper nonzero parts. It does not give a binary splitter: each partition may have arbitrarily many parts. A current functional relation follows the unique true part of these partitions. BC_t supplies its canonical descending chain and a false terminal member.

The second choice application selects one partition child of each discarded part along this chain. Their actual join is a Boolean code b. Every discarded part has only children that are monochromatic for b; every true chain member has a child meeting both b and its complement. This gives a crisp test which identifies the selected child at every true chain member. A lambda-defined operation collects the children passing that test. Its crisp canonical chain agrees with the original chain up to the false terminal member. The predecessor cut at that member is therefore crisp, making the terminal member a material meet of truths, a contradiction.

## 2. Background facts and the two canonical-chain lemmas

Write 0 and 1 for Bottom and Top, and use the algebraic Boolean order p≤q, meaning p∧q=p. A formula is **crisp** when its proposition is 0 or 1. C5 makes identities crisp, supplies Barcan, and makes Boolean combinations and quantified formulas of crisp assertions crisp. In particular, order comparisons and their quantified combinations are crisp and necessary when true.

We use the following C5 bound calculation. For any admitted operation v indexed by a fixed admitted type, the material existential over its entire range is the actual algebraic join of those range values. More generally, if A is crisp, then

```math
\exists x\,[A(x)\land v(x)]
\tag{2}
```

is the actual algebraic join of the values v(x) at current A-members. Universal instantiation gives each bound. Conversely, a current algebraic bound at every index is a family of true identity statements; C5 and Barcan make the corresponding universal bound necessary, giving the algebraic bound on (2). The order-dual calculation applies to material universals. This fact is about crisp-indexed families or entire admitted ranges. It does not identify arbitrary current BC_t suprema with material existentials.

Two previously proved chain lemmas are used:

1. **Current relational canonical chain.** In a represented antisymmetric poset with a least element and suprema of all represented chains, a represented total progressive functional relation has a canonical internally wellordered chain ending at a fixed point. Function notation abbreviates its unique current graph value; an operation representing that graph is unnecessary. See [the represented and descending canonical-chain lemmas](propositional-canonical-chain-lemmas.md).
2. **Strong crisp canonical chain.** Under C5, an admitted necessarily deflationary operation g on [0,a] has a crisp descending canonical chain N, fully wellordered in reverse Boolean order against **all admitted current subproperties**, and ending at a fixed point. Its conformity and full wellordering hold necessarily. No BC assumption is used in this lemma. See [the strong crisp-chain lemma](propositional-canonical-chain-lemmas.md#3-strong-crisp-chains-for-operations).

For both descending chains, conformity means that a member x is the actual infimum, in [0,a], of the successor values at its strict predecessors:

```math
x=\inf\{f(y):y\text{ belongs to the chain and }x<y\}
\tag{3}
```

The empty predecessor family has infimum a. The stronger lemma in item 2 is important: wellordering only against crisp subproperties would not justify the later comparison with a possibly noncrisp chain.

## 3. A uniform strict partition on a true core

Suppose h is currently true and [0,h] is atomless. Put

```math
A_h(p):=(0<p\land p\le h)
```

For each current A_h-member p there is a q with 0<q<p. Thus the relation

```math
R(p,q):=[A_h(p)\land 0<q<p]
\lor[\neg A_h(p)\land q=0]
\tag{4}
```

is currently serial. It is crisp. Apply RC_{t,t} to obtain a current total functional subrelation K of R.

Normalize its coefficients by

```math
\begin{aligned}
c_p(q)&:=K(p,q)\land R(p,q)\\
&\quad\land\forall z\,[(K(p,z)\land R(p,z))\to z=q],\\
d_p&:=\exists q\,c_p(q)
\end{aligned}
\tag{5}
```

For every current p, its selected K-output has a true coefficient, so d_p is currently true. For distinct q,z the coefficients c_p(q),c_p(z) are algebraically disjoint: their conjunction implies q=z, and under C5 a false identity is 0. Also a coefficient with false R(p,q) is 0, because R is crisp.

Define

```math
a:=h\land\forall p\,d_p
\tag{6}
```

Then a is currently true, a≤h, and a≤d_p for every p. For all p,q define admitted operations

```math
u_0(p,q):=p\land c_p(q)\land q,
\qquad
u_1(p,q):=p\land c_p(q)\land\neg q
\tag{7}
```

For 0<p≤a their positive values form a partition of p into proper parts:

* Values belonging to distinct q are disjoint by the disjointness of their coefficients; the two values at one q are disjoint by q∧¬q=0.
* If either value is nonzero, its coefficient is nonzero. Since p≤h and R is crisp, this gives 0<q<p. Hence u_0(p,q)≤q<p, and u_1(p,q)≤p∧¬q<p. Thus each positive value is strictly below p.
* Their range join is p. Indeed the Boolean and quantifier laws give

```math
\exists q\,[u_0(p,q)\lor u_1(p,q)]
=p\land d_p=p
\tag{8}
```

  By the entire-range calculation of §2 this is also their actual algebraic join.

Define the admitted relation

```math
\mathrm{Child}(p,r):=
(0<p\le a)\land r>0\land
\exists q\,[r=u_0(p,q)\lor r=u_1(p,q)]
\tag{9}
```

This relation is crisp: its assertions are identities, order comparisons, and quantifiers over them. For each 0<p≤a its current members are pairwise disjoint, all are strictly below p, and their actual join is p. Thus there is at least one positive child. Moreover, for **each** child r there is a different child: otherwise the whole join would be r<p. These existence claims concern nonzero entities, not current truth of their propositions.

Because Child is crisp, its weighted material join is its actual join. In particular,

```math
p=\exists r\,[\mathrm{Child}(p,r)\land r]
\qquad(0<p\le a)
\tag{10}
```

Therefore, if p is currently true, exactly one of its children is currently true. Existence follows from (10), and uniqueness follows from disjointness. No child is asserted to be true when p is false.

## 4. The truth-guided relational chain and its discarded children

On [0,a] define a current functional relation F as follows:

```math
F(p,r):=[\neg p\land r=p]
\lor[p\land\mathrm{Child}(p,r)\land r]
\tag{11}
```

When p is false it selects p itself. When p is true, (10) supplies exactly one true child. Hence F is total, single-valued, deflationary, and strictly deflationary at every true p. It is an admitted relation; no operation with these literal outputs has been extracted.

BC_t supplies all represented infima in [0,a]. Apply the current relational canonical-chain lemma. Let M be its canonical chain and m its terminal fixed point. Then:

* m is false, since every true point is strictly decreased;
* every other M-member is true, since each false point is fixed and a fixed point in a canonical chain is terminal;
* for a true M-member p, its unique graph value F(p) is a true M-member and the next member of the chain;
* if q<p are M-members, then q≤F(p), by conformity at q.

Define the represented family of discarded positive children by

```math
\Delta(d):=\exists p,r\,[Mp\land p\land F(p,r)
\land\mathrm{Child}(p,d)\land d\ne r]
\tag{12}
```

Each Δ-member is positive, lies below a, and is false. Crucially, distinct Δ-members are algebraically disjoint **across all stages**. At one parent this is the partition property. If p>q are different true M-parents, every child discarded at q lies below q≤F(p), whereas every child discarded at p is disjoint from F(p). Thus the two discarded children are disjoint. In particular, a positive discarded child cannot reappear at a different stage.

Every true M-member has at least one discarded positive child, since its selected child is strictly smaller and the entire partition has join equal to the parent.

## 5. One Boolean code from a second relational choice

For each Δ-member d, its Child-partition is nonempty and all its members are strictly below d. Apply RC_{t,t} to the serial relation

```math
[\Delta(d)\land\mathrm{Child}(d,r)]
\lor[\neg\Delta(d)\land r=0]
\tag{13}
```

Let J(d,r) be the resulting current total functional selector graph. For d∈Δ write r_d for its unique current output. Thus

```math
\mathrm{Child}(d,r_d),\qquad 0<r_d<d
\tag{14}
```

This notation does not assert that d↦r_d is represented by an operation. Its image over Δ is the admitted current property

```math
Y(r):=\exists d\,[\Delta(d)\land J(d,r)]
```

Use BC_t to choose its actual supremum b. For every current d∈Δ,

```math
b\land d=r_d
\tag{15}
```

Indeed r_d≤b and r_d≤d. Conversely, every other selected r_e lies below a discarded e disjoint from d. Hence ¬d∨r_d bounds all members of Y, including r_d itself; the least-upper-bound property gives b≤¬d∨r_d. Meeting with d proves (15).

Define the crisp formulas

```math
\begin{aligned}
\mathrm{Mixed}(x)&:=(x\land b>0)\land(x\land\neg b>0),\\
H(c)&:=\exists e\,[\mathrm{Child}(c,e)\land\mathrm{Mixed}(e)]
\end{aligned}
\tag{16}
```

They have the following opposite behaviours.

**Discarded children fail H.** If d∈Δ and Child(d,e), then e is either r_d or disjoint from r_d, because r_d is itself a child in the same partition. In the first case e≤b. In the second, e∧b=e∧d∧b=e∧r_d=0. Thus no child of d is mixed, so H(d) is false.

**True chain members satisfy H.** If c is a true M-member, choose a positive child d discarded at c. Then d∈Δ, and (14)–(15) give

```math
d\land b=r_d>0,
\qquad
d\land\neg b=d\land\neg r_d>0
```

Thus d is a mixed child of c and H(c) is true.

Consequently, at a true M-member p, exactly one Child(p,c) satisfies H(c), namely its selected true successor F(p). All other children are discarded and fail H. Because H is crisp, these true and false values are literal 1 and 0.

## 6. The decoded operation

Define the admitted operation

```math
g(p):=p\land\exists c\,[\mathrm{Child}(p,c)\land H(c)\land c]
\tag{17}
```

It is globally deflationary: g(p)≤p. It sends 0 to 0 and maps [0,a] into itself. Those are identities or quantified identity formulas, so C5 makes the required interval and progress hypotheses necessary.

For every true M-member p,

```math
g(p)=F(p)
\tag{18}
```

as an **entity identity**. The crisp guard Child(p,c)∧H(c) selects exactly the one entity F(p); by §2 its weighted material join is that entity. Thus (18) does not infer identity merely from agreement in current truth.

The operation g need not strictly decrease every positive proposition. Strictness is needed only on the true members of M, where (18) and (11) supply it. This is why the construction can use arbitrary partitions without first producing a binary strict splitter.

## 7. Comparing the chains and deriving the contradiction

Apply the strong crisp-chain lemma to g on [0,a]. Obtain a crisp, necessarily fully reverse-wellordered g-chain N with a terminal fixed point u.

Compare M and N by their common initial segment I, defined using common membership and equality of the predecessor **extensions**. If m∈I, then M is already an initial segment of N. Otherwise every I-member is a true M-member, and F and g agree there by (18). If both chains had a first member outside I, full current wellordering supplies those first members; conformity makes both the infimum of the same current successor-image family. Antisymmetry identifies them, extending I, a contradiction. Hence one chain is an initial segment of the other.

N cannot be a proper initial segment of M. If it were, its fixed endpoint u would be an M-member strictly before the terminal m, and hence true. But then

```math
g(u)=F(u)<u,
```

contradicting g(u)=u. Therefore M is an initial segment of N, including m. This argument uses no global strictness of g.

The predicate

```math
I_m(p):=Np\land m<p
\tag{19}
```

is crisp. Its current members are exactly the strict predecessors of m in M. All are true, and their g-values equal their true F-values. Thus

```math
a\land\forall p\,[I_m(p)\to g(p)]
\tag{20}
```

is currently true. Since I_m is crisp, §2 identifies (20) with the actual algebraic infimum in [0,a] of these g-values. Conformity of N at m identifies that infimum with m. This makes m true, contradicting §4.

We have proved that C5+BC_t+RC_{t,t} permits no currently true atomless interval.

## 8. Actuality and exact dependency scope

Under C5, Atom(p) is crisp. Hence

```math
z:=\exists p\,[\mathrm{Atom}(p)\land p]
\tag{21}
```

is the algebraic join of the atoms by §2. If z is true, a true atom witnesses Actuality. If z is false, h=¬z is true and [0,h] is atomless: any atom below h would also lie below z, and so would be 0. The latter case is ruled out by §§3–7. Therefore Actuality follows, proving (1).

The proof uses:

* C5 for crisp identities and quantified identity assertions, the crisp-family bound calculation, and the strong crisp canonical-chain lemma;
* two applications of the **same unboxed instance RC_{t,t}**, first for proper parts and then for children of discarded parts;
* unboxed BC_t for the current relational chain's bounds and for the single code b.

No selected graph is extracted into an operation. The operations u_0,u_1 and g are explicit admitted lambda terms, with the literal identities needed for g justified by crisp indexing. No coextension of predicate codes is turned into their identity, no current completeness or choice premise is necessitated, and no external recursion, wellorder of proposition entities, or infinite list of type qualifications occurs.

The stronger crisp-chain lemma is the only chain result needed beyond the already recorded relational canonical-chain argument. Its full wellordering against noncrisp admitted subproperties, as proved in the cited §3, is essential to §7.

## 9. Consequences using established results

The recorded [C5 and Actuality imply full Boolean Completeness](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/results/c5-and-actuality-imply-completeness.yaml) result, together with (1), gives

```math
\boxed{\text{over }C5+RC_{t,t}:\qquad
BC_t\ \longleftrightarrow\ \mathrm{Actuality}
\ \longleftrightarrow\ \text{full Boolean Completeness}}
\tag{22}
```

In particular this equivalence holds with all-type RC in the background. The reverse implication from full completeness to BC_t is its propositional instance; the implication from Actuality to full completeness is the cited existing result, not a new part of the proof here.

With all-type RC, the established C5+RC⇒TC⇒Zorn⇒WO chain supplies a current wellorder W of proposition entities. After (1), let u be a true atom. For any proposition r, u≤r holds exactly when r is currently true: the nonzero meet of the true propositions u and r must equal the atom u. Therefore

```math
W'(p,q):=(u\land W(p,q)=u)
\tag{23}
```

is crisp under C5 and currently coextensive with W. It is consequently a crisp current wellorder. This is the converse construction already checked in the preceding rigid-wellorder argument. Here the new theorem supplies its Actuality hypothesis. The separate [Zorn proof](c5-zorn-and-propositional-completeness-imply-actuality.md) establishes the corresponding implication from Zorn_t.
