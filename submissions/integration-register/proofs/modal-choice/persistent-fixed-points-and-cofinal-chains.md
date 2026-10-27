# Persistent fixed points and cofinal chains

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

Write O(p) for p=□p and O⁻(p) for O(p) and p≠1. Order is algebraic
Boolean order. Every proper persistent proposition is currently false:
if p=□p and p is true, then □p is true, which means p=1. Conversely,
every false persistent proposition is proper. Finite joins of persistent
propositions are persistent, and finite joins of proper persistent
propositions remain proper. These are current statements justified by
the unconditional S4 laws of C and ordinary material reasoning.

The two conclusions are:

1. Already over C, an admitted operation that preserves O⁻ and is
   inflationary there has a fixed point in O⁻.
2. Over either C+BC_t+RC_(t,t) or C+BC_t+Zorn_t, Actuality is equivalent
   to the existence of an admitted chain cofinal in O⁻.

In particular, each choice package implies Actuality if the persistent propositions form a chain under entailment: between any two, one entails the other. Equivalently,

```math
\forall p^t q^t\, .\,(\Box p\le\Box q\lor\Box q\le\Box p)
```
 The unrestricted bare-C implications remain unresolved.

## 1. A direct fixed-point lemma over bare C

**Lemma.** Let f:tt be admitted. Suppose, currently, for every p∈O⁻,

```math
f(p)\in O^-,\qquad p\le f(p)
\tag{1}
```

Then there is r∈O⁻ with f(r)=r. Monotonicity, Boolean completeness,
choice, BF, and ND are not premises.

Define admitted terms

```math
u(x):=f(\Box x)\land\neg\Box x,\qquad
B:=\exists x^t\,u(x),\qquad r:=\Box B
\tag{2}
```

For every current x, □x is persistent. If □x=1, u(x)=0. Otherwise
□x∈O⁻, so f(□x) is a proper persistent proposition and is false.
Thus every u(x) is false. Material existential truth makes B false;
consequently r is a proper persistent proposition.

Unconditional existential introduction in C gives u(r)≤B. Also r≤B
by T and □r=r by persistence. Apply (1) to r. Boolean algebra gives

```math
f(r)=r\lor(f(r)\land\neg r)=r\lor u(r)\le B
```

Since f(r) is persistent, algebraic monotonicity of □ gives

```math
f(r)=\Box f(r)\le\Box B=r
```

Together with r≤f(r), this proves f(r)=r. In particular, there is no
admitted operation strictly increasing every member of O⁻ while
remaining in O⁻.

The proof has not identified a material existential with an algebraic
join. It uses only the individual inequalities u(x)≤B. No equivalence
derived from (1) is submitted to Logical Equivalence.

## 2. A useful successor-graph criterion

Assume BC_t and ¬Vicinity. By the existing characterization of
Vicinity, O⁻ has no greatest member and has actual Boolean supremum 1.
Every represented family of persistent propositions has a persistent
join: if j is its Boolean join, then □j is also an upper bound, so
j≤□j≤j. Thus O, with its inherited order, has suprema of all represented
chains and has least member 0.

Suppose there are an admitted chain D⊆O⁻ cofinal in O⁻ and an admitted
current functional graph F on O such that

```math
F(1)=1,\qquad p<F(p)\in D\quad(p\in O^-)
\tag{3}
```

Function notation here and below abbreviates the unique current graph
value. No operation representing F is asserted.

Apply the existing represented canonical-chain lemma to the graph
F² on O. Composition is admitted by existentially quantifying the
intermediate value. We obtain an admitted internally wellordered
chain C, closed under F², with conformity

```math
c=\sup\{F^2(e):e\in C,\ e<c\}\quad(c\in C)
\tag{4}
```

The supremum is in O and is also the Boolean supremum, since Boolean
joins of persistent families are persistent. The chain terminates at
a fixed point of F². By (3), this point is 1. For c<e in C, (4) gives
F²(c)≤e. Also F²(c) is proper whenever c is proper. Conformity at 1
therefore proves

```math
\sup(C\setminus\{1\})=1
\tag{5}
```

Every member c of C is comparable with every d of D. Indeed, the
family in (4) consists of D-members. If all those members are ≤d,
then c≤d. Otherwise some member is >d, since D is a chain, and hence
d<c. This argument also covers c=0 with its empty defining family.

It follows that C\{1} is cofinal in O⁻. For p∈O⁻, choose d∈D with
p≤d. By (5) there is c∈C\{1} with c not≤d. Comparability gives d<c,
and therefore p<c.

## 3. Two Boolean colors give the contradiction

For every c∈C\{1}, define the two positive bands through their admitted
graphs:

```math
A_c:=F(c)\land\neg c,\qquad
B_c:=F^2(c)\land\neg F(c)
\tag{6}
```

Both are nonzero by (3). Bands from distinct stages are disjoint,
because c<e implies F²(c)≤e; the two bands at one stage are disjoint
as well. BC_t supplies the scalar Boolean join

```math
b:=\sup\{A_c:c\in C,\ c\ne1\}
\tag{7}
```

The family in (7) is an admitted predicate: use existential witnesses
for c, F(c), and F²(c) in the graph formulas. All A_c≤b, and all
B_c≤¬b because each B_c is disjoint from every A-band.

Define the admitted operation

```math
h_b(p):=\Box(p\lor b)\lor\Box(p\lor\neg b)
\tag{8}
```

It is inflationary on O and takes persistent values. It also maps
O⁻ into O⁻. To check the latter, take p∈O⁻ and a proper c∈C with
p≤c, using §2. The positive A_c and B_c are disjoint from p. Since
A_c≤b and B_c≤¬b, neither b≤p nor ¬b≤p. Thus neither p∨b nor p∨¬b
equals 1. Both boxes in (8) are therefore false, making h_b(p) a
proper persistent proposition.

Lemma 1 now supplies a proper persistent fixed point p of h_b. But
no such fixed point exists. The admitted subproperty

```math
\{c\in C:c\not\le p\}
```

is nonempty because it contains 1. Let c be its least member. Every
e∈C below c satisfies e≤p. For such e,

```math
F(e)=e\lor A_e\le p\lor b
```

Persistence of F(e) gives

```math
F(e)\le\Box(p\lor b)\le h_b(p)=p
```

Similarly,

```math
F^2(e)=F(e)\lor B_e\le p\lor\neg b,
\qquad
F^2(e)\le\Box(p\lor\neg b)\le p
```

Conformity (4) yields c≤p, a contradiction. This proves that the
data of §2 cannot coexist with ¬Vicinity.

Full current wellordering is sufficient for the least-counterexample
argument. Neither the chain predicate nor its predecessor predicates
have been assumed crisp, persistent, or necessarily wellordered.

## 4. The Relational Choice theorem

**Theorem.** Over C+BC_t+RC_(t,t), the following are equivalent:

```math
\mathrm{Actuality};\qquad
\mathrm{Vicinity};\qquad
O^{-}\text{ has an admitted cofinal chain}
\tag{9}
```

The first two are equivalent by the existing Vicinity theorem. If
Vicinity holds, the greatest proper persistent member supplies a
singleton cofinal chain.

Conversely, suppose D⊆O⁻ is an admitted cofinal chain and Vicinity
fails. Every p∈O⁻ has a strictly larger member in O⁻. To see this,
choose r∈O⁻ not≤p and take p∨r, which is still proper persistent.
Cofinality of D then gives d∈D strictly above p.

Define a serial relation on all propositions whose permitted outputs
at p∈O⁻ are precisely the d∈D with p<d, and whose sole permitted
output at all other p is 1. This definition uses current material
cases; no crispness is claimed. RC_(t,t) supplies a functional
subrelation. Restrict it to O, obtaining exactly the graph (3).
Sections 2–3 contradict ¬Vicinity. Hence Vicinity and Actuality hold.

Only the single instance RC_(t,t) is used, once. No RC with predicate
inputs or outputs, higher-type completeness, or OS is required.

## 5. The Zorn theorem

**Theorem.** Equivalence (9) also holds over C+BC_t+Zorn_t.

Again, only the cofinal-chain-to-Vicinity direction is new. Suppose
D⊆O⁻ is an admitted cofinal chain and Vicinity fails. Its supremum
is 1. The complement-image family

```math
E:=\{\neg d:d\in D\}
```

is an admitted positive Boolean chain with infimum 0. Apply the
existing one-proposition annulus-history refinement theorem, which
uses only BC_t+Zorn_t: E has an admitted reverse-wellordered coinitial
subchain L. The complement image K of L is an admitted internally
wellordered subchain of D cofinal in D and hence in O⁻. The admitted
subproperty version of wellordering transfers along complement by
pulling back each tested subproperty.

For every p∈O⁻, the property {k∈K:p<k} is nonempty, because O⁻ has
no greatest member and K is cofinal. Define F(p) to be its least
member, and set F(1)=1. This is an admitted current functional graph,
specified by its least-member formula, without using RC or extracting
an operation. It satisfies (3), with K as D. Sections 2–3 give the
contradiction.

The annulus refinement applies to any admitted positive chain with
infimum 0. Its applicability here does not depend on the other
note's later C5-specific Actuality argument.

## 6. Consequences and remaining scope

If O is linearly ordered, O⁻ itself is an admitted cofinal chain.
Thus either C+BC_t+RC_(t,t) or C+BC_t+Zorn_t, together with this
linearity assumption, implies Actuality. Under either package,
failure of Actuality forces O⁻ to have no admitted cofinal chain.

There is also a choice-free intermediate statement: under C+BC_t,
an admitted internally wellordered cofinal chain in O⁻ implies
Vicinity. Under ¬Vicinity its least strict-successor graph is defined
exactly as in §5, and §§2–3 contradict it. Actuality is not inferred
from this intermediate statement without an additional hypothesis.

The unrestricted gap remains precise. The canonical chain from a
general increasing graph on O is unbounded below 1, but need not be
cofinal in O⁻. An arbitrary proper persistent p can be incomparable
with its members. Without a cofinal chain, one cannot conclude that
(8) preserves properness, so Lemma 1 does not supply the prohibited
proper fixed point. This proof does not derive a cofinal chain from
either choice principle alone.

## Sources

- The new fixed-point diagonal and the cofinal-chain implications:
  this note, §§1–6, OpenAI Codex, 26 October 2026, `misc`, unpaginated.
- Vicinity iff O has a greatest proper member; the established
  RC_(t,t)+BC_t+Vicinity implication: [the supported-interpretation
  theorem](../../../next-update/proofs/vicinity-relational-choice-and-propositional-completeness-imply-actuality.md),
  §§1–3, unpaginated. The Zorn counterpart is linked below.
- Represented canonical chains: [Relational Choice and Boolean
  Completeness imply Actuality](../../../../logical-maps/topics/classicism/writeups/relational-choice-and-boolean-completeness-imply-actuality.md),
  Appendix D, unpaginated.
- The BC_t+Zorn_t coinitial-refinement theorem: [Zorn and propositional
  completeness imply Actuality](../../../next-update/proofs/c5-zorn-and-propositional-completeness-imply-actuality.md),
  §§3–4, especially (11), unpaginated. A restatement appears in
  [the bare-C higher-completeness proof](../../../next-update/proofs/zorn-and-higher-completeness-imply-actuality.md),
  §3, unpaginated.
