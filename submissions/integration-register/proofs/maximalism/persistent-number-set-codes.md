# Persistent propositions representing the admitted number sets

26 October 2026. Ordinary mathematical research by OpenAI Codex. Direct source: `misc`, §§1–4 below, unpaginated. The argument received independent AI mathematical review; no human review or formal certification is claimed.

**Over C, pure Maximalism and propositional Boolean Completeness provide a Boolean copy of every admitted current number set in which every element, including every complement relative to the copy's unit, satisfies the full identity p = Box p.** The copy preserves existing joins. An admitted operation carries the previously constructed number-set codes to these persistent codes.

No observer separation, Choice, Zorn, BF, or boxed version of either optional premise is required. The result concerns the admitted number sets, not an internal full power set, and the atoms of this relative algebra need not be atoms of the whole proposition algebra.

## 1 Persistently finite possibilities

Use the notation of [Number sets encoded by propositions](../dependencies/number-set-codes-in-complete-maximalism.md), §§1–4:

```math
\nu=(et)t,\qquad N=\mathrm{FiniteCardinality}_e,
\qquad a_n=(\mathrm{Suc}_e n)(\lambda x^e.\top).
```

The current members of N are the numbers in this argument. Define

```math
\Psi:=\forall n^\nu\,(Nn\to\Diamond\Box a_n).
\tag{1}
```

The [coalesced model with all finite individual domains](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/coalesced-all-finite-individual-domains.md) satisfies Psi. Its current numbers are the standard numeral values, and the leaf with k+1 individuals makes a_k true. At that leaf Box is the identity, so Box a_k is true as well. This verifies C-consistency of the pure sentence Psi. Pure Max(C), with C unchanged as its reference theory, therefore gives Diamond Psi.

C proves Diamond Psi implies Psi. Indeed, fix a current Nn. The established C theorem Nn implies Box Nn carries this same number to a possible Psi evaluation. There Diamond Box a_n holds, so Diamond Diamond Box a_n holds currently. Modal 4 reduces this to Diamond Box a_n. Generalizing n proves the implication. Consequently pure Max(C) implies Psi.

Put d_n := Box a_n. For every current number n, Psi makes d_n nonzero. S4 gives the proposition identity Box d_n = d_n, and T gives d_n ≤ a_n. Moreover Psi implies the earlier sentence Pi := forall n(Nn implies Diamond a_n). The established exclusivity argument under Pi makes distinct current a_n disjoint. Hence the d_n are also pairwise disjoint.

## 2 A persistent relative unit

Let B be the current Boolean algebra of propositions. BC_t gives the actual algebraic joins

```math
b:=\bigvee_{n\in N}a_n,
\qquad d:=\bigvee_{n\in N}d_n.
\tag{2}
```

These are joins of admitted properties: for example the second property is lambda p.exists n(Nn and p = Box a_n). They are not merely current material existential disjunctions. Since d_n ≤ a_n for each current n, d ≤ b; also d is nonzero.

Every existing join of Box-fixed propositions is Box-fixed. If z is such a join and p is one of its summands, monotonicity gives p = Box p ≤ Box z. Thus Box z is an upper bound, and leastness gives z ≤ Box z. T supplies the converse inequality. In particular,

```math
d=\Box d.
\tag{3}
```

This is full proposition identity. The argument requires neither persistence of the join assertion nor boxed BC_t.

## 3 The admitted embedding

The previous coding theorem identifies the algebra of number-set codes as

```math
D=\{c\le b:\forall n\in N\,
      (a_n\le c\ \lor\ a_n\land c=\bot)\}.
\tag{4}
```

It is a Boolean algebra with relative unit b. Every nonzero member contains some a_n. Its elements represent exactly the current subsets of N that are extensions of admitted predicates. Its existing joins are actual B-joins.

Define the admitted operation

```math
J:=\lambda c^t.(d\land c).
\tag{5}
```

Finite meet distributes over every existing Boolean join. Since each c in D includes or excludes every a_n, equations (2) and (4) yield

```math
J(c)=\bigvee\{d_n:n\in N\text{ and }a_n\le c\}.
\tag{6}
```

Every summand on the right is Box-fixed, so §2 proves

```math
J(c)=\Box J(c)\qquad(c\in D).
\tag{7}
```

This is full identity for each current code input. NI therefore preserves each established identity. Equation (7) does not assert that J and lambda c.Box J(c) are identical operations on all propositions.

The map J preserves Bottom, meets and finite joins, and sends b to d. Its relative-complement law is

```math
J(b\land\neg c)=d\land\neg c
                =d\land\neg J(c).
\tag{8}
```

Thus its image is a Boolean algebra with relative unit d. In particular its relative complements also satisfy (7).

For injectivity, suppose c and e are distinct members of D. Their symmetric difference is a nonzero code, so it contains some a_n. Then

```math
\bot<d_n\le d\land(c\mathbin{\triangle}e)
                  =J(c)\mathbin{\triangle}J(e),
```

and J(c) differs from J(e). Hence J restricts to a Boolean isomorphism from D onto its image. No admitted inverse operation or admitted uniform code-selection operation is asserted.

## 4 Preservation of existing joins and exact scope

Suppose a family of members of D has an existing join s in D. The earlier coding theorem makes s its actual B-join. Therefore

```math
J(s)=d\land s=\bigvee_c(d\land c)=\bigvee_c J(c).
\tag{9}
```

The right-hand join is an actual B-join. This applies to every family whose join exists in D, and in particular to all admitted families covered by BC_t. Relative complementation also gives preservation of existing relative meets; the empty meet is b in D and d in the image.

Combining the previous number-set representation with J proves the stated persistent representation of every admitted current number set. Existing unions are preserved. This does not assert external completeness, global Atomicity, or that all propositions are necessary. The exact premises are C + pure Max(C) + BC_t. Equivalently, the representation argument itself works over C + Psi + BC_t; Max(C) supplies Psi by §1.
