# Finite semilattices collapse the material and pointwise observer tiers

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated. The base is H in the fixed relational type system. No C, NI, BF, Choice or Functionality is assumed unless explicitly stated.

## 1. Statements and scope

Use the observer qualifications and separation tiers of [Local separation tiers](local-tiers-and-models.md), §3. In particular,

```math
M_{\rm mat}(E):\quad\forall p,q\,[E(p\land q)\leftrightarrow(Ep\land Eq)],
```

```math
M_{\rm pt}(E):\quad\forall p,q\,[E(p\land q)=Ep\land Eq]
```

The qualifications V_mat and V_pt are the analogous disjunction laws. A(E) means ETop is true, and Z(E) means EBottom is false. An optional orientation O is any of no condition, A, Z or A∧Z. Sep_t is propositional separation; FullSep is separation at every relational type.

Let All:=λp.Top and let Fin_t(All) be internal Frege finiteness, as defined in §2. Then, for every such O,

```math
\boxed{\mathrm H+\mathrm{Fin}_t(\mathrm{All})\ \vdash\
\mathrm{Sep}_t[O\land M_{\rm mat}]
\leftrightarrow\mathrm{Sep}_t[O\land M_{\rm pt}]}
\tag{1}
```

The same equivalence holds with V in place of M, and at full typed scope. At full typed scope the whole-operation tier is equivalent to these two tiers as well. At propositional scope, passing to the whole-operation tier requires the local Functionality instances specified in §6.

The normalization uses a least true proposition in the meet order, or a greatest false proposition in the join order. Those extrema suffice even without internal finiteness. The two output values need not be the fixed abbreviations Top and Bottom.

## 2. Internal finite induction for closed sets

The [background definition](../../source/topics/classicism/background.md) is

```math
\mathbf0:=\lambda U.\forall x\neg Ux,
\qquad
\mathrm{Suc}(Z):=\lambda U.\exists y\,[Uy\land Z(\lambda x.Ux\land x\ne y)],
```

```math
\mathrm{FiniteCardinality}_t(Z):=
\forall W\,[(W\mathbf0\land\forall Y(WY\to W(\mathrm{Suc}(Y))))\to WZ],
```

```math
\mathrm{Fin}_t(\mathrm{All}):=
\exists Z^{(tt)t}\,[\mathrm{FiniteCardinality}_t(Z)\land Z(\mathrm{All})]
```

All these types are admitted. Internal finiteness neither supplies a standard external enumeration nor says that its cardinality witness is a standard numeral.

**Finite-closure lemma.** Suppose an admitted operation m makes the proposition domain a meet semilattice, with x≤y abbreviating m(x,y)=x. Under Fin_t(All), every admitted nonempty predicate C closed under m has a least member.

**Proof.** Fix C. Comprehend the following property of cardinality objects:

```math
W(Z):=\forall U\left[ZU\to
\left((\exists x\,[Ux\land Cx])\to
\exists b\left[Cb\land
\forall x\,((Ux\land Cx)\to b\le x)\right]\right)\right]
\tag{2}
```

At cardinality zero, U has no members, so the antecedent asserting a member of U∩C is false. Thus W(0).

For the successor, assume W(Z) and Suc(Z)U. Eliminate the latter existential to obtain y with Uy and Z(V), where V is the exact deletion term λx.Ux∧x≠y. Suppose U∩C is nonempty.

If V∩C is empty, every member of U∩C equals y. Nonemptiness therefore gives Cy, and y itself is the required lower bound in C.

If V∩C is nonempty, W(Z) supplies b∈C below all its members. When Cy is false, every member of U∩C belongs to V∩C, so b suffices. When Cy is true, use m(b,y). It belongs to C by closure, lies below y, and lies below every member of V∩C by the semilattice equations. It is therefore below every member of U∩C. This proves W(Suc(Z)).

Frege induction gives W(Z) at the witness to Fin_t(All). Apply it to All. Since C is nonempty, the result is a member of C below every member of C, hence its least member. ∎

The proof uses single existential witnesses in an induction step, not a choice function. The induction predicate is an admitted lambda term with C and m as parameters. No extensionality of predicates or cardinality objects is used, and no transfer from internal finiteness to external finiteness occurs. The exact successor deletion term avoids a separate finite-subset closure lemma.

For a join semilattice, apply the same argument with its order reversed: every admitted nonempty join-closed predicate has a greatest member. This is also proved directly by replacing the lower bound b and m(b,y) above by an upper bound b and b∨y.

## 3. Least truth gives an explicit meet normalization

Assume conjunction satisfies its associativity, commutativity and idempotence identities. Suppose u is true and least among the true propositions in its meet order:

```math
u,\qquad\forall p\,[p\to u\land p=u]
\tag{3}
```

Put

```math
d:=u\land\neg u,
\qquad n(p):=u\land\neg(u\land p),
\qquad\chi(p):=n(n(p))
\tag{4}
```

Here u is true, d is false, and d≤u. All operations in (4) are explicitly admitted terms.

If p is true, (3) gives u∧p=u, so n(p)=d. If p is false, u∧p is false, hence ¬(u∧p) is true; (3) then gives n(p)=u. Applying this calculation twice gives the identities

```math
p\ \Longrightarrow\ \chi(p)=u,
\qquad
\neg p\ \Longrightarrow\ \chi(p)=d
\tag{5}
```

Thus χ preserves current truth, takes exactly the two values u,d, and fixes both. In particular χ(χ(p))=χ(p). These are output identities, not just a claim about χ's truth profile.

Given any materially meet-preserving observer E, define

```math
E'(p):=\chi(Ep)
\tag{6}
```

Its truth profile is exactly E's. The two values u,d form a two-element meet chain, with u∧u=u, u∧d=d∧u=d and d∧d=d. Therefore the material M law for E and (5) imply, in all four truth cases for Ep and Eq,

```math
E'(p\land q)=E'p\land E'q
\tag{7}
```

Hence E' satisfies M_pt. Any A or Z condition on E survives, since E' has the same truth at every input. No equation identifying u with Top or d with Bottom is claimed; endpoint fixing is a different restriction.

This proves the stronger local assertion: under the semilattice equations and (3), **every admitted material meet character has an admitted pointwise meet character with the same truth profile**. In particular, composing χ with the principal tests λp.(a∧p=a) gives explicit pointwise meet separators.

## 4. Greatest falsity gives the dual join normalization

Assume disjunction satisfies the join-semilattice equations. Let v be false and greatest among the false propositions in its join order:

```math
\neg v,\qquad\forall p\,[\neg p\to v\lor p=v]
\tag{8}
```

Put

```math
u:=v\lor\neg v,
\qquad n(p):=v\lor\neg(v\lor p),
\qquad\chi(p):=n(n(p))
\tag{9}
```

Then v is false, u is true and v≤u in the join order. If p is false, v∨p=v and n(p)=u. If p is true, v∨p is true and its negation is false, so (8) gives n(p)=v. Thus χ(p)=u when p is true and χ(p)=v when p is false.

The pair v,u is a two-element join chain. Consequently E':=χ∘E turns every materially join-preserving observer E into a pointwise join-preserving observer with exactly the same truth profile. Its A/Z qualifications survive. This is the dual local theorem, again without identifying the pair with the fixed endpoints.

## 5. Finite collapse of separation

Suppose Sep_t[O∧M_mat]. This implies bare material M separation, since its qualified observer class is smaller. The [truth-profile theorem](truth-profiles-and-connective-reducts.md), §6, therefore gives the conjunction semilattice equations.

The admitted predicate C(p):=p is nonempty, since Top is true, and is meet-closed by H's truth conditions. The finite-closure lemma supplies a least true u, so §3 applies. To prove Sep_t[O∧M_pt], assume all its qualified observers agree on p,q. For any O∧M_mat observer E, the normalized E' satisfies O∧M_pt and has E's truth profile. Thus E agrees on p,q. Material separation gives p=q. The forward equality-to-agreement implication is H substitution.

Conversely, M_pt implies M_mat by identity substitution and the H truth table. Pointwise separation therefore implies material separation without any finiteness assumption. This proves (1).

For V, use the admitted predicate C(p):=¬p. It is nonempty because Bottom is false, and join-closed by the H truth table. Section 2 gives a greatest false v; §4 supplies the normalized witnesses. The rest of the proof is identical.

The argument transfers every observer's entire truth profile. It therefore proves the same equivalence for separation at any fixed relational type once the propositional semilattice equations are available, and in particular for FullSep. At full typed scope those equations come from the included propositional separation instance.

## 6. Whole-operation preservation and exact algebraic forms

At propositional scope, (7) alone does not identify its two abstracted operations. Assume the local Functionality instances at t,t and t,tt. First apply Functionality at t,t, for each fixed p, to the two q-operations in (7). Then apply Functionality at t,tt to the resulting p-operations. This yields

```math
(\lambda p,q.E'(p\land q))
=(\lambda p,q.E'p\land E'q)
```

The same argument applies to V. Hence internal finiteness plus these two local Functionality instances collapses all three propositional separation tiers for M or V, with any of the four A/Z orientations.

At full typed scope, [FullSep is propositional separation plus Functionality](typed-separation-and-classicism.md), §2. The local Functionality instances are consequently already available, giving equivalence of material, pointwise and whole-operation full typed separation under Fin_t(All).

Combining (1) with the material characterization gives explicit algebraic equivalences under internal finiteness:

| Qualification | Exact condition for propositional material or pointwise separation |
|---|---|
| M | Conjunction is a meet semilattice |
| A∧M | That semilattice has greatest element Top |
| Z∧M | That semilattice has least element Bottom |
| A∧Z∧M | Both specified bounds |
| V | Disjunction is a join semilattice |
| A∧V | That semilattice has greatest element Top |
| Z∧V | That semilattice has least element Bottom |
| A∧Z∧V | Both specified bounds |

For full typed separation, append all Functionality instances to the right column. With the local binary Functionality package, the propositional table also applies to whole-operation preservation. The table concerns the separate M and V branches; it makes no assertion about their joint preservation.

## 7. Consequence for the unresolved comparison

A material-versus-pointwise M countermodel over H cannot have an externally finite proposition domain. More generally, its conjunction truth filter cannot have a least member. The dual V countermodel would require the false join ideal to have no greatest member. By the internal proof above, neither countermodel can satisfy Fin_t(All).

This does not settle the general infinite comparison. It also does not identify pointwise and whole-operation propositional separation without Functionality: the finite hidden-proposition model in [Local separation tiers](local-tiers-and-models.md), §3, still separates those two tiers.

The result strengthens the [identity-bivalence representation](representation-under-identity-bivalence.md), §§2–3, in a different direction: here no bivalence condition is imposed on equality judgments, and the two output representatives are constructed from a local extremum of truth or falsity. Internal finiteness guarantees that extremum without assuming C or a uniform choice principle.
