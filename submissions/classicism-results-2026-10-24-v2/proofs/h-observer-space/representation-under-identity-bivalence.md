# Observer representation under local identity assumptions

Ordinary mathematical arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated.

Over H, a small local identity package turns the intrinsic meet/universal and join/existential structures into exact representations by admitted, strongly preserving observers. The two directions use different principal tests. The join test uses a second identity judgment to complement the first; no identity law for primitive negation is assumed.

## 1. Framework and qualifications

Use H in the fixed relational type system. The base types are e and t, and an arrow type is admitted only when its codomain is relational. All type lists below are finite external lists, not object-language type quantifiers. Retain the fixed abbreviations

$$
a:=\forall p^t\,p,\qquad \top:=a\lor\neg a,\qquad
\bot:=a\land\neg a.
$$
H makes Top true and Bottom false and therefore proves their distinctness. Their algebraic behavior under the primitive operations is not otherwise assumed.

For an observer E of type tt, put

$$
\begin{aligned}
A(E)&:=E\top,& Z(E)&:=\neg E\bot,\\
M(E)&:=(\lambda p,q.E(p\land q))=(\lambda p,q.Ep\land Eq),\\
V(E)&:=(\lambda p,q.E(p\lor q))=(\lambda p,q.Ep\lor Eq),\\
Q_\sigma(E)&:=(\lambda F^{\sigma t}.E(\forall x^\sigma Fx))
              =(\lambda F^{\sigma t}.\forall x^\sigma E(Fx)),\\
P_\sigma(E)&:=(\lambda F^{\sigma t}.E(\exists x^\sigma Fx))
              =(\lambda F^{\sigma t}.\exists x^\sigma E(Fx)).
\end{aligned}
$$
Write Q_Delta and P_Delta for the finite conjunctions at the listed types. Every preservation clause is an identity of the displayed whole operations. Define

$$
S[R]:=\forall p,q\,[p=q\leftrightarrow
                  \forall E\,(R(E)\to(Ep\leftrightarrow Eq))].
$$
The last biconditional compares truth values. It is not E(p iff q).

## 2. The local identity package

Assume identity bivalence at t:

$$
\mathrm{IB}_t:\quad
\forall p,q\,[(p=q)=\top\lor(p=q)=\bot].
$$
This concerns identity judgments, not every proposition. Together with H's truth clauses it says that a true identity judgment is Top and a false one is Bottom.

For admitted sigma rho, let

$$
\mathrm{Fun}_{\sigma,\rho}:\quad
\forall F,G^{\sigma\rho}
  [(\forall x^\sigma\,Fx=Gx)\to F=G].
$$
For a finite Delta, the local package L_Delta consists of IB_t and

$$
\mathrm{Fun}_{t,t},\qquad \mathrm{Fun}_{t,tt},\qquad
\{\mathrm{Fun}_{\sigma t,t}:\sigma\in\Delta\}.
$$
The first two Functionality instances lift a doubly pointwise identity to an identity between the curried binary operations. The last instances lift the quantifier identities. No unlisted Functionality instance is used.

These are local hypotheses over H. They are not claimed to be consequences of C, or to imply C. In particular C alone does not supply IB_t or unrestricted unboxed Functionality. No argument below uses Logical Equivalence, Intensionality, NI, BF, or necessitation.

## 3. Exact meet/universal representation

Say Meet_Delta holds when:

1. Primitive conjunction is commutative, associative and idempotent, and p and Top equals p. Thus it is a meet-semilattice with greatest element Top.
2. Writing u <=_meet v for u and v equals u, each listed primitive universal supplies an admitted greatest lower bound:

$$
\forall F^{\sigma t}\forall u\,
 [u\le_{\land}\forall x^\sigma Fx
  \leftrightarrow\forall x^\sigma(u\le_{\land}Fx)].
$$
**Theorem.** Over H + L_Delta,

$$
\boxed{S[A\land M\land Q_\Delta]\ \leftrightarrow\ \mathrm{Meet}_\Delta.}
$$
The right side does not require Bottom to be least.

### Separation implies the intrinsic structure

This direction needs neither IB_t nor Functionality. For the qualified class R define

$$
p\preceq q\quad\text{iff}\quad
\forall E\,[R(E)\to(Ep\to Eq)].
$$
H makes this a preorder. Separation is its antisymmetry: mutual comparison says precisely that all eligible observers agree on the two propositions. Since every eligible observer accepts Top, Top is greatest.

Evaluating the conjunction operation identity gives

$$
u\preceq(p\land q)\quad\leftrightarrow\quad
(u\preceq p\ \land\ u\preceq q).
$$
Thus primitive conjunction supplies binary meets. In particular it has the stated semilattice identities. Moreover p precedes q iff p and q equals p: in the forward direction all observers agree on p and q's meet and on p, so separation identifies them; the reverse follows by substitution and the conjunction truth clause. Hence this preorder is exactly <=_meet.

Similarly, universal preservation and ordinary H quantifier reasoning give

$$
u\preceq\forall x^\sigma Fx
\quad\leftrightarrow\quad
\forall x^\sigma(u\preceq Fx).
$$
Here one exchanges the universal quantifiers over observers and x after distributing implication over the universal whose variable is absent from Eu. This is a truth-level derivation in H, not a functional-identity inference. It proves the required GLB law in the identified order.

### Principal observers give the converse

Assume Meet_Delta. For each a:t take the admitted term

$$
E_a(p):=(a\land p=a).
$$
IB_t gives endpoint-valued outputs, and E_a(p) is true exactly when a <=_meet p. Since a and Top equals a, E_a(Top)=Top; in particular A(E_a).

The semilattice law gives

$$
E_a(p\land q)\ \leftrightarrow\ E_a(p)\land E_a(q).
$$
Both sides are endpoint propositions. Indeed Top is greatest, so Bottom <=_meet Top whether or not Bottom is least in the entire algebra. The set {Bottom,Top} therefore has the usual two-element meet table. Equality follows from truth agreement between endpoints:

$$
E_a(p\land q)=E_a(p)\land E_a(q).
$$
For a listed sigma, the GLB law gives the material equivalence

$$
E_a(\forall x^\sigma Fx)\ \leftrightarrow\
\forall x^\sigma E_a(Fx).
$$
The right side is also an endpoint. If every E_a(Fx) is Top, its GLB is Top. Otherwise some value is Bottom; the family then consists only of Top and Bottom and has GLB Bottom. This uses Bottom <=_meet Top, not global leastness of Bottom. The left side is an endpoint by IB_t, so again truth agreement gives the pointwise identity.

Now apply Fun_(t,t) to the inner q-abstractions and Fun_(t,tt) to their p-abstractions to obtain M(E_a). Apply Fun_(sigma t,t) to obtain each full Q_sigma(E_a). These are the only pointwise-to-operation upgrades.

Finally, suppose every qualified observer agrees on p,q. The test E_p gives p <=_meet q, since E_p(p) is true. The test E_q gives q <=_meet p. Antisymmetry yields p=q. The forward equality-to-agreement implication is H substitution. Thus the principal tests prove the separation principle.

## 4. Exact join/existential representation

Say Join_Delta holds when:

1. Primitive disjunction is commutative, associative and idempotent, and p or Bottom equals p. Thus it is a join-semilattice with least element Bottom.
2. Writing u <=_join v for u or v equals v, each listed primitive existential supplies an admitted least upper bound:

$$
\forall F^{\sigma t}\forall u\,
 [(\exists x^\sigma Fx)\le_{\lor}u
  \leftrightarrow\forall x^\sigma(Fx\le_{\lor}u)].
$$
**Theorem.** Over H + L_Delta,

$$
\boxed{S[Z\land V\land P_\Delta]\ \leftrightarrow\ \mathrm{Join}_\Delta.}
$$
Top need not be greatest. There is no assumption identifying primitive negation with endpoint complement.

### Separation implies the intrinsic structure

Use the same observer preorder. Rejection of Bottom makes Bottom least. Disjunction preservation gives

$$
(p\lor q)\preceq u\quad\leftrightarrow\quad
(p\preceq u\ \land\ q\preceq u),
$$
so disjunction supplies binary joins. Separation identifies the preorder with <=_join and gives the join-semilattice and Bottom-unit identities. Existential preservation gives

$$
(\exists x^\sigma Fx)\preceq u
\quad\leftrightarrow\quad\forall x^\sigma(Fx\preceq u).
$$
For each observer this uses the H equivalence between an implication with existential antecedent and the universal family of implications, with x absent from Eu. Exchanging the universal observer and object quantifiers proves the displayed law. Again this forward direction requires no local identity package.

### The dual principal test uses equality twice

Assume Join_Delta. Define

$$
D_a(p):=((p\lor a=a)=\bot).
$$
The inner judgment is Top exactly when p <=_join a and Bottom otherwise. IB_t also applies to the outer identity judgment. Since Top and Bottom are distinct,

$$
D_a(p)=\top\quad\text{iff}\quad p\not\le_{\lor}a,
$$
and its other value is Bottom. This constructs endpoint complementation without applying primitive negation to the inner identity proposition. Since Bottom <=_join a, D_a(Bottom)=Bottom, so Z(D_a).

A join is below a exactly when both arguments are below a. Classical truth reasoning therefore gives

$$
D_a(p\lor q)\ \leftrightarrow\ D_a(p)\lor D_a(q).
$$
Both sides are endpoints: Bottom is least and hence Bottom <=_join Top, so the two endpoints have the usual two-element join table. Truth agreement yields identity.

Likewise the LUB law gives

$$
D_a(\exists x^\sigma Fx)\ \leftrightarrow\
\exists x^\sigma D_a(Fx).
$$
The primitive existential on the right is an endpoint because it is the LUB of an endpoint family: Bottom if every value is Bottom, and Top otherwise. This does not require Top to be greatest in the whole algebra. The left side is an endpoint by IB_t, so the pointwise identity follows. The same local Functionality instances used in §3 now give full V(D_a) and P_sigma(D_a).

If p and q are distinct, antisymmetry says either p is not below q or q is not below p. In the first case D_q(p) is true and D_q(q) false; in the second D_p(q) is true and D_p(p) false. Hence these admitted principal tests separate.

## 5. Adding the other endpoint condition

The two exact refinements are:

$$
\begin{aligned}
S[A\land Z\land M\land Q_\Delta]
&\leftrightarrow\mathrm{Meet}_\Delta
  +\forall p\,(p\land\bot=\bot),\\
S[A\land Z\land V\land P_\Delta]
&\leftrightarrow\mathrm{Join}_\Delta
  +\forall p\,(p\lor\top=\top).
\end{aligned}
$$
Both are over H + L_Delta. In the forward meet direction, Z makes Bottom least in the observer order. In the forward join direction, A makes Top greatest.

For the converse meet direction retain only principal E_a with a different from Bottom. When Bottom is least, E_a(Bottom)=Bottom for every such a, so these tests satisfy both endpoint conditions. They still separate: if p is not below q, then p is not Bottom and E_p distinguishes; use E_q in the other case.

Dually, retain only D_a with a different from Top. When Top is greatest, D_a(Top)=Top. If p is not below q, then q is not Top and D_q distinguishes; use D_p in the other case. Thus acceptance on the join branch adds exactly greatestness of the fixed Top.

In every converse construction the witnesses actually fix the required endpoints, not merely their truth values. Accordingly the same equivalences hold if A is replaced by E(Top)=Top and/or Z by E(Bottom)=Bottom wherever those clauses occur. The forward implications still follow because fixing gives the corresponding truth condition.

## 6. Scope and a small H model

The converse theorems use two explicit resources: identity judgments supply an admitted endpoint-valued principal truth test, and local Functionality lifts its pointwise preservation to the requested whole-operation identities. They neither assume every external order homomorphism is admitted nor identify a truth-preserving map with an existing operation automatically.

The results concern one semilattice operation and its matching quantifiers. They do not assert that the same principal tests preserve both primitive conjunction and primitive disjunction, or both types of indexed bound. Such mixed preservation is an additional condition.

To see directly that the local assumptions and the meet representation do not imply C, use the full-function H construction with proposition domain {0,1} squared, truth in the first coordinate, singleton individuals, and every admitted function space full. Use coordinatewise conjunction, negation and both quantifiers. Interpret equality at every type as (delta,delta), where delta is identity. Interpret primitive disjunction as

$$
(b,c)\lor(d,e)=(b\lor d,\ c\mathbin{\mathrm{XOR}}e).
$$
All primitives have their ordinary first-coordinate truth conditions, so H is sound; beta/eta and all Functionality instances hold for the full function spaces. The fixed abbreviations give Top=(1,1) and Bottom=(0,0), and IB_t holds. Coordinatewise conjunction and universal quantification satisfy Meet_Delta for every finite Delta. Thus the meet theorem applies. But p or p differs from p at p=(0,1), refuting an instance of Logical Equivalence. The unlisted connective remains unconstrained.

## 7. Sources and scope

The proofs and the local formulation in this note are original mathematical deductions, direct source `misc`, OpenAI Codex, 24 October 2026, §§1–6, unpaginated. The H framework, type convention, fixed abbreviations, and distinctions among identity principles are in [the topic background](../../source/topics/classicism/background.md), Framework and Notation, with the source locators retained there.

The forward observer-order calculations specialize [Conjunction and quantifier separation over H](../meet-quantifier-separation.md), §§2–3, and the disjunction analysis in [The observer-separation lattice](../observer-lattice.md), §2. The full-function H recipe and the corrupted primitive disjunction appear in that latter note, §7. The new converse constructions and their explicit local Functionality requirements are proved here rather than attributed to an external source.
