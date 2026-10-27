# Parameter noncontingency under entailment order symmetries

Ordinary mathematical research by OpenAI Codex, 25 October 2026. Direct source for the connecting arguments: `misc`, this note, §§1–5, unpaginated. Exact background throughout: C5, meaning C plus all-type boxed Necessity of Distinctness in the fixed relational language.

The original first-order endpoint-parameter schema does not characterize reversible logical separation. A higher-parameter variant does: pure statements about endpoint families of propositions invariant under every admitted automorphism of the entailment order are noncontingent. The parameter restriction needs neither a logical quantifier-preservation clause nor an explicitly supplied inverse. Those conditions follow from the order-automorphism condition over C5.

## 1 The original and revised parameter scopes

The original schema universally closes

```math
\mathrm{End}(\bar R)\to
\bigl(P(\bar R,\bar x)\leftrightarrow\Box P(\bar R,\bar x)\bigr)
\tag{1}
```

Here P is pure, its only free variables are individuals and first-order relations R_i:e^{n_i}t with n_i at least one, and every value of each R_i is Top or Bottom. Bound variables may have any admitted type. The [countermodel](../../../next-update/proofs/fixed-individual-component-shift.md) satisfies every boxed instance of (1) and necessary left-inverse separation, even with infinitely many fixed individuals, while Rev fails.

The revised schema admits a parameter X:tt representing a family of propositions, subject to the following entirely internal conditions. Write 0 and 1 for Bottom and Top, and define the algebraic entailment order by p≤q iff p∧q=p. This order is not current material implication. Put

```math
\begin{aligned}
\mathrm{Aut}_{\le}(E)
 &:=(\forall q^t\exists p^t\,Ep=q)
 \land\forall p^t q^t\,(p\le q\leftrightarrow Ep\le Eq),\\
\mathrm{Stable}(X)
 &:=(\forall p^t\,(Xp=0\lor Xp=1))\\
 &\quad\land\forall E^{tt}\Bigl(
 \mathrm{Aut}_{\le}(E)\to
 \forall p^t\,X(Ep)=Xp\Bigr)
\end{aligned}
\tag{2}
```

Every quantified operation is admitted. No external automorphism is silently included. The proposed schema is

```math
\forall X^{tt}\Bigl(
\mathrm{Stable}(X)\to
(P(X)\leftrightarrow\Box P(X))\Bigr),
\tag{3}
```

for each pure formula P whose only free variable is X. Arbitrary higher-type bound variables remain allowed. Types and formulas are external schema indices, not object-language variables.

**Theorem.** Over C5, schema (3) is equivalent to full Rev. In fact the one instance

```math
\forall X^{tt}\Bigl(
\mathrm{Stable}(X)\to
(J(X)\leftrightarrow\Box J(X))\Bigr),
\qquad J(X):=\exists p^t(Xp\land p),
\tag{4}
```

already suffices. Consequently (3) is a strict strengthening of (1) over C5. This gives an order-theoretic restriction on parameters; it is not a characterization avoiding symmetry altogether.

## 2 Barcan makes admitted quantifiers order bounds

For every admitted H:σt, C5 proves

```math
b\le\forall x^\sigma Hx
\quad\longleftrightarrow\quad
\forall x^\sigma(b\le Hx)
\tag{5}
```

For the forward direction, necessary universal instantiation gives the quantifier lower-bound law, and order transitivity applies. Conversely, the right side is ∀x Box(b→Hx). BF at σ gives Box ∀x(b→Hx). The universally closed, unconditional H equivalence between ∀x(b→Hx) and b→∀x Hx, where x is not free in b, supplies the needed C identity. Thus b≤∀x Hx.

This proves an actual algebraic greatest-lower-bound property for the values of each admitted family. Dually, the admitted existential is the least upper bound of that family's values. No Boolean Completeness for arbitrary current predicates or external sets is inferred. C5 supplies BF at every required type and Functionality. Optional assumptions about an observer are never necessitated in this argument.

## 3 Order automorphisms are exactly reversible logical observers

Suppose Aut≤(E). Order reflection implies injectivity, so the onto map E is an order isomorphism of the proposition algebra. It preserves 0, 1, binary meets and joins by their order characterizations. It preserves complements by uniqueness of Boolean complements. Functionality converts these proposition identities into the corresponding identities of whole operations.

For a fixed admitted H:σt, put

```math
m:=\forall x^\sigma Hx,
\qquad n:=\forall x^\sigma E(Hx)
```

From m≤Hx, monotonicity and (5) give Em≤n. By surjectivity choose b with Eb=n. Each n≤E(Hx) and order reflection give b≤Hx. Equation (5) therefore gives b≤m, hence n=Eb≤Em. Antisymmetry proves

```math
E(\forall x^\sigma Hx)=\forall x^\sigma E(Hx)
\tag{6}
```

Functionality over H supplies the whole quantifier identity

```math
\lambda H^{\sigma t}.E(\forall x^\sigma Hx)
=\lambda H^{\sigma t}.\forall x^\sigma E(Hx)
\tag{7}
```

This works for each admitted σ directly. Existential preservation follows by Boolean duality. In particular, the usual finite logical-observer qualifications hold at every requested type list.

An inverse is admitted explicitly. Define

```math
F_E(q):=\exists p^t\bigl((Ep=q)\land p\bigr)
\tag{8}
```

Fix q and its unique preimage b. C5 makes every equality guard Ep=q an endpoint. The b-joinand in (8) is b; every other joinand is 0. The admitted existential bounds from §2 prove F_E(q)=b. Thus E(F_E(q))=q and F_E(Ep)=p. Functionality gives both inverse equations as whole-operation identities. No Choice principle is needed. The inverse is itself an order isomorphism, so the same proof supplies its whole Boolean and all-type quantifier identities.

Conversely, a reversible qualified logical observer and its qualified whole inverse plainly give an onto order-preserving and order-reflecting map. Therefore

```math
\mathrm{Aut}_{\le}(E)\quad\longleftrightarrow\quad A(E),
\tag{9}
```

where A is the finite reversible Good_t qualification from the [fixed-proposition characterization](../../../classicism-results-2026-10-24-v2/proofs/h-observer-space/reversible-fixed-proposition-characterization.md), §1. The translated equality truth clauses follow from Boolean qualification over C, as in that definition.

A useful weaker-background observation is separate: when an admitted Boolean inverse is already supplied, C plus all Barcan instances suffices for (6)–(7). The stronger C5 assumption here also handles endpoint equality guards, inverse admission and the later noncontingency comparison.

## 4 Proof of the parameter noncontingency equivalence

Assume Rev and Stable(X). For any admitted order automorphism E and its admitted inverse F, the conjugation lift at tt is

```math
E_{tt}^*X=E\circ X\circ F
```

Each output of X is an endpoint, so E fixes it. Stability under F gives X(Fp)=Xp. Functionality therefore gives E*X=X as a whole-operation identity. By (9), these are precisely the reversible logical symmetries.

The general pure-term conjugation lemma in [proof-route.md](../../../next-update/proofs/reversible-invariant-family-realization.md), §2, now makes P(X) invariant under every reversible logical observer. It applies to arbitrary admitted bound-variable types and uses no unadmitted e-valued operation. Rev makes every such invariant proposition either 0 or 1. Therefore P(X)↔Box P(X), proving every instance of (3).

For the converse, assume only (4). Let u be fixed by every Aut≤-member and define the admitted singleton family

```math
X_u(q):=(q=u)
\tag{10}
```

C5 gives endpoint membership. Since E is injective and Eu=u, E(q)=u iff q=u. Both equality propositions are endpoints, so X_u(Eq)=X_u(q). Thus Stable(X_u). Ordinary equality substitution gives J(X_u)=u; this is an unconditional H equivalence and hence a licensed C identity.

The instance of (4) at X_u gives u↔Box u. Also ¬u is invariant, since the automorphisms preserve negation, so the instance at X_{¬u} gives ¬u↔Box ¬u. If u is true then u=1. If u is false then ¬u=1, so u=0. Every invariant proposition is therefore an endpoint. The established fixed-proposition theorem, together with (9), yields Rev.

This argument deliberately uses both singleton families. A single assertion u↔Box u would not by itself make a false u impossible. Uniform quantification over stable families supplies the complement instance.

## 5 Why the restriction matters

Arbitrary endpoint families would force Extensionality: for any proposition p, the singleton X_p in (10) is endpoint-valued and J(X_p)=p. Without stability, (4) and the complementary singleton instance would make every p an endpoint.

The new guard permits X_p exactly when p is fixed by all admitted order automorphisms. It consequently tests the invariant propositions which Rev controls, without excluding contingency elsewhere. Rev does not imply Extensionality, as witnessed by the existing atomless finite-support model in [Reversible separation and pure truth](../../../classicism-results-2026-10-24-v2/proofs/h-observer-space/reversible-separation-and-pure-truth.md), §4.

The original countermodel explicitly fails (3): its nonzero false invariant u gives a stable family X_{¬u}, whose join is true but not Top. This also explains why merely adding more fixed individuals to (1) does not repair that schema.

## Sources and status

The entailment-order automorphism comparison, explicit inverse calculation under its finite guard, and application to schema (3) are the connecting arguments in this note. Direct source: `misc`, §§1–5, unpaginated. The general conjugation and invariant-family machinery is in [proof-route.md](../../../next-update/proofs/reversible-invariant-family-realization.md), §§2–3; the exact invariant-proposition characterization and its admitted orbit-join proof are in the linked note of 24 October. The present order comparison proves qualification directly and does not assume its conclusion from those sources.

The C framework, algebraic order and modal rules are from Bacon and Dorr, [Classicism](https://philarchive.org/archive/BACC-8v1), draft of 16 May 2023, §§1.3 and 1.5. The needed BF-to-Functionality result is Proposition 2.1, n. 27, pp. 20–21; C5-to-BF is Proposition 2.3, p. 22, as recorded in the local principle map. These framework facts are distinguished from the new connecting arguments above.

Ordinary proofs only. The order-automorphism lemma received two separate agent checks. No human verification or formal certificate is claimed, and no native database record is changed.
