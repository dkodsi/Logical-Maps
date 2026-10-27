# Reversible chain separation through adjacent pairs

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated.

A bounded meet chain whose truth cut has a greatest false and a least true proposition has an exact reversible-separation characterization. Its adjacent pairs must distinguish every strict order comparison, and the admitted automorphisms must act transitively on those pairs. The relevant pairs are gaps in the chain, not atoms above Bottom.

This permits atomless examples preserving both kinds of quantifier. A complete split interval, with full function domains, has reversible joint conjunction/disjunction separation together with preservation of every universal and existential quantifier. It nevertheless fails C: its separating observers are not required to preserve primitive negation. The result gives a different positive region from the dense-chain order-primitivity theorem.

## 1. Exact hypotheses and notation

Work over H in the fixed relational type system. Put B=Bottom and T=Top, retaining the fixed abbreviations of the atlas. Assume primitive conjunction is a bounded meet-semilattice with these bounds, and that its order is linear:

```math
p\le q\quad\Longleftrightarrow\quad p\land q=p
\tag{1}
```

As always, the semilattice laws and bound laws are identities of proposition objects. Truth is an upper segment: if p≤q and p is true, then p∧q=p is true, so q is true by the conjunction truth clause.

Let G:(tt)t be an admitted predicate containing identity and closed under composition. Every E with GE must preserve conjunction as a whole composite operation and have an admitted F with GF and both whole inverse equations E∘F=I and F∘E=I. These are the exact admitted-group assumptions of [Reversible semilattice order actions](reversible-semilattice-order-actions.md), §1. They make every G-member an order isomorphism fixing B and T. They do not assume that every external order permutation is admitted.

Assume there are propositions f,u such that

```math
\neg f,\quad u,\qquad
\forall p\,[\neg p\to p\le f],\qquad
\forall p\,[p\to u\le p]
\tag{2}
```

Thus f is greatest among the false propositions and u least among the true ones. They satisfy f<u and no proposition lies strictly between them. Indeed every proposition is true or false, and either alternative excludes an intermediate value. These are extrema of the truth classes, not global extrema of the chain.

Define the admitted adjacency relation

```math
\mathrm{Gap}(a,b):=a<b\ \land\
\neg\exists x\,(a<x\land x<b)
\tag{3}
```

An order isomorphism preserves this relation in both directions. The **gap-density** condition is

```math
\forall p,q\,[p<q\to
\exists a,b\,(p\le a\land\mathrm{Gap}(a,b)\land b\le q)]
\tag{4}
```

It says every nontrivial closed interval contains an adjacent pair. This is different from density of the order, which would prohibit all adjacent pairs.

The action is **transitive on gaps** when every two ordered adjacent pairs are matched by some G-member:

```math
\begin{aligned}
\forall a,b,c,d\,[&\mathrm{Gap}(a,b)\land\mathrm{Gap}(c,d)\\
&\to\exists E\,(GE\land Ea=c\land Eb=d)]
\end{aligned}
\tag{5}
```

All displayed quantifiers are over admitted objects. Formula (5) does not require an admitted operation choosing E uniformly for the pairs.

## 2. Exact characterization

Write

```math
S[G]:=\forall p,q\,[p=q\leftrightarrow
\forall E\,(GE\to(Ep\leftrightarrow Eq))]
\tag{6}
```

**Theorem 1.** Under the bounded-chain, admitted-group and truth-extremum hypotheses above,

```math
\boxed{S[G]\quad\longleftrightarrow\quad
\text{gap-density and transitivity of G on gaps}}
\tag{7}
```

**Necessity.** Suppose S[G] and p<q. Some admitted E with GE distinguishes p,q. Since E is increasing and truth is an upper segment, Ep is false and Eq true. By (2), Ep≤f<u≤Eq. Choose an admitted inverse F in G. Put a=Ff and b=Fu. Then p≤a<b≤q, and (3) holds for a,b because it holds for f,u and F is an order isomorphism. This proves (4).

If a<b is itself an adjacent pair, a separating E again has Ea≤f<u≤Eb. Adjacency of Ea,Eb forces Ea=f and Eb=u: a strict inequality at either outer end would insert f or u strictly inside that adjacent pair. Hence every gap can be sent to the fixed truth gap (f,u). For any two gaps, compose a map from the first to (f,u) with the admitted inverse of a map from the second to (f,u). Closure of G gives a member taking the first gap to the second, proving (5).

**Sufficiency.** If p≠q, linearity lets us assume p<q. By (4) choose a gap a<b contained in [p,q]. By (5), some admitted E in G sends a,b to f,u. Monotonicity gives Ep≤f and u≤Eq. Every proposition below f is false, since truth is upward closed and f is false. Every proposition above u is true. Thus E distinguishes p and q. Equality implies agreement by H substitution, completing (6). ∎

This is an action-and-order characterization, not a reformulation quantifying over separating truth profiles. Gap-density and gap transitivity make no reference to the truth predicate. Truth enters through the explicit existence of the adjacent cut (2).

The theorem does not require C, NI, ND, BF, Plenitude, Choice or an atom premise. The admitted inverse and whole-preservation assumptions are retained. For full relational separation, append the usual all-type Functionality schema; propositional separation alone does not supply it.

## 3. Quantifier preservation from the order

Suppose a primitive universal quantifier at an admitted type σ supplies the greatest lower bound of every admitted family F:σt in the chain. Every G-member then preserves this universal **pointwise**:

```math
E(\forall x^\sigma Fx)=\forall x^\sigma E(Fx)
\tag{8}
```

To prove this, write v=∀x Fx. Order preservation gives Ev≤E(Fx) for every x. If z≤E(Fx) for every x, apply the admitted inverse E⁻¹ to obtain E⁻¹z≤Fx for every x, hence E⁻¹z≤v and z≤Ev. Thus Ev is precisely the GLB of the admitted family λx.E(Fx), proving (8) by uniqueness. This reasoning does not quantify over external families or infer that every external subset is represented.

Dually, if a primitive existential quantifier supplies the admitted LUBs, then

```math
E(\exists x^\sigma Fx)=\exists x^\sigma E(Fx)
\tag{9}
```

If primitive disjunction is the join of the same chain, order isomorphisms likewise preserve it pointwise. At propositional scope, converting these equations into whole composite identities needs the relevant local Functionality instances: Fun_(σt,t) for each quantifier and the usual two curried instances for a binary connective. At full relational scope all Fun is already an explicit part of the factorization, so the whole-operation upgrade is available. No preservation of primitive negation follows from these order arguments.

Consequently Theorem 1 gives the same exact characterization for full relational separation by reversible whole M,V,Q_Δ,P_Γ observers when the original M,V operations give the stated chain, the listed quantifiers supply its admitted bounds, Fun is present, and G is the specified admitted whole-M automorphism group. The lists Δ,Γ remain finite and external. If the observer class has additional restrictions, the group hypotheses and gap transitivity must hold for that actual admitted class.

### Plenitude supplies the adjacent truth cut

There is a route to (2) from a pre-existing admission principle. Assume the original M,V operations give the bounded chain, Q_t supplies its admitted GLBs, P_t its admitted LUBs, and the single instance Plen_{t,t} holds. Apply that instance to the two current total single-valued relations

```math
\begin{aligned}
U_+(p,y)&:=(p\land y=p)\lor(\neg p\land y=T),\\
U_-(p,y)&:=(\neg p\land y=p)\lor(p\land y=B)
\end{aligned}
\tag{9a}
```

They supply admitted A₊,A₋:tt. Every A₊p is true, and A₊p=p whenever p is true. Every A₋p is false, and A₋p=p whenever p is false. Put

```math
u:=\forall p\,A_+p,\qquad f:=\exists p\,A_-p
\tag{9b}
```

The H truth clauses make u true and f false. The GLB property gives u≤A₊p=p for every true p, while the LUB property gives p=A₋p≤f for every false p. Thus (2) follows, and linearity makes (f,u) adjacent. No equation between function objects or optional-premise necessitation has been used; Fun and C are unnecessary for this step.

Consequently, under this exact Plenitude and order-quantifier package, Theorem 1 needs no additional truth-extremum premise: reversible separation by G is exactly gap-density plus gap transitivity. This also explains why the model below uses a split interval: an order-dense chain cannot have both such quantifiers, the stated admission instance, and their H truth clauses. The earlier dense-chain example uses different primitive quantifier operations, so there is no conflict.

The [Plenitude normalization note](plenitude-material-normalization.md), §1, states the precise pre-existing t,t instance used here. Full function domains satisfy it, since every current total single-valued relation has its function in the domain. The present use admits truth-restricted families and then takes their order bounds; it does not assume a truth-extremum or an endpoint-valued observer in advance.

## 4. A complete atomless split interval

Define the proposition domain

```math
L=\{B,T\}\ \cup\ ((0,1)\times\{0,1\}),
\tag{10}
```

where (0,1) is the real open unit interval. Put B below every ordered pair, T above every pair, and use the lexicographic order on the pairs. The two points at a real coordinate x satisfy

```math
(x,0)<(x,1)
\tag{11}
```

They are adjacent. These are all the adjacent pairs. If two interior points have distinct real coordinates, an intermediate real coordinate supplies a point strictly between them. The same argument supplies a point between B and any interior point, and between any interior point and T.

The order is complete. Here is an explicit supremum calculation for a nonempty set A. If T∈A, its supremum is T. If A has no interior points, A={B} and its supremum is B. Otherwise take the ordinary real supremum r of its interior coordinates. If r=1 the supremum in L is T. If r<1 and A contains a point at r, take its largest such point: (r,1) if present, otherwise (r,0). If A contains no point at r, its supremum is (r,0). The defining upper-bound and leastness properties follow from the real supremum property and the lexicographic order. The infimum construction is dual: use B if the infimum coordinate is 0, the least point at r if attained, and (r,1) when approached only from above. Empty joins and meets are B and T respectively.

The chain has no meet atoms: every p>B has a strictly intermediate point between B and p, using a smaller positive coordinate when p is interior. It has no join coatoms for the dual reason. Nevertheless it satisfies (4). If p,q have the same coordinate, they themselves form a gap. If they have distinct coordinates, choose x strictly between them and use ((x,0),(x,1)); intervals involving an endpoint are handled the same way. Thus the gap structure is abundant even though no gap touches either bound.

Designate a proposition true exactly when it is at least

```math
u=(1/2,1),\qquad f=(1/2,0)
\tag{12}
```

Then (2) holds, with f,u as displayed.

## 5. Full H interpretation and the separating group

Use singleton individuals. At every allowed relational arrow type take the full set of functions between the relevant domains. Interpret abstraction and application by actual functions. Conjunction is min and disjunction max in L. Define primitive negation by

```math
\neg B=T,\quad\neg T=B,\qquad
\neg(x,i)=(1-x,1-i)
\tag{13}
```

This is an order-reversing involution and exchanges the true and false segments determined by (12). Interpret each universal quantifier as the infimum of the values of its admitted family, and each existential as the supremum. Completeness from §4 makes these operations total.

These quantifiers have the H truth clauses. If every family value is true, every value is at least u, so its infimum is at least u and true. If some value is false, the infimum lies below that false value and is false. If some value is true, the supremum is true; if all values are false, all lie below f and their supremum lies below f, hence is false. Every type is nonempty. Identity at every type takes value T for actual equality and B otherwise.

Thus the ordinary truth clauses, equality substitution, contextual beta/eta and the quantifier rules hold. This is a full-domain H interpretation in the framework of [Local tiers and models](local-tiers-and-models.md), §1. All Functionality instances hold because there are no unobserved arguments. The fixed a=∀p p is B; hence its fixed abbreviations a∨¬a and a∧¬a are T and B as required. This verifies the complete typed interpretation, not just a proposition algebra.

Every increasing bijection h:(0,1)→(0,1) induces an admitted operation

```math
E_h(B)=B,\quad E_h(T)=T,\qquad
E_h(x,i)=(h(x),i)
\tag{14}
```

Its inverse is induced by h⁻¹. The predicate G selecting exactly these operations is admitted because the higher function domains are full; take it to return T on the specified class and B elsewhere. Composition, identity and inverses remain in G.

For any 0<x,y<1, an increasing piecewise-linear bijection of [0,1] fixing its endpoints and taking x to y restricts to a bijection as above. Consequently G is transitive on the adjacent pairs (11). Section 4 gives gap-density, and Theorem 1 supplies S[G]. Full Functionality lifts this to separation at every relational output type.

Every order isomorphism of a complete chain preserves all infima and suprema: the lower-bound/upper-bound argument of §3 applies to every set of values. Hence the observers (14) preserve min, max and every primitive universal and existential quantifier. Because these are actual functions on full domains, the resulting composite identities are whole-operation identities. Both the observer and its admitted inverse have all of these preservation properties. Thus, for every finite external Δ,Γ, the model satisfies full relational separation by reversible endpoint-fixing whole M,V,Q_Δ,P_Γ observers. In this particular model the same witnesses work for all the lists; no infinitary qualification formula has been introduced.

## 6. Why this does not recover C

The model fails C. Take p=(1/4,0). Then ¬p=(3/4,1), so

```math
p\lor\neg p=(3/4,1)\ne T
\tag{15}
```

H proves the material equivalence of p∨¬p and T. C's Logical Equivalence schema would identify the corresponding lambda terms and hence these output values. Thus (15) contradicts C, while all the positive preservation claims in §5 hold.

There is no conflict with complete logical separation recovering C. Negation preservation is absent from the qualified class. For instance, an h taking 1/2 away from 1/2 moves the actual truth gap and cannot commute with (13). The order automorphisms that do commute with (13) preserve that gap and therefore preserve current truth; they cannot separate distinct same-truth propositions. This last observation concerns the displayed order automorphisms; no classification of every possible observer in the model is needed for the C failure.

The full model supplies both a least true and a greatest false proposition, yet it is atomless. The gap theorem therefore complements the [dense-interior primitivity theorem](reversible-semilattice-order-actions.md), rather than deriving an atom conclusion from these truth extrema. The exact [reversible-meet atom theorem](reversible-meet-characterization.md) still requires an actual meet atom, which this model lacks.

The quantifier conclusion is stronger than the earlier rational-chain example, whose quantifiers return endpoints according to current truth and therefore need not be preserved by its separating order automorphisms. Here genuine infima and suprema, together with an adjacent truth cut, supply both quantifier families with their whole identities. No endpoint-valued restriction is imposed on the observer outputs.

## 7. Sources

The gap characterization, its admitted-quantifier extension, and the split-interval model verdicts are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated. The proof of order completeness uses the ordinary completeness of the real interval in the external model construction; no internal Choice or completeness schema is inferred from that metatheory.

The fixed H language is in [Background](../../source/topics/classicism/background.md). The full-function semantic verification uses [Local tiers and models](local-tiers-and-models.md), §1. The admitted-group convention and the separate dense-chain theorem are in [Reversible semilattice order actions](reversible-semilattice-order-actions.md), §§1–4. Full typed lifting is [Typed separation](typed-separation-and-classicism.md), §2. The distinct atom-bearing characterization is [Reversible meet characterization](reversible-meet-characterization.md), §§2–5.
