# An extensional mathematical core from Gallin comprehension alone

Research theorem, 22 October 2026 (`misc`). Independently audited by the choice lane. This concerns the fixed relational-type fragment of higher-order logic, with no function types ending in e. No database edits, external-fullness claim, or formal-verification claim.

## 1. Assumption and exact conclusion

Assume Gallin Extensional Comprehension (GC). By the independently audited equivalence in `gallin-bivalent-evaluator.md`, there is a unique operation E such that

    forall p (p iff Ep),
    box forall p (Ep=top or Ep=bottom).

For a relation Y, let TwoVal(Y) mean that necessarily every full argument-instance is literally top or bottom. Define Λ_tau(X)(xbar):=E(X(xbar)). The preceding note proves that Λ gives the unique TwoVal relation currently coextensive with X, is idempotent, and necessarily preserves finite Boolean operations. It fixes every TwoVal relation literally. These facts hold without BF, RP or Choice.

**Theorem.** GC alone interprets extensional Henkin higher-order logic, in the fixed relational-type fragment, with all current individuals as its individual domain. Adding ambient Relational Choice supplies ordinary Choice in the interpretation. No C5, BF, Rigid Power, Rigid Comprehension, Atomicity or Infinity assumption is needed.

The theorem is an interpretation at the evaluation point. Its recursively constructed domain predicates have globally two-valued instances, but their future extensions need not satisfy the same unboxed defining characterization at those future points. In particular this is not asserted to be a necessary interpretation obtained by silently boxing GC.

## 2. The recursively actualized domains

Put H_e=top_e. For tau=sigma_1...sigma_n t define

    A_tau(xbar):=conjunction_i H_sigma_i(x_i),
    H_tau:=Λ_(tau t)(lambda F . TwoVal(F) and F<=A_tau).

For n=0, A_t=top. Every H predicate is TwoVal, by construction, and so is every finite product A_tau. At the current point,

    H_tau(F) iff TwoVal(F) and F<=A_tau.                         (1)

Thus the current truth domain H_t consists exactly of top and bottom. Every relational core domain is nonempty because it contains its bottom relation. Its supported top A_tau belongs as well. The individual domain is the whole current nonempty domain of e.

Equation (1) is deliberately unboxed. A future object may belong to the transported H_tau without being TwoVal at that future point; no proof below makes that substitution. All uses of (1) concern current objects in the interpreted structure.

## 3. Application and extensionality

Suppose currently H_(sigma tau)(F) and H_sigma(a). By (1), F is TwoVal and supported on H_sigma times A_tau. A section F(a) is TwoVal: its necessary endpoint condition follows by instantiating the first argument with the fixed current a at every future point. The support inequality gives F(a)<=A_tau. Equation (1) therefore gives H_tau(F(a)). Application preserves the interpreted domains.

If two current core relations agree on all current core argument tuples, their support makes both false on every other current tuple. Hence they are currently coextensive on the whole ambient argument domain. Both are TwoVal by (1), so uniqueness of TwoVal coextension gives their literal identity. This proves target extensionality.

The support condition is again essential: taking all TwoVal relations with unrestricted higher arguments would not justify extensionality from agreement only on interpreted arguments.

## 4. Comprehension and logical operations

For a target formula phi on core arguments, form the ordinary ambient term

    F:=Λ_tau(lambda xbar . A_tau(xbar) and phi*(xbar)).

It is TwoVal and currently represents phi on the core arguments. It is supported on A_tau as an entailment, not merely actually: the necessary Boolean law for E gives

    E(A_tau and phi*) = E(A_tau) and E(phi*) = A_tau and E(phi*),

at every future tuple, because A_tau is TwoVal and E fixes the endpoints necessarily. Thus F<=A_tau and F is a current H_tau-member by (1). This proves every target comprehension instance.

Relational-valued lambda abstraction is the same construction with the output's trailing arguments made explicit. At a current core input, its section is TwoVal and actually coextensive with the intended current core output. Uniqueness of TwoVal coextension makes the two objects identical, proving beta. Eta and extensionality follow from the same support and uniqueness argument.

Target logical constants are normalized and supported as well. For example the target universal-quantifier operation on predicates of core σ-objects is represented by

    Q_sigma(P):=E(H_(sigma t)(P)
                    and forall x(H_sigma(x)→P(x))).

This is TwoVal and supported on H_(sigma t), hence a member of the target operation domain. On current core P it has exactly the truth value of the bounded universal, by current truth correctness of E. Equality at σ is represented by the similarly supported normalized matrix

    E(H_sigma(x) and H_sigma(y) and x=y).

On current core arguments it is the endpoint truth value of their identity. Connectives are handled in the same fashion. These clauses show that quantification and equality are interpreted as available core operations; no unproved necessary outer quantifier-commutation law for E is used.

The standard syntactic induction therefore gives an extensional Henkin interpretation of the entire allowed relational-type language. The formulas being interpreted may quantify impredicatively over the interpreted higher-type domains. This still does not assert external fullness.

## 5. Transfer of ambient Relational Choice

Let a core relation be serial on core inputs with core outputs. Extend it on noncore inputs using a fixed core default, and apply ambient Relational Choice. Restrict the resulting chosen graph to the product of the core domains and apply Λ. The resulting graph is TwoVal, has exactly the same actual choices, and its support is sealed by the necessary Boolean laws just used. It is therefore a core relation, functional and serial on the core inputs.

For an allowed relational output type tau, a core functional graph G(x,Y) also gives a core operation directly, without invoking ambient Plenitude. Define its curried matrix by

    F(x,ybar):=E(A_(sigma tau)(x,ybar)
                     and exists Y(G(x,Y) and Y(ybar))).

At a current core input x, the graph has a unique chosen core output Y. Consequently F(x) is actually coextensive with that Y. The section F(x) and Y are both TwoVal, so uniqueness makes them identical. The support/normalization argument makes F a core operation. Choice with individual output remains represented by a functional binary graph, as required by the fixed type system.

Thus GC+Relational Choice interprets ordinary extensional Choice without needing BF, RP, or a separate Plenitude assumption. Section 7 separately proves the exact transfer of the quantified Infinity axiom.

## 6. Comparison with the rigid core

The ND+RP rigid-domain construction in `bounded-extensional-core.md` obtains intrinsic comprehension by sealing current decisions inside a rigid support. The present construction instead uses the globally TwoVal actualizer to import every current extension and to normalize each domain predicate recursively. These are genuinely different sufficient hypotheses and constructions.

When both constructions apply, their current supported extensional domains can be compared by their actualization maps, but no identity of the two hierarchies is assumed. In particular TwoVal relations need not be rigid when BF fails, and the present proof never substitutes TwoVal for rigidity.

## 7. Exact quantified Infinity transfer under GC

The quantified Infinity transfer can be proved under GC alone for this new core. The choice lane independently audited the argument below on 22 October 2026. This is a theorem about the database's impredicative Frege-cardinality Axiom of Infinity, not merely its finite distinctness schema. It does not require Choice or external fullness.

For clarity take the individual sort e; the same proof works with all objects of any fixed original type σ interpreted as a new base sort. Put ν=(et)t, P=H_et and B=H_ν. P is the current domain of TwoVal properties of all individuals, and B is the domain of TwoVal predicates supported on P. Let N be the original FiniteCardinality_e predicate and Nc its core translation.

The original zero and successor are

    0(X):=forall u not Xu,
    S(Z)(X):=exists y (Xy and Z(X-y)),
    (X-y)(u):=Xu and u!=y.

For a core property X define its core deletion d(X,y):=Λ_et(X-y). Its current extension is exactly X with y removed, and it is a core property. The core zero 0c and successor Sc are the supported normalized versions supplied by core comprehension: on current core X, 0c(X) has the truth value of emptiness, and Sc(Y)(X) has the truth value of

    exists y (Xy and Y(d(X,y))).

Each is a core cardinality object; Sc is represented by a core operation with the usual input support B. These are exactly the interpretations of Frege zero and successor in extensional HOL.

Define the available map

    h(Z):=Λ_ν(lambda X . P(X) and Z(X)).

For every original Z, h(Z) belongs to B. Also h(0)=0c, by current coextension of TwoVal outputs. A subtlety matters: h need not commute with successor on arbitrary Z, because raw X-y need not be TwoVal and Z may distinguish coextensive input properties. The following elementary induction repairs precisely this gap.

### Coextension-invariance of original finite cardinalities

Write Ext(Z) for the actual extensionality condition

    forall X Y [(forall u(Xu iff Yu)) -> (ZX iff ZY)].

Zero satisfies Ext. If Z satisfies Ext, then S(Z) does: for coextensive X,Y, the raw deletions X-y and Y-y are coextensive for every current y; apply Ext(Z) inside the existential successor clause. Thus Ext is an inductive ambient predicate. The impredicative definition of N gives

    N(Z) -> Ext(Z).                                             (2)

This coextension-invariance lemma is already recorded as Lemma A in `topics/classicism/writeups/possible-infinity-t-and-bf-t-imply-axiom-of-infinity-t.md`; the new use here is to repair the core-transfer commuting square under GC.

For every current Z satisfying Ext(Z), and every current core property X, the raw X-y and d(X,y) are actually coextensive. Hence Z gives them the same actual truth value. The definitions and current truth correctness of Λ now give current coextension of h(S(Z)) and Sc(h(Z)) on core X; both vanish outside P and are TwoVal. Unique TwoVal coextension yields the literal identity

    Ext(Z) -> h(S(Z))=Sc(h(Z)).                                 (3)

No BF or boxed Ext hypothesis is used. Equation (3) is derived from coextension of globally TwoVal outputs, not from an illicit application of Logical Equivalence to a contingent premise.

### Surjectivity on natural cardinalities

Fix any core inductive predicate V on B. The ambient predicate

    U(Z):=Ext(Z) and V(h(Z))

contains original zero, and is closed under original successor: Ext is successor-closed, and (3) plus V's inductivity supplies the second conjunct. Therefore N(Z) implies V(h(Z)). Since V was an arbitrary core inductive predicate,

    N(Z) -> Nc(h(Z)).                                           (4)

Conversely form the core image predicate

    I(Y):=Λ_(νt)(lambda Y . B(Y)
                              and exists Z(N(Z) and h(Z)=Y)).

It is a core predicate on B. It contains 0c. If I(Y) holds for a current core Y, current truth correctness supplies an original natural Z with h(Z)=Y. By (2), Ext(Z), and therefore (3) gives h(S(Z))=Sc(Y). Since N is successor-closed, I(Sc(Y)). Thus I is core-inductive, and core induction gives

    Nc(Y) iff exists Z(N(Z) and h(Z)=Y), for current core Y.      (5)

The forward implication uses I and the reverse uses (4). This is a surjectivity theorem, not a claim that h is injective as an intensional map.

### Infinity

The ordinary universal individual property top_et is a core property: it is TwoVal and its support is the whole individual domain. For every original Z,

    Z(top_et) iff h(Z)(top_et),

by current truth correctness of Λ. Combining with (5) gives

    exists Z(N(Z) and Z(top_et))
      iff exists Y in B(Nc(Y) and Y(top_et)).

Negation proves the exact equivalence of the ambient AxiomOfInfinity_e and the core's quantified Axiom of Infinity. More generally, for a core based on all objects of an original type σ, the same proof equates AxiomOfInfinity_σ with the interpreted Infinity axiom of that base sort. For σ=t this means treating ALL original propositions as a new individual sort; it does not make the core Boolean truth sort {bottom,top} infinite.

Consequently GC+Relational Choice+AxiomOfInfinity_e interprets extensional Henkin relational HOL with Choice and its quantified Infinity axiom on all current individuals. This lowers the sufficient modal assumptions of the earlier C5+Actuality transfer theorem, while changing to the TwoVal core constructed here. The earlier C5 proof remains valid for its rigid core.

## 8. Canonical isomorphism with the Actuality world-slice core

Independent mathematical audit: the choice lane checked this section on 22 October 2026. In particular, global TwoVal output for j follows from E's global bivalence on all future arguments; k uses only support; the inverse and quantifier arguments use current domain bijections and never identify future domains. This records an AI-agent audit, not human or formal verification.

Under GC both this core and the world-slice core of `actuality-world-slice-core.md` exist. Let L_sigma,G_sigma denote their respective domain predicates, and A^L_tau,A^G_tau their supports. Their current individual domains are both all current individuals, but their truth domains are {bottom,w} and {bottom,top}, respectively. Their higher domains therefore need not be literally the same.

They are canonically isomorphic as current extensional Henkin structures. Define simultaneous maps j_sigma from the local slice to the globally TwoVal core and k_sigma in the reverse direction. At e both are metalinguistic identity substitution, with no term of type ee. At a relational type tau=sigma_1...sigma_n t define allowed ambient lambda terms

    j_tau(F)(bbar):=A^G_tau(bbar)
                       and E(F(k_sigma_1(b_1),...,k_sigma_n(b_n))),
    k_tau(G)(abar):=A^L_tau(abar)
                       and G(j_sigma_1(a_1),...,j_sigma_n(a_n)).

For n=0 these are j_t(p)=E(p) and k_t(q)=w∧q. Each j-output is globally TwoVal, because both its support and its E-value are globally TwoVal, and it is supported on A^G. Hence it is a current G_tau-member. Every k-output is supported on A^L, hence a current L_tau-member.

Induction on types proves, for current interpreted objects,

    k_sigma(j_sigma(a))=a for L_sigma(a),
    j_sigma(k_sigma(b))=b for G_sigma(b).

For the first identity, evaluate on current local core arguments. Their j-images are global core arguments, and the lower inverse identities reduce the displayed matrix to E applied to the original F-instance. E preserves its current truth. Outside local support both sides vanish. The two outputs are w-supported, so the slice localization lemma gives literal identity.

For the second, evaluate on current global core arguments. The lower inverse identities reduce the matrix to E of an expression currently equivalent to the original G-instance. Current truth therefore agrees. Outside global support both sides vanish. The two outputs are globally TwoVal, so uniqueness of TwoVal coextension gives literal identity. This proves both inductive inverse steps without BF or future domain-identification assumptions.

The same calculation gives application preservation:

    j_tau(Fa)=j_(sigma tau)(F)(j_sigma(a)),

for current local core F,a, and dually for k. Identity is preserved and reflected by the inverse maps. True and false map to true and false. The represented connectives and quantifiers are preserved because their current truth conditions agree under the domain bijections; the respective coextension-uniqueness lemmas upgrade this to literal identities of the core operations. Thus every formula of the interpreted extensional language is preserved.

The maps are canonical: Actuality's true atom w is unique, and GC's globally bivalent evaluator E is unique. No Choice is used. They are available ambient terms at relational types, with graph/identity-substitution treatment of the individual sort; no external bijections or forbidden output types are introduced.

Consequently GC changes the representatives and their global endpoint behavior, but does not change the current extensional mathematical content of the Actuality slice. Choice, represented well-orders, cardinal comparisons, induction and the interpreted quantified Infinity axiom correspond under this isomorphism. This statement compares the two CURRENT structures; it does not identify their future domains or turn the local slice into a necessarily inhabited core.
