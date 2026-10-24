# Exact characterization of reversible meet separation with an atom

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated.

Reversible meet separation with one atom has an exact structural characterization. The proposition order must be atomistic, one of its atoms must be true, and its admitted meet automorphisms must act transitively on atoms. The true atom then determines ordinary truth. Neither C nor any preservation of negation, disjunction or quantifiers is required.

A version for an arbitrarily restricted observer class uses an even more direct action condition: every atom must be movable to a true atom by an eligible observer. That formulation does not assume that the extra restrictions are closed under inverses or composition.

## 1. Definitions

Use H in its fixed relational language, with the fixed Top and Bottom abbreviations T,B. Let

$$
A(E):=ET,\qquad Z(E):=\neg EB,
$$
$$
M(E):=(\lambda p,q.E(p\land q))
      =(\lambda p,q.Ep\land Eq).
$$
Write I for the identity operation and define composition by the admitted lambda term. Put

$$
\operatorname{Aut}_M(E):=
M(E)\land
\exists F^{tt}\,[M(F)\land E\circ F=I\land F\circ E=I].
$$
All three preservation/inverse assertions are whole-operation identities. In particular an external permutation or a pointwise order bijection is not automatically an eligible observer.

For any additional qualification R(E), set

$$
K_R(E):=R(E)\land\operatorname{Aut}_M(E),
$$
$$
S_R:=S[A\land Z\land K_R],
$$
where S is propositional separation by material agreement of observer outputs:

$$
S[K]:=\forall p,q\left[
p=q\leftrightarrow
\forall E\,(K(E)\to(Ep\leftrightarrow Eq))
\right].
$$
The basic case has R always true.

Let BMeet say that primitive conjunction is an associative, commutative, idempotent operation with

$$
p\land T=p,\qquad p\land B=B.
$$
Thus it is a bounded meet-semilattice. Define

$$
p\le q\quad:\!\!\leftrightarrow\quad p\land q=p
$$
and

$$
\operatorname{Atom}(a):=
a\ne B\land
\forall b\,[b\le a\to(b=B\lor b=a)].
$$
Here Atom refers to this meet order, not to an unstated Boolean or modal structure.

Write AS for the atomistic order condition

$$
\operatorname{AS}:=
\forall p,q\left[
\bigl(\forall a\,
  ((\operatorname{Atom}(a)\land a\le p)\to a\le q)\bigr)
\to p\le q
\right].
$$
Under BMeet, this says exactly that each p is the least upper bound of its atoms. Equivalently, every failure p not below q is witnessed by an atom below p and not below q. It is stronger than merely requiring an atom below every nonbottom element.

Finally put

$$
\operatorname{MoveTrue}_R:=
\forall a\left[
\operatorname{Atom}(a)\to
\exists E\,(K_R(E)\land Ea)
\right].
$$
This is an internal existence condition on admitted observers. It does not choose a simultaneous observer-valued function of all atoms.

## 2. The exact theorem for an arbitrary restricted class

**Theorem 1.** Over H, for every R,

$$
\boxed{
S_R+\exists a\,\operatorname{Atom}(a)
\quad\leftrightarrow\quad
\operatorname{BMeet}+\operatorname{AS}
+\operatorname{MoveTrue}_R.}
$$
No closure property of R is required.

### Forward direction

The [reversible meet theorem](reversible-meet-atomicity.md), §§2–4, proves precisely the needed implications. Briefly, observer profiles give the bounded meet order. Every qualified observer and its admitted meet-preserving inverse are order isomorphisms, so they fix T,B and preserve atoms.

Separation of any atom a from B supplies an eligible E with Ea true, since EB is false. This establishes MoveTrue_R. The assumed atom therefore also supplies a true atom w. H's conjunction truth clause makes a true atom unique and gives

$$
p\quad\leftrightarrow\quad w\le p.
$$
If p is not below q, separate p and p and q. Meet preservation forces a witness E with Ep true and Eq false. Pulling w back along its admitted inverse yields an atom below p and not below q. Thus AS holds. This argument requires no assertion that the inverse satisfies R.

### Two order facts used in the converse

Under BMeet, any Aut_M observer is an order isomorphism, fixes both bounds, and preserves atoms. These are consequences of its meet preservation and two inverse identities.

Also any true atom w determines truth:

$$
\boxed{\forall p\,[p\leftrightarrow w\le p].}
$$
If p is true, w and p is true and hence differs from the false B. Atomhood forces w and p equals w, giving w below p. Conversely w below p means w and p equals w; since w is true, H's conjunction truth clause makes p true. No identity between the two propositions of this biconditional is inferred.

### Converse direction

Assume BMeet, AS and MoveTrue_R.

First AS ensures that at least one atom exists. Otherwise every q would be an upper bound of the empty collection of atoms below T, so AS would give T below B. The bounds would then identify T with B, contradicting their opposite H truth values.

Suppose p and q are distinct. In the meet order either p is not below q or q is not below p. Treat the first case. AS supplies an atom a with a below p but not below q. By MoveTrue_R, choose an admitted E satisfying K_R with Ea true, and choose its admitted meet-preserving inverse F.

The atom w:=Ea is true. Applying E to a below p gives w below Ep, so Ep is true. If Eq were true, the truth characterization by w would give w below Eq. Applying F would yield a below q, a contradiction. Hence Eq is false.

The observer E fixes T,B because it is an order isomorphism of the bounded meet order. Thus it also satisfies A,Z and is eligible for S_R. It distinguishes p,q. The reverse-order case is symmetric, and H substitution supplies equality-to-agreement. This proves S_R and completes the equivalence. ∎

The converse extracts one atom and one observer for the particular pair being separated. It does not invoke Choice, an external supply of functions, or Functionality.

## 3. The automorphism-transitivity formulation

For the basic class R=true, let

$$
\operatorname{TrueAtom}:=
\exists w\,(\operatorname{Atom}(w)\land w)
$$
and

$$
\operatorname{Trans}_M:=
\forall a,b\left[
(\operatorname{Atom}(a)\land\operatorname{Atom}(b))
\to
\exists E\,(\operatorname{Aut}_M(E)\land Ea=b)
\right].
$$
**Theorem 2.** Over H,

$$
\boxed{
S[A\land Z\land\operatorname{Aut}_M]
+\exists a\,\operatorname{Atom}(a)
\quad\leftrightarrow\quad
\operatorname{BMeet}+\operatorname{AS}
+\operatorname{TrueAtom}+\operatorname{Trans}_M.}
$$
Under BMeet and AS, atoms exist. MoveTrue supplies a true atom w, which is unique by the truth/meet argument above. For any atoms a,b, choose admitted automorphisms E_a,E_b taking them to true atoms, hence to w. If F_b is an admitted inverse of E_b, then F_b composed with E_a takes a to b.

This composite is still an admitted full-M automorphism. Full M is closed under composition by substitution of its whole-operation identities, and the two inverse identities compose by conversion. No pointwise-to-operation upgrade is involved.

Conversely, TrueAtom supplies w, and transitivity supplies an admitted automorphism taking every atom a to w. This is exactly MoveTrue. Apply Theorem 1.

A true atom, rather than a separate truth-principality axiom, is the required connection to current truth. Atomhood and H's conjunction truth clause already provide the full material equivalence p iff w is below p.

## 4. Extra restrictions and the precise closure requirement

Theorem 1 remains valid with any R for which its displayed qualification is meaningful. Theorem 2 has an R-restricted version when the admitted K_R maps are closed under composition and admit their inverses within K_R.

Under that closure assumption,

$$
\operatorname{MoveTrue}_R
\quad\leftrightarrow\quad
\operatorname{TrueAtom}
+\operatorname{Trans}_{K_R}
$$
in the presence of BMeet and AS. The proof is exactly the composition argument in §3, now within the restricted class. It is enough that each K_R map has an admitted K_R inverse; no claim about every independently chosen inverse is needed.

Without the closure assumption, retain Theorem 1. Every atom is still movable to the unique true atom by an eligible observer, but an eligible map between an arbitrary pair of atoms need not follow. Its construction uses an inverse and a composition, either of which could violate R.

If R is indexed by a fixed finite type list, all witnesses in that instance use the same list. No quantification over types or mixing of separately qualified observers is implicit.

## 5. Representation and typed consequences

Assume either characterization. At a current evaluation point let

$$
\mathcal A(p):=\{a:\operatorname{Atom}(a)\text{ and }a\le p\}.
$$
AS makes this a faithful order representation, with

$$
\mathcal A(p\land q)=\mathcal A(p)\cap\mathcal A(q),\qquad
\mathcal A(B)=\varnothing,\qquad
\mathcal A(T)=\{\text{all atoms}\}.
$$
Every singleton atom set is represented. If w is the true atom, p is true exactly when w belongs to A(p).

An admitted meet automorphism E permutes the atoms and satisfies

$$
\mathcal A(Ep)=E[\mathcal A(p)].
$$
Consequently its observer truth profile is

$$
Ep\quad\leftrightarrow\quad E^{-1}w\le p.
$$
Thus the reversible observers observe membership at the atom obtained by moving the true atom backward. Transitivity means every atom is obtained in this way; AS means those atom tests distinguish every proposition.

This is a representation of propositions and their current truth profiles. It does not claim the action on atoms distinguishes all operator objects, that every external permutation is admitted, that every subset of atoms is represented, or that primitive disjunction or quantifiers are determined by the meet structure.

For full typed separation, the exact structural characterizations acquire precisely the explicit Functionality schema. For example,

$$
\operatorname{FullSep}[A\land Z\land\operatorname{Aut}_M]
+\exists a\,\operatorname{Atom}(a)
$$
is equivalent over H to BMeet + AS + TrueAtom + Trans_M + Functionality. This follows from the [general typed-separation theorem](typed-separation-and-classicism.md), §2, applied to Theorem 2.

The atom assumptions and conclusions remain propositional. Full typed separation has not converted them into atomicity assertions at every higher type. No statement here is boxed.

Ordinary atomicity is insufficient for the structural converse: in the three-element chain B<a<T, every nonbottom element has an atom below it, but a and T have the same atom set. Even a transitive action on the singleton atom set and truth principal at a cannot make those atom tests distinguish a from T. AS is the exact order condition used in the proof.

## 6. Atomisticity and a true atom do not supply transitivity

The following finite full-function H model verifies that the automorphism condition in Theorem 2 is substantive.

Let U={a,b,c} and take

$$
D_t=\{\varnothing,\{a\},\{b\},\{c\},\{a,b\},U\}.
$$
A proposition p is true exactly when c belongs to p. Take a singleton individual domain and the full function space at every admitted arrow type. Interpret application and abstraction as actual function application and abstraction.

Interpret primitive conjunction by intersection, which is closed on D_t. Interpret every other logical primitive by returning U when its ordinary H truth condition is true and the empty set when it is false. More explicitly, negation returns U just when its argument is false; disjunction returns U just when at least one argument is true; universal and existential quantification return U just when every or some admitted instance is true, respectively. Equality at every type returns U for actual identity and the empty set otherwise.

**Fixed abbreviations and H soundness.** The proposition forall p p is the empty set, since the domain includes a false proposition. Its negation is U; their primitive disjunction is U, and their primitive conjunction is the empty set. Thus the fixed Top and Bottom really are

$$
T=U,\qquad B=\varnothing.
$$
Intersection has the ordinary conjunction truth condition for membership of c. The other primitive truth conditions hold by their definitions. Actual function spaces validate application, lambda conversion and all Functionality instances; actual identity validates equality substitution. Hence this is an H model at every admitted relational type. Equality judgments have outputs T or B, so identity bivalence holds at every type as well.

**The structural conditions.** The meet order is subset inclusion on the displayed six sets. Its three atoms are {a},{b},{c}. Every displayed set is the union of its atoms and therefore their least upper bound in this restricted order. Consequently BMeet and AS hold. The unique true atom is {c}, and ordinary truth is exactly the condition {c} below p.

**The admitted automorphisms.** Since all function spaces are full, Aut_M is exactly the class of actual meet-semilattice automorphisms. Every such map fixes the two bounds. The set {a,b} is the unique proper element that is neither bottom nor an atom, so it is fixed. Its two atoms {a},{b} may be exchanged, while the remaining atom {c} must be fixed. Thus the only meet automorphisms are identity and the interchange of a,b, extended to the displayed sets.

Every such automorphism preserves current truth, because it fixes {c}. In particular all of them reject both the empty set and {a}, which are distinct propositions. Reversible meet separation therefore fails already at t. Atom transitivity, or equivalently MoveTrue, is exactly the missing condition: {a} cannot be sent to the true atom {c}.

For comparison, ordinary strong meet separation does hold. For each nonempty displayed set d, the full function space admits the principal observer

$$
P_d(p)=
\begin{cases}
U,&d\subseteq p,\\
\varnothing,&d\not\subseteq p.
\end{cases}
$$
It fixes T,B, preserves intersection, and separates by taking d to be an atom in the symmetric difference of two displayed sets. Because the function domains are full, these are whole-operation preservation identities. The observers have two outputs and fix both, hence are idempotent as operations. Thus even ordinary meet separation with explicit binary-range idempotent witnesses does not supply the reversible atom motion required by the characterization.

No preservation of the independent primitive negation, disjunction or quantifiers is claimed for these principal observers. The model is used as an H model, not as a C model.

## 7. Sources and scope

The direct source for the converse, exact characterizations and finite asymmetric-atom construction is this original argument (`misc`, OpenAI Codex, 24 October 2026, §§2–6, unpaginated). The forward atom-spreading argument is proved in [Reversible meet separation and atoms over H](reversible-meet-atomicity.md). The relation between full typed separation and Functionality is proved in the linked typed-separation note.

The fixed language is specified in [Background](../../source/topics/classicism/background.md). These results use no C, NI, BF, identity bivalence, negation preservation, disjunction preservation, quantifier preservation or Choice principle. No database records, generated state or Lean files are changed by this note.
