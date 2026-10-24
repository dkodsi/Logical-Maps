# Local and necessary observer separation

Original mathematical argument, direct source misc; unpaginated.

1. SCOPE

For fixed X put S_X:=forall p,q [p=q IFF forall O(X(O)->O(p IFF q))].
The result here is a model satisfying full Boolean/quantifier separation
at one object and failing it at an accessible object, despite C5. The
routine reformulation using K_X(p)=forall O(X(O)->Op) is not a separate
research result: over C, BOX S_X iff K_X=(lambda p.BOX p).

2. RE-EVALUATE THE EXISTING QUALITATIVE-CONTRAST MODEL AT W1

Keep the entire published construction used in reverse-entailment-countermodel.txt,
but take W1 as the evaluation object. W0 and W1 are copies of N; all
bijections between any two objects are arrows. Propositions are finitely
pinned sets of outgoing arrows. Their component ending at W0 is invariant
under every postcomposition by a permutation of W0, hence is full or empty.
Their component ending at W1 has no additional symmetry restriction.
Higher types contain the finitely pinned applicative profiles.

All arrows remain invertible, so this evaluation satisfies C5 and BF at
every type. This is the SAME action model evaluated at its other object,
not a new claim of soundness for an arbitrary restricted hierarchy.

Let A be the proposition consisting of all arrows W1->W0. It is a
nonbottom atom, although it is false at W1. Its complement D consists of
all loops W1->W1 and is atomless. There are two kinds of separating tests.

3. FINITE-PERMUTATION OBSERVERS SEE THE W1 COMPONENT

For a permutation pi:W1->W1 with finite support K, let the current
application of E_pi be the proposition action rho_t(pi). The required
whole exponential profile is

  alpha_pi(h,a) = rho_t(h pi h^-1)(a),

for h:W1->V and a in D_t(V). This is the groupoid version of the
finite-support-permutation observer from operator-model-separations.txt.
It satisfies application coherence, since it is equivalently
rho_t(h) rho_t(pi) rho_t(h^-1)(a).

Admissibility requires finite pinning of the entire profile. If parallel
h,h':W1->V agree on K, then the finite permutations h pi h^-1 and
h' pi (h')^-1 of V are identical. Indeed their common support is h(K)=h'(K),
their action there is given by the same finite permutation of those images,
and they fix the complement. The transported exponential elements are
therefore equal. A groupoid exponential is determined by its current
application, as every future application is recovered using the inverse
arrow. Hence K pins E_pi, and E_pi belongs to the admitted tt domain.

Its current action on a proposition is

  E_pi(p) = {g out of W1 : g pi belongs to p}.

This is inverse image under a bijection of the outgoing arrows, so it
preserves every Boolean operation and both constants.

It also commutes with both quantifiers at every fixed type.
For any current F:sigma t, invertibility of every arrow and its bijective
action on D_sigma give

  forall_sigma F = intersection {F(a): a in D_sigma(W1)},
  exists_sigma F = union {F(a): a in D_sigma(W1)}.

These displayed sets are admitted because they are the interpreted
quantifiers; this is not a claim of arbitrary external completeness.
Inverse image under g |-> g pi commutes with these unions and intersections.

At any future arrow h the
transported E_pi is the same construction for the finite permutation
h pi h^-1. The Boolean and quantifier identities therefore hold for every
future input as well. By C Intensionality, the corresponding composite
operations themselves are identical; for example,

  (lambda F. E_pi(forall x Fx)) = (lambda F. forall x E_pi(Fx)).

The analogous closed identities hold for exists and the Boolean operations.
Thus these witnesses meet both the pointwise identity reading and the
stronger identity-between-composites reading of the user's clarification.

If p,q differ at a loop g:W1->W1, take a finite set S pinning both.
Extend the finite partial bijection g|S to a permutation pi of finite
support. It agrees with g on S, so p,q differ at pi as well. Since

  E_pi(p) is true at W1 iff pi belongs to p,

this admitted observer distinguishes them.

4. ONE ATOM OBSERVER SEES THE W0 COMPONENT

Take the admitted term

  B_A(p):=BOX(A->p).

Every current p either includes all of A or none of it. In the first
case B_A(p)=top. In the second B_A(p)=bottom: from every arrow one can
return to W0, where A holds and p does not. These are literal proposition
identities. Thus B_A is Boolean-preserving and its actual truth exactly
reads membership of the W0 component.

There is a direct FULL IDENTITY verification of its quantifier laws. At
every future object V, the transported A is the set A_V of all arrows
V->W0. Every proposition at V contains either all of A_V or none of it.
For any F:sigma t at V, the groupoid quantifier formulas in section 3 give

  A_V is included in forall x Fx iff every F(a) includes A_V,
  A_V is included in exists x Fx iff some F(a) includes A_V.

Consequently B_(A_V)(forall x Fx) and forall x B_(A_V)(Fx) are the SAME
endpoint proposition: top if every F(a) includes A_V, bottom otherwise.
Likewise the two existential expressions are the same endpoint. These
are literal identities for every future F, so Intensionality also gives
identities between the lambda-F composite operations. The Boolean laws
likewise hold at every future object and give the closed composite laws.
Thus B_A qualifies even for the strongest closed-identity version of every
finite Boolean/quantifier list.

If p,q differ on the W0 component, B_A distinguishes them. Otherwise,
any difference is on the W1 component and is detected by section 3.
This proves proposition separation with the composite identities at every
finite type list at W1. Section 4 of [Logical Observers](logical-observers.md)
therefore gives the entire OS schema at W1.

One can also verify the equality laws directly: in this
groupoid every equality proposition is top or bottom, because
all type actions are bijections. Boolean tests consequently satisfy the
reflexivity and Leibniz clauses. Higher-type pointwise
separation then follows from Functionality, available here with BF.

5. NECESSARY SEPARATION FAILS

At W0, reverse-entailment-countermodel.txt sections 3-4 proves S_B false:
finite pinning and W0's output symmetry prevent every Boolean observer
from detecting the nonempty W1-target component. W0 is accessible from
W1, so BOX S_B is false at W1. In particular BOX OS(t,empty) is false.

We have therefore established the ordinary model separations

  C5 + S_B does not entail BOX S_B,
  C5 + OS does not entail the schema BOX OS.

In the second line OS means all its current finite instances. The failure
of its boxed schema is witnessed by the single instance (t,empty); no
infinitary object formula has been introduced.

For X=Bool, the routine C reformulation gives at W1:

  forall p [K_Bool(p) IFF BOX p] holds,
  K_Bool=(lambda p.BOX p) fails.

This separates current correctness of the collective test from literal
identity with necessity, even with C5 and full current OS.

Exactly the same separation holds for each fixed X consisting of the full
Boolean laws and a finite list of full quantifier laws, including the
closed-composite reading just verified. The W1 witnesses qualify; at W0
Boolean-preserving operators cannot
separate. Therefore, for each of these qualifications,

  C5 + S_X does not entail BOX S_X,
  forall p [K_X(p) IFF BOX p] holds at W1, but K_X=(lambda p.BOX p) fails.

The model is also a new positive example beyond the two earlier extremes:
at W1 it satisfies OS while having an atom (A), a nonzero atomless part
(D), and no Actuality witness. OS thus does not force a choice between
Atomicity_t and Atomlessness. The absence of Actuality follows because
every true proposition can be refined on its W1 component by a fresh
coordinate, exactly as in the finite-support permutation model.

Here is an explicit refinement. If true p is pinned by finite S, choose
distinct a,b outside S with a<b in a fixed external enumeration of W1.
Let r contain exactly the W1-target arrows g with g(a)<g(b), and no
W0-target arrows. Then p AND r is a nonempty proper subproposition of p:
the identity belongs to it, while the transposition of a,b fixes S, belongs
to p, and does not belong to r. Both p and r are admitted. No true p is
an atom, so Actuality fails. At W0 it holds by the source construction.
The closed pure sentence NOT Actuality is therefore true but not necessary
at W1. This also proves failure of no-pure-contingency-r at W1.

6. RELATION TO THE CURRENT RESULT

ordered-symmetry-observers.txt strengthens this example to an everywhere
atomless model and separates necessary Boolean separation from quantifier
separation despite necessary BF. That structural distinction is the current
focus. The original example remains useful for the catalog coverage proof
in full-identity-commutation.txt. Arbitrary Boolean catalog combinations
remain unsettled.

SOURCES

Underlying model: topics/classicism/models/symmetric-qualitative-contrast.yaml;
Bacon-Dorr, Classicism, map draft of 16 May 2023, Appendix D p.79 final
construction. The author-hosted 1 July 2022 draft describes that construction
on printed pp.77-78, and pinning in Definition D.1 on printed p.73:
https://andrew-bacon.github.io/papers/Classicism.pdf .
Intensionality: topics/classicism/principles/intensionality-r.yaml,
Classicism, 16 May 2023 draft, section 1.5 pp.17-18.
The new W1 observer verdict and the distinction in section 5
are arguments of this note, not results attributed to the source.
