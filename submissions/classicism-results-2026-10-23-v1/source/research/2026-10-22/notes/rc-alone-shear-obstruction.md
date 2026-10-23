# The higher-order moving-fiber obstruction rules out the semilinear shear seed

OpenAI Codex research audit, 22 October 2026. New ordinary mathematical argument, checked in outline by the coordinating and seed-research agents. No human check, Lean proof, model construction, or database edit is claimed.

This audits `/tmp/classicism-research/rc-alone-skolem-seed-audit.md`. Its enlarged infinite-dimensional seed does **not** survive impredicative comprehension together with the proposed finite-support invariant. The obstruction below is internally definable; it does not assume symmetric ideal fullness or the full hereditarily symmetric hierarchy.

## 1. Exact hypotheses

At the designated evaluation point let the individual domain be the divisible ordered abelian group

    M = V ⊕ Q,

ordered lexicographically, where V is an ordered Q-vector space of infinite Q-dimension. Let

    H={0}⊕Q,  h=(0,1),  c=(v0,0),  v0>0.

The higher-type structure includes predicates representing the actual addition and ordering relations and H. It includes every first-order definable predicate on finite tuples with individual parameters, and is closed under the impredicative lambda/quantifier constructions of C. Addition notation below is shorthand: no prohibited e→e function type is introduced. Every occurrence of u+v, −u, or a finite sum can be translated using the admitted ternary addition graph and existentially bound outputs.

Let G consist of the shears

    g_f(v,q)=(v,q+f(v)),

where f:V→Q is Q-linear and f(v0)=0. Assume these act as automorphisms of the whole intensional structure preserving the designated evaluation, including the fixed seed relations and h,c. Assume every admitted entity, in particular every candidate selector graph, is fixed by G_A for some finite set A of individual parameters, where G_A denotes the shears fixing A pointwise.

These are exactly the intended no-transversal support hypotheses of the enlarged seed. The argument concludes that RC at (et,e) fails. It does not conclude anything about models that abandon this support invariant or fail to retain the stated seed relations/predicates.

For an explicit metatheoretically elementary V one may take a countable direct sum of Q with a fixed lexicographic basis. The separating linear functionals used below can then be found by finite-dimensional linear algebra; no unprovided choice principle is needed. The seed's example V=R works in the ordinary ZFC metatheory as well.

## 2. The ancestral of +h is exactly the standard natural multiples

Define the admitted predicate

    N_h(n) := ∀P^{et} [ (P0 ∧ ∀u(Pu→P(u+h))) → Pn ].  (1)

Every ordinary nonnegative integer multiple mh satisfies (1), by external finite induction applied to any admitted P.

Conversely suppose n is not such a multiple.

* If n∉H, the admitted first-order property H contains 0 and is closed under +h, so excludes n from N_h.
* If n<0, the admitted nonnegative ray contains 0 and is closed under +h, so excludes n.
* If n∈H and n≥0 but n is not an integer multiple of h, choose an ordinary integer r with n−rh<0. The first-order property

      P(u) := Hu ∧ u≥0 ∧ u∉{n,n−h,...,n−rh}

  contains 0, because no displayed excluded point is 0. It excludes n and is closed under +h: if u+h=n−jh, then u=n−(j+1)h is either another excluded point or negative. Thus it excludes n from (1).

Therefore the actual extension of N_h is precisely {mh:m∈N}, even after further higher-order predicates are added. Adding predicates can only make the intersection in (1) smaller, while every standard iterate belongs to every forward-closed predicate. This exactness is stronger than a merely nonstandard internal natural-number predicate.

## 3. Paired ancestral recursion defines ordinary integer multiplication

For x∈M define an admitted ternary relation L(n,x,y) by saying that (n,y) belongs to every admitted binary relation T satisfying

    T(0,0),
    ∀u v [T(u,v) → T(u+h,v+x)].                     (2)

For every standard m, finite induction gives L(mh,x,mx).

For the converse at that index, define the following FIRST-ORDER predicate on pairs, using the finitely many ordinary multiples jh,jx as parameters or expanded finite sums:

    T_m^x(u,v) := [∨_{j=0}^m (u=jh ∧ v=jx)] ∨ u>mh.  (3)

It contains (0,0) and is closed under the step in (2). At a listed pair with j<m, the step gives the next listed pair. At j=m, the new first coordinate is above mh, so the second disjunct applies. That disjunct stays true after adding h. But at first coordinate mh, (3) holds exactly when v=mx. Hence

    L(mh,x,y) iff y=mx                              (4)

for every standard m, every x,y. The initial predicate domain contains (3), so (4) is preserved under all later expansions.

Only relations on individuals were quantified: T has type eet. No operation with output type e has been postulated.

## 4. Rational multiples and finite rational spans are admitted

Using N_h and L, define QMult(x,y) by

    ∃m n z w [N_h(m) ∧ N_h(n) ∧ n≠0
              ∧ L(m,x,z) ∧ L(n,y,w) ∧ (w=z ∨ w=−z)]. (5)

By §§2–3, (5) holds exactly when y is a rational multiple of x. Zero is included using m=0, and the last disjunction permits negative scalars. Divisibility of the actual group gives the converse witnesses for every rational multiple.

For any finite tuple A=(a1,...,ak), lambda comprehension now supplies the property

    Span_A(y) := y∈span_Q(h,c,a1,...,ak),              (6)

expressed by existentially choosing one Q-multiple of each listed generator and requiring their finite sum to equal y. The terms QMult, N_h and L have been defined uniformly from the fixed seed relations and h; (6) has only the finite tuple A,c,h as additional individual parameters.

Consequently the INTENSION of Span_A, not merely its actual extension, is fixed by every g∈G_A: such g fixes all its parameters and the named seed relation entities, and the whole higher-type interpretation is equivariant. The same holds of its complement F_A:=¬Span_A.

## 5. The rational span is exactly the stabilizer's fixed-point set

Write a_i=(v_i,q_i), and let

    W=span_Q(v0,v1,...,vk) ⊆ V.

A shear in G_A is exactly one whose linear map f vanishes on W. Hence every element of W⊕Q is fixed by G_A.

If v∉W, choose a Q-linear f vanishing on W with f(v)≠0. Then g_f moves every point (v,q), so no such point is fixed by G_A. Thus

    Fix_M(G_A)=W⊕Q=span_Q(h,c,a1,...,ak).             (7)

The final equality holds because subtracting a linear combination of c,a_i with the required first coordinate leaves a multiple of h. Since V has infinite Q-dimension and W is finite-dimensional, the complement in (7) is nonempty.

Equations (6)–(7) show that the moved-element set

    F_A=M \ Fix_M(G_A)

is internally represented by a predicate code fixed by G_A. This is exactly the intension a smaller Henkin construction would have to omit to evade the generic moving-fiber obstruction; here it cannot omit it while retaining the stated comprehension and seed predicates.

## 6. Relational Choice fails

Suppose RC at (et,e) supplied an actual functional S below

    U(P,y):=Py ∨ ¬∃z Pz.

By the finite-support invariant, choose finite A such that every g∈G_A fixes S. Sections 4–5 supply an admitted nonempty F_A whose code is fixed by G_A and whose extension contains no G_A-fixed individual.

The selector supplies y with S(F_A,y) and F_Ay. For every g∈G_A, automorphism invariance gives S(gF_A,gy), i.e. S(F_A,gy), because both S and F_A are fixed. Actual functionality gives gy=y. Therefore y∈Fix_M(G_A), contradicting F_Ay.

This refutes the exact RC property-selector instance. The contradiction uses no BC, Actuality, ND, BF, full external powerset, ideal fullness, operation-valued choice, or arbitrary transfinite closure.

## 7. Consequence for the proposed construction

The original Q² seed failed because higher-order ancestry defined a transversal directly. Passing to infinite Q-dimension avoids that direct transversal but does not save RC: higher-order ancestry defines the finite rational spans that are stabilizer fixed-point sets, and their complements obstruct every finitely supported uniform chooser.

A replacement seed must prevent this definability of support-fixed sets, or alter the support mechanism so that these complements have stabilizer-fixed witnesses. Ordinary first-order definable Skolem functions do not address this condition. No surviving RC/TC countermodel is supplied by the semilinear/shear family under the stated hypotheses.
