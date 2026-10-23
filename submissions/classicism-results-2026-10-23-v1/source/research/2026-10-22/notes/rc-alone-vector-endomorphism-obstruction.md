# Removing order does not save the full-vector-symmetry seed

OpenAI Codex research audit, 22 October 2026. The endomorphism argument was supplied by the `rigid_bottom_audit` agent and independently checked and written out by `bourbaki_audit`. Ordinary mathematics only; no model, Lean verification, human check, or database edit is claimed.

## Exact hypotheses and verdict

Let M be an infinite-dimensional vector space over the actual standard field Q, regarded as a divisible torsion-free abelian group. The higher-type structure contains the addition graph and named individuals h,c. It is closed under the lambda and quantifier constructions of C, and includes the first-order rational scalar graphs. An optional named predicate H=Qh causes no change below.

Let G be the full group of Q-linear automorphisms of M fixing h,c. Assume that G acts on the WHOLE intensional structure, preserves the designated evaluation, and fixes the seed relation entities. Assume every admitted entity has finite individual support: it is fixed by G_A for some finite A, where G_A fixes A pointwise.

Then RC at (et,e) fails. No ordering relation, standard-natural predicate, ideal fullness, or arbitrary powerset closure is needed.

## 1. A finite-support additive endomorphism is a rational scalar

Let F be an admitted graph which is actually total, functional, and additive on M. Choose a finite support A for its entity, and put W=span_Q(h,c,A). Actual functionality identifies F with an external map f:M→M for this argument only. Additivity and the divisible torsion-free group law imply that f is Q-linear. Invariance of the graph under G_A gives f(gx)=g f(x) for all g∈G_A.

For b∉W, the pointwise stabilizer of W and b has fixed-point set W+Qb. Hence f(b)=w_b+q_b b for unique w_b∈W and q_b∈Q. The group fixing W pointwise acts transitively on M\W, so equivariance makes the coefficients independent of b: there are w∈W and q∈Q with

    f(b)=w+qb  for every b∉W.

Apply this at b and 2b. Additivity gives w+2qb=f(2b)=2f(b)=2w+2qb, so w=0. For a∈W, both b and b+a lie outside W; therefore

    f(a)=f(b+a)−f(b)=q(b+a)−qb=qa.

Thus f=q·Id on all of M. This argument only needs W proper, not codimension at least two.

The fixed-point and transitivity statements are ordinary linear algebra: extend a basis of W by b; scaling or changing the remaining basis vectors supplies the required automorphisms. For a countable explicit rational vector space they can also be supplied directly by finite linear transformations.

## 2. The admitted endomorphism quantifier defines rational multiplication

Write End(F) for the actual formula saying that F is a total functional additive binary relation on individuals. This is an admitted formula; all sums can be expanded with the ternary addition graph. Define

    QMult(x,y) := ∃F^(eet) [End(F) ∧ F(x,y)].

Section 1 proves that QMult(x,y) implies y=qx for some actual rational q. Conversely every rational scalar graph y=qx is first-order definable from addition (integer multiples and unique division), hence admitted, and is an additive endomorphism. Consequently the actual extension of QMult is exactly rational scalar multiplication.

This is stable under all further comprehension/quantifier closure preserving the stated group and finite-support invariant: every newly admitted additive endomorphism still falls under §1. It does not rely on guessing a first-stage extension of an impredicative ancestral.

For a finite tuple A, ordinary lambda comprehension now represents Span_A=span_Q(h,c,A), by taking a finite sum of QMult-multiples. Its defining intension and its complement are fixed by G_A.

## 3. The uniform membership chooser is impossible

Suppose S is a functional selector for U(P,y):=Py ∨ ¬∃z Pz, as supplied by RC at (et,e). Choose finite support A for S. The predicate F_A:=M\Span_A is nonempty because M has infinite dimension. Its code is fixed by G_A, while no point of its extension is fixed by G_A: the fixed-point set is exactly Span_A.

The selected y satisfies S(F_A,y) and F_Ay. For each g∈G_A, invariance gives S(F_A,gy); functionality yields gy=y. This contradicts F_Ay.

## 4. Limits of the obstruction

The proof uses the FULL vector-space automorphism group, not only the additive shear group of the ordered seed. For shear-only actions, centralizers can contain non-scalar finite-rank maps, so §1 is not available without another argument.

If the group fixes an externally large subspace W0 pointwise, and supports are finite only relative to W0, the scalar-endomorphism classification still holds whenever W0+span_Q(A) is proper. But the final contradiction no longer follows: the complement of a finite rational span can contain many G_A-fixed elements from W0. One must represent the ENTIRE fixed subspace W0+span_Q(A) to use the moving-fiber contradiction. Nothing here supplies such a representation.

Thus this rules out the order-free finite-base full-vector-symmetry seed. It does not rule out the proposed unrepresented-W0 escape and does not settle RC⇒TC.
