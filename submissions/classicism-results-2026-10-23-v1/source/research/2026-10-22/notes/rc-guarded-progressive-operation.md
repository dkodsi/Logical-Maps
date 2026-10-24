# RC supplies a guarded progressive operation on partial selectors

OpenAI Codex research argument, 22 October 2026. Independently audited in outline by the coordinating agent. This sharpens the exact choice instance in the new RC+BC⇒TC proof. It is not a representation theorem for arbitrary functional graphs, and it uses no Plenitude.

## Exact statement

For any admitted σ, including e, put ρ=σt. Over C, for every R^{σσt} which is an equivalence relation actually, Relational Choice at **(ρ,σ)** supplies an admitted operation g:ρ→ρ (depending on R) such that

    F≤gF,
    P(F)→P(gF),
    P(F)∧¬Full(F)→F<gF,

where

    P(F):=∀u v □(Fu∧Fv∧Ruv→u=v),
    Full(F):=∀u∃v(Ruv∧Fv).

All hypotheses are actual and unboxed. Therefore BC at σt together with RC at (σt,σ) implies TC at σ by the already audited chain-completeness/fixed-point argument. RC at (σt,σt) remains an alternative sufficient premise because individual outputs can first be replaced by haecceity codes.

## 1. The actual selected point

Let

    Miss(F,x):=¬∃z(Rxz∧Fz),
    U(F,x):=(¬Full(F)→Miss(F,x)).

This is serial. If ¬Full(F), classical quantifier duality supplies x with Miss(F,x); otherwise any individual of the inhabited σ-domain works. Apply RC at (ρ,σ) to get an actually functional S⊆U.

No necessary functionality or necessary containment of S is asserted. It may have multiple outputs, no outputs, or unsuitable outputs elsewhere.

## 2. A formula that protects itself at every world

Define

    Unique_S(F,y):=∀z(S(F,z)→z=y),
    Safe_R(F,y):=∀z(Fz∧(Ryz∨Rzy)→z=y),
    N(F,y):=S(F,y)∧Unique_S(F,y)∧Safe_R(F,y),
    g:=λF^ρ y^σ [Fy∨N(F,y)].

This has the admitted type ρρ. The guard is evaluated wherever the output predicate is evaluated. If S loses functionality, all its conflicting outputs fail Unique_S, so no such pair is added. If an old F-member would conflict with y under either R-direction, Safe_R blocks y.

The H theorem Fy→(Fy∨N(F,y)) gives F≤gF algebraically.

## 3. Preservation of P

Fix actual u,v. There is an H-theorem implication

    (Fu∧Fv∧Ruv→u=v)
          → ((gF)u∧(gF)v∧Ruv→u=v),

with g expanded as above. Check the four disjunctive cases:

* both points come from F: use the antecedent;
* both come from N: Unique_S(F,u), together with S(F,v), gives v=u;
* u comes from N and v from F: Safe_R(F,u), Ruv and Fv give v=u;
* u comes from F and v from N: Safe_R(F,v), Ruv and Fu give u=v.

Necessitate only this H theorem and combine it with P(F)'s existing boxed pair-safety assertion. Then generalize over actual u,v. This proves P(F)→P(gF), without □∀uv, BF, ND, or necessary Equiv(R).

## 4. Strict progress at every nonfull input

Suppose P(F) and ¬Full(F). Let x be S's unique actual value at F. Its containment in U gives Miss(F,x). Therefore Fx is false, by actual reflexivity of R.

Unique_S(F,x) holds by actual functionality. Safe_R(F,x) holds because actual symmetry makes either R-direction place an F-member in x's missed cell, which has none. Thus N(F,x), so (gF)x while ¬Fx. Consequently F≠gF. Together with F≤gF this gives F<gF.

Actual truth of either guard is never necessitated. The uniform implication in §3 is the only new boxed reasoning.

## 5. Why this does not imply Plenitude or Actuality

The output gF is a property whose extension adds the selected point actually. It is **not** asserted to be the rigid haecceity of that point, or to be identical to a separately chosen output entity of a graph. Away from the evaluation point, the guards can delete its new summand. Thus g need not represent the original selected graph as an operation.

Nor is g required to identify actually coextensive inputs or even send them to actually coextensive outputs. Different intensions of the same actual partial selector can receive different S-values. This is still the obstacle to a straightforward RC-alone transfinite construction using ordinary actual unions as limit stages.

## 6. Resulting location of the RC-alone obstruction

A failed TC instance plus this RC instance would supply a represented algebraically progressive operation g on P which is strict everywhere on P. The union of all g-chains from the fixed-point construction is an internally well-ordered chain of P-members with no ambient algebraic supremum. The difficulty is therefore genuinely at coherent limit formation. It cannot be attributed merely to the absence of a selected operation.

This also permits the BC proof's abstract fixed-point lemma to be stated for operations if desired, though the stronger already checked functional-graph version remains correct.
