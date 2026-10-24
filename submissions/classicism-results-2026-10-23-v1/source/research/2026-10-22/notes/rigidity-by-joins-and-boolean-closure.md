# Rigidity by joins and Boolean closure

Research note, 22 October 2026. New arguments and formulations from the principles lane, with independent checks and related closure proofs by the root and rigidity lanes. No database records have been changed; no Lean verification or literature novelty is claimed. Direct source category for these arguments: misc.

The general background and definitions are those of fixed Classicism C in the database. Related detailed notes are `.reproduction/classicism-research/maximalism-modal.md`, §§17–23, and `.reproduction/classicism-research/rigidity-actualization.md`. The existing results WeakRC⇒BC, WeakRC⇒Actuality, RC⇒TR, and ND+WeakRC⇒Plenitude are used below with their current proved status. The last is the recorded weakening of Bacon–Dorr Proposition 2.16, p.33 n.49.

Fix a relational type τ=σ̄t. Write F≤G for necessary inclusion, δ_ā for the tuple haecceity, and H_F(Y):=∃ā(F(ā)∧Y=δ_ā). Families and joins always refer to current members of admitted relations. Optional hypotheses are never automatically boxed.

## 1. Reconstruction from current singletons

C proves δ_ā≤Z iff □Z(ā). Therefore

    WeakRigid(F) iff LUB(F,H_F),
    Rigid(F) iff □LUB(F,H_F).

The upper-bound half of the first equivalence is weak persistence. The least-upper-bound half is exactly weak inextensibility. This requires no Boolean Completeness: it asserts existence of this particular join, with F as its value. Rigidity means that the same reconstruction remains valid at every reached world, using the instances current there.

## 2. Existing joins preserve weak rigidity

Suppose Z=LUB(H) and every current H-member Y is weakly rigid. Each Y is fully persistent in C. From Y≤Z one consequently gets Y≤λā.□Z(ā). Leastness gives Z≤λā.□Z(ā), so Z is persistent.

If a test W is necessary of every current Z-instance, it is necessary of every current Y-instance for each current H-member. WI(Y) gives Y≤W; leastness then gives Z≤W. Thus Z is weakly inextensible and hence weakly rigid.

The indexing family H itself need have no rigidity. The same proof separately establishes closure of persistent relations and of weakly inextensible relations under existing joins.

It follows that

    TR_τ iff every existing admitted join of rigid τ-relations is rigid.

The forward direction uses the preceding lemma and TR. Conversely every weakly rigid F is the existing join of its current singleton family, whose members are rigid, so rigid-join closure makes F rigid. This is exact without BC; under BC it is ordinary arbitrary admitted-join closure of the rigid fragment.

## 3. ND is precisely ambient intersection closure

Assume ND at the argument types σ_i. If B is weakly rigid and ¬B(ā) currently, every current B-tuple b̄ is necessarily distinct from ā. WI(B), with the test b̄≠ā, gives □¬B(ā). Positive membership is already necessary by weak persistence. Thus every current tuple has its B-membership decided.

For weakly rigid A,B, weak persistence of A∩B is immediate. If a test Z is necessary on its current members, every current A-tuple either belongs to B and necessarily satisfies Z, or necessarily fails B. Hence each current A-tuple necessarily satisfies B→Z, and WI(A) yields A∩B≤Z. This proves A∩B weakly rigid. Reversing the B-cases proves A\B weakly rigid; its weak persistence uses the stable negative B-membership just established.

For rigid A,B, let D_B(ā):=□B(ā)∨□¬B(ā). Current A-tuples satisfy this persistent predicate, so WI(A) gives A≤D_B. At every reached world the same decided-cut argument applies using WI(A) there. Thus A∩B and A\B are rigid.

Conversely, if distinct a,b have rigid (or merely weakly rigid) haecceities whose intersection is weakly rigid, that intersection is actually empty and hence equals bottom, by uniqueness of coextensive weakly rigid relations. Consequently □a≠b. The relative-difference version similarly uses the difference of two haecceities: when a≠b, η_a\η_b is actually coextensive with η_a, so weak-rigidity uniqueness identifies them; future a=b would make the difference empty but η_a nonempty. Tuple arguments localize these observations to the relevant coordinate types, using fixed fillers in the other positions.

Thus, as all-type schemata, each of the following is equivalent to ND:

- weakly rigid relations are closed under binary intersection;
- weakly rigid relations are closed under relative difference;
- rigid relations are closed under binary intersection;
- rigid relations are closed under relative difference.

The nullary instance alone is trivial and does not imply ND; the reverse all-type argument uses unary haecceities at each desired argument type.

## 4. Actuality makes represented joins pointwise current unions

Let w be a true proposition entailing every true proposition, as supplied by Actuality. If Z=LUB(H), then at every current tuple ā,

    Z(ā) iff ∃X(HX∧X(ā)).

The reverse implication is the upper-bound condition. For the forward implication suppose Z(ā) but no current H-member holds of ā. For each such X, Actuality gives w≤¬X(ā). Hence X≤¬(c(w)∧δ_ā), where c(w)=λb̄.w. The join has the same upper bound, contradicting the current w∧Z(ā). No ND or BF is used in this lemma.

This is a statement about a represented Boolean join, not a general interchange of quantifiers and □.

## 5. The weak and rigid fragments are Boolean intervals

Under WeakRC, let W_τ be the current weakly rigid τ-relations. The proved consequences BC and Actuality are available. Fix a true actual-world proposition w. Then

    L: W_τ → [bottom,c(w)],       L(Y)=c(w)∧Y

is an order isomorphism.

Surjectivity: for X≤c(w), choose a weakly rigid Y actually coextensive with X. Actuality applied to the true sentence ∀ā(X(ā)↔Y(ā)) gives c(w)∧Y=c(w)∧X=X.

Order reflection: if c(w)∧Y≤c(w)∧Z, then Y⊆Z currently because w is true. Persistence of Z makes it necessary of every current Y-instance, so WI(Y) gives Y≤Z. Order preservation is Boolean algebra. Injectivity follows from order reflection, or directly from uniqueness of coextensive weakly rigid relations.

Thus W_τ is an admitted-complete Boolean algebra as an ORDERED FRAGMENT. Its joins coincide with ambient Boolean joins by section 2 and BC. Its greatest member U_τ is the unique weakly rigid coextension of top; every weakly rigid Y is below it by WI(Y) and persistence of U_τ. Its meets and complements need not be ambient meets and relative complements without ND.

Under RC the same construction works for the current rigid fragment R_τ. RC gives TR, so all represented ambient joins of rigid members are rigid. It too is order-isomorphic to [bottom,c(w)], with unit the rigid coextension U_τ of top.

Under ND, section 3 shows that the fragment's meets and relative complements ARE ambient meets and complements relative to U_τ. Hence ND+WeakRC, respectively ND+RC, makes the weak, respectively rigid, fragment a complete Boolean subalgebra of the ambient interval [bottom,U_τ]. The unit U_τ can be properly below ambient top; no BF is concluded.

These order-theoretic statements alone do not identify the PROPERTY collecting the fragment with a rigid property. The subsequent proof in `.reproduction/classicism-research/nd-rigid-comprehension-implies-weak-power.md` closes that gap under ND+RC, using necessary internal distinctness and the fact that ND forbids new persistent truths. Thus ND+RC implies WRP; the unrestricted TR+RP conjecture remains open.

## 6. Uniform rigidification and complete Boolean retractions

Let UniformWeakRC_τ assert an admitted operation R:τ→τ uniformly choosing the weakly rigid coextension of each current relation; UniformRC_τ uses rigid coextensions.

Even one such instance gives Boolean evaluation. Set U=R(top_τ), choose a current tuple ā, and put E(p)=R(c(p))(ā). If p is true, uniqueness makes R(c(p))=U, and U(ā)=top by weak persistence. If p is false, its representative is bottom. Thus E maps every current true proposition to top and every false proposition to bottom. This is the Boolean-evaluation principle, equivalent to ND+Actuality. For the ND direction, if a≠b then E(a=b)=bottom while E(top)=top; these identities are necessary, and future a=b would give the contradiction bottom=top.

Conversely ND+WeakRC implies Plenitude by the recorded theorem. The total single-valued relation saying that Y is the weakly rigid coextension of X is therefore represented by an operation. The rigid case is identical. Consequently, as full schemata,

    UniformWeakRC iff ND+WeakRC,
    UniformRC iff ND+RC.

No converse from only a single unboxed comprehension instance is claimed.

The uniform R is idempotent and fixes every member of its range. Section 3 and uniqueness give

    R(X∨Y)=R(X)∨R(Y),     R(X∧Y)=R(X)∧R(Y),
    R(¬X)=U_τ\R(X),       R(bottom)=bottom.

It also preserves every represented admitted join. If Z=LUB(H), section 4 makes Z actually coextensive with the current union of H. The join of the represented image family {R(X):HX} is weakly rigid by section 2 (rigid under RC), and section 4 gives it the same current extension as R(Z). Uniqueness identifies them. Thus R is a complete Boolean-algebra retraction onto the relevant fragment, with unit U_τ.

Its kernel is exactly the actually empty relations, equivalently the ambient interval below c(¬w): Actuality applied to ∀ā¬X(ā) proves X≤c(¬w), and the converse is immediate because w is currently true. The restriction of R to [bottom,c(w)] is inverse to L above.

All displayed operation equations are identities, hence necessary for each fixed tuple of current arguments. Their universal closures are not boxed without additional assumptions. New future arguments prevent deducing the power principle merely by boxing this retraction law. The separate internal-distinctness argument in the companion note supplies the missing reasoning and proves WRP under ND+RC.
