# The Boolean closure ladder for rigid relations

Research proof, 22 October 2026. New deductions in the fixed Classicism framework; literature novelty is unchecked. No database record has been edited and no formal verification is claimed. A narrow search of the existing principle/result records for rigid complement, intersection and negation closure found no record of these equivalences. The open-question discussion of Rigid Rigidity=>Rigid Power mentions C5 as a sufficient condition for conjunction closure; the result below identifies the exact weaker assumption.

Use the database definitions: WeakRigid(F) means weak persistence and weak inextensibility; Rigid(F) means their necessary version. In C, weak rigidity implies persistence, coextensive weakly rigid relations are identical, and identity entails necessary identity. Sources for these background facts are the topic's `background.md`, the recorded proof of `rigid-comprehension-implies-tame-rigidity`, and the defining rigidity records. All new closure arguments below have source category `misc`.

## 1. A cut lemma

Write

    D_B(x) := box Bx or box not Bx.

If A is rigid and A<=D_B, then A∧B and A∧not B are rigid. The premise A<=D_B is a necessary pointwise implication, so it remains available at every reached world, as does rigidity of A.

At any such world, A∧B is weakly persistent: an actual member has persistent A-membership, and D_B plus B supplies box B. For weak inextensibility, suppose every current A∧B member necessarily satisfies Z. Consider a current A-member x. If Bx, the hypothesis gives box Zx. If not Bx, D_B gives box not Bx. In either case box(Bx→Zx). Weak inextensibility of A applied to B→Z therefore gives A<=B→Z, which is A∧B<=Z. The same proof with B negated gives A∧not B. Since it applies at every reached world, both cuts are rigid.

No Barcan principle is used. The critical requirement is that B be decided on every possible A-member, not merely on the actual members.

## 2. ND gives stable membership on current arguments

Fix an argument type σ and assume ND_σ. Let B^(σt) be rigid and let a be an actual nonmember. Every actual B-member x differs from a, hence necessarily differs from a by ND_σ. Weak inextensibility of B, tested on λx.x≠a, gives

    B<=λx.x≠a,

and consequently box not Ba. Positive membership is necessary by persistence. Thus

    forall a (Ba→box Ba) and (not Ba→box not Ba)

holds for every rigid B. For a finite argument tuple, the same argument uses ND at each component, which gives necessary tuple-distinctness.

Now take rigid A,B of this relation type. Every actual A-member satisfies D_B. Moreover each such decision is necessary by modal axiom 4. Weak inextensibility of A therefore gives A<=D_B. The cut lemma proves that A∧B and A∧not B are rigid. This is the step that seals the actual decisions inside the rigid bound A; simply assuming that the current pointwise decisions hold of every future object would be invalid.

## 3. Exact typewise equivalences

For every argument type σ, the following unboxed statements are equivalent over C:

1. ND_σ.
2. Rigid properties of σ-objects are closed under binary intersection.
3. Rigid properties of σ-objects are closed under relative difference.
4. Rigid properties of σ-objects are closed under symmetric difference.

Section 2 gives (1)=>(2),(3). Rigid relations are always closed under finite union in C: at every world, a test necessarily true of all members of A∨B is necessarily true of every A-member and every B-member, so the weak-inextensibility tests for A and B give the union test. Hence (3) gives symmetric-difference closure.

For (2)=>(1), let a≠b and intersect their rigid haecceities. The intersection is actually empty, and if rigid is identical to bottom because coextensive weakly rigid relations are identical. It is therefore necessarily empty. A future identification a=b would put a in the intersection, a contradiction. Thus box(a≠b).

For (3)=>(1), a belongs actually to η_a\η_b when a≠b. If that difference is rigid, persistence makes this membership necessary, which prevents a=b at any future point. The same argument applies to η_a symmetric-difference η_b, giving (4)=>(1).

These are instancewise claims: the closure principle is at relation type σt, while the corresponding distinctness principle is at argument type σ. At an arbitrary nonempty tuple type, closure is equivalent to ND at all its component types, using tuple haecceities; to recover one component, fix arbitrary values of the others. The nullary case t is trivial in C and gives no ND assumption: its rigid elements are just bottom and top.

Thus ND says precisely that rigid relations are closed under the finite Boolean operations that do not require taking an ambient complement. They contain bottom and are always closed under finite union; with ND they also close under intersection, relative complement and symmetric difference. The ambient top relation need not itself be rigid.

## 4. Complement closure is exactly C5

There is a useful exact typewise form. Let CC_(σt) mean that the ambient complement of every rigid property of σ-objects is rigid. Then

    CC_(σt) iff ND_σ and box BF_σ.

For the forward direction, bottom is rigid in C, so its complement top is rigid. Weak inextensibility of top is exactly BF_σ; rigidity of top is exactly box BF_σ. Complement closure together with the C-theorem of finite-union closure gives intersection closure by De Morgan, hence ND_σ by section 3.

Conversely ND_σ gives relative-difference closure, and box BF_σ says that top is rigid. Therefore top\F, the ambient complement of F, is rigid whenever F is.

At all types this yields the compact characterization

    C5 iff rigid relations are closed under ambient complementation.

Indeed C5 supplies boxed BF and ND at every type. In the reverse direction, complement closure supplies ND and BF; the recorded ND_t+BF_t route gives boxed ND_t and then boxed ND at every type, which is C5. In fact complement closure only at type tt, the rigid properties of propositions, already suffices: it gives ND_t and BF_t. Conversely C5 gives complement closure at every relation type.

Similarly, intersection, difference, or symmetric-difference closure only at tt already gives ND_t and therefore ND at every type by the recorded propositional-to-all-types transfer. The full closure schema is therefore controlled by this one low type.

The distinction between ND and C5 is substantive. Intersection and relative-complement closure are already available under unboxed ND. Ambient complement closure additionally requires that the ambient universal relation be rigid, equivalently boxed BF at that argument type. No inference that arbitrary conjunctions are rigid has been made.

## 5. Consequence for simpler formulations

For a rigid F, unboxed ND alone gives the pointwise bivalence formula

    forall x (Fx=top or Fx=bottom).

The usual C5 equivalence between rigidity and pointwise bivalence uses stronger assumptions in the reverse direction. It should therefore be stated with its direction visible: ND suffices to make every rigid relation pointwise bivalent on current arguments; C5 makes pointwise bivalence characterize rigidity.

The closure ladder provides a direct algebraic presentation of the modal strengthening: necessary distinctness is exactly closure of rigid relations under finite intersections, and C5 is exactly closure under complements. This does not alter the database's definitions; it supplies conditional equivalent formulations.

## 6. The same finite-operation characterization at the weak level

The principles lane independently observed that ND_σ is also equivalent to closure of **weakly rigid** properties of σ-objects under intersection, relative difference, or symmetric difference. The stable-nonmembership argument in section 2 uses only weak inextensibility of B and ND; positive membership uses the C-theorem that weak rigidity implies persistence. For weakly rigid A,B, the same two-case test on A proves weak inextensibility of A∧B and A∧not B directly, and weak persistence follows from the pointwise necessary memberships. The reverse haecceity arguments are unchanged: an actually empty weakly rigid relation is bottom, and a weakly rigid difference is weakly persistent. Finite-union closure also holds at the weak level by the same two-tests argument.

At the weak level, ambient complement closure has the typewise form

    weak-complement closure at σt iff ND_σ and BF_σ.

Forward, complementing bottom makes top weakly rigid, which is BF_σ; De Morgan gives weak intersection closure and hence ND_σ. Reverse, BF_σ makes top weakly rigid and ND_σ gives weak relative-difference closure, so top\F is weakly rigid. At tt this again implies C5 by the recorded ND_t+BF_t theorem; consequently the full weak-complement and full rigid-complement closure schemata are equivalent to the same C5 preset, although their isolated typewise BF clauses differ by a box.

## 7. Pointwise bivalence and section closure also characterize ND

There are two further exact simplifications. At an argument type σ,

    ND_σ iff every rigid σ-property has only top/bottom instance values,
         iff every weakly rigid σ-property has only top/bottom instance values.

The forward direction is section 2 (whose proof uses only weak rigidity). Conversely apply either claim to the rigid haecceity η_b at a. If a≠b, the false identity proposition η_b(a) must be bottom, so the distinctness is necessary. This is a characterization of ND, not C5.

More generally ND makes **every section of every rigid relation rigid**, even though the original section argument in rigidity-actualization.md section 3 assumed C5. Here is the stronger proof. Fix a rigid R(x,ybar) and an actual parameter a of the x-type. Every current R-tuple necessarily decides x=a by ND. As in section 2, weak inextensibility of R seals this decision throughout R. The cut lemma therefore makes

    R(x,ybar) and x=a

rigid. Existential projection preserves rigidity in C: if every actual projected member necessarily satisfies Z, every actual member of the original relation necessarily satisfies the same Z with the forgotten coordinates ignored; weak inextensibility gives the required entailment, at every reached world. Projecting x from the cut gives exactly R(a,ybar), so this section is rigid. Iterate to fix any finite tuple of arguments.

The weak version follows directly from the two-case weak-inextensibility test using ND, and existential projection also preserves weak rigidity in C.

Thus the full schema saying that rigid relations are closed under sections is equivalent to ND; the same is true at the weak level. The reverse direction already follows by taking nullary sections of unary haecceities, as above. Closure under one specified section fixing an argument of type σ needs only ND_σ in the forward direction, regardless of the remaining argument types.

This gives an operational reading: ND is exactly what makes application of a rigid relation to a fixed argument stay within the rigid relations. BF is not needed for this closure result.
