# The exact choice obstruction in the symmetric model

22 October 2026. New ordinary argument by OpenAI Codex; direct source `misc`. Mathematical self-audit only; no human or formal verification. This concerns the new construction in `central-map-complete-gluing.md`, not any original pinned-model record.

## A single proposition-to-proposition relation fails selection

The symmetric model satisfies full BC and fails Actuality. Its failure of Relational Choice is already witnessed at input and output type t, not only by the two-element-family example at input type tt. The witness is the pure relation proposed in `choice-completeness-actuality.md`, §8:

    W(b,x) := (b≠⊤ ∧ ¬x ∧ x≰b) ∨ (b=⊤ ∧ x=⊥).

It is serial. In general C, under ¬Actuality every nonzero proposition has a nonzero actual falsehood below it: if it is already false use itself; if true, intersect it with the complement of a truth it fails to entail. Apply this to ¬b when b≠⊤. At b=⊤ use ⊥.

Here is a direct construction-specific proof that no admitted actual functional subrelation of W exists. It does not depend on the Choice chat's fixed-point argument.

## 1. Stabilizer support equals pinning support

Retain U of cardinality κ⁺ and the support bound κ. Write M=K×Surj(U), allowing any of the first factors from the model note. If an admitted relational entity F is fixed by every permutation π fixing N pointwise, |N|≤κ, then N is a pinning support for F.

To prove this, let P be any existing support of F, and let s,t be surjections agreeing on N. Choose a permutation π fixing N and moving P\N disjointly off P∪N. Prescribe a surjection u by

    u|P=s|P,              (uπ)|P=t|P.

The prescriptions agree on their overlap P∩N and concern at most κ arguments; extend them to a surjection using the κ⁺ unused arguments. For every k∈K, pinning and π·F=F give

    F_(k,s)=F_(k,u)=F_(k,uπ)=F_(k,t).

Thus N supports F. The converse is immediate from the transport formula. This lemma concerns equality of whole entities under the stabilizer, not merely invariance of their actual extensions.

## 2. Each support fragment has its own truth atom

For N⊆U with |N|≤κ, define the admitted proposition

    a_N(k,s) ⇔ k=1_K and s|N is injective,
    b_N := ¬a_N.

These profiles are N-supported and symmetric. The proposition a_N is actually true, so b_N≠⊤.

Every actually false N-supported proposition x satisfies x≤b_N. Indeed, at a coordinate (1_K,s) where s|N is injective, choose a permutation ρ with (ρs)|N=id|N. Such a permutation extends the indicated inverse partial bijection, whose domain and range have size at most κ. Left symmetry and pinning give

    x_(1_K,s)=x_(1_K,ρs)=x_(1_K,id)=false.

Thus x vanishes wherever a_N holds. Dually a_N entails every actually true N-supported proposition. It is an actuality witness for that support fragment, although it is not a global actuality witness. Fresh pairs outside N still split it.

The fragment has an exact Boolean-algebra description. Write Eq(N) for the set of equivalence relations on N. The algebra of all N-supported propositions is

    P(K×Eq(N)),

under the identification (k,s)↦(k,ker(s|N)). If two restricted surjections have the same kernel, the bijection between their images extends to a permutation of U, so symmetry and pinning identify their proposition values. Conversely any subset of K×Eq(N) defines an admitted profile, and every equivalence relation on N is realized by a surjection of U. The atom a_N corresponds to the singleton (1_K,equality_on_N).

For N⊆P, inclusion of fragments is inverse image along restriction Eq(P)→Eq(N). Consequently the actual atom of the smaller fragment splits when the support grows. The global proposition algebra is the directed union of these complete atomic fragments and is atomless. This description is about this particular all-surjections construction; arbitrary pinned models need not have these extension and symmetry properties.

## 3. A selector is trapped by its own support

Suppose R⊆W is an admitted actual functional relation, and let N support R. The actual extension of R is invariant under every permutation fixing N: pinning gives R_π=R_1, while symmetry gives R_π=π·R_1.

The input b_N is fixed by every such permutation. Therefore its unique selected output x is also fixed by all of them. Section 1 makes x N-supported. But R⊆W requires x to be actually false and x≰b_N. Section 2 instead gives x≤b_N, a contradiction.

This proves failure of the exact local RC_(t,t) instance needed by the Choice chat's theorem. There is no appeal to unrestricted constant graphs: those would destroy the symmetry restriction and are not admitted.

## 4. The obstruction is stronger than failure of single-valued choice

Let R⊆W be any admitted actually total relation, and let N support R. Its row E at b_N is invariant under the pointwise stabilizer of N. If |E|≤κ externally, the pointwise union p=⋃E of its proposition profiles is admitted: the union of their supports still has size at most κ, and symmetry is preserved. Invariance of E gives π·p=p for every π fixing N, so §1 makes p N-supported.

Every member of E is actually false, so p is false. Section 2 gives p≤b_N, contradicting x≤p and x≰b_N for any member x of this nonempty row. Hence

    every admitted total R⊆W has |R(b_N,-)|>κ
    at the input determined by any support N of R.

This is an external cardinal statement about the construction, not a new internal cardinality axiom. It applies in particular to finite-valued selectors. Enlarging the support allowance merely moves the obstruction to the next cardinal.

There is also an algebraic description. BC supplies the Boolean join j of the represented row E. Its uniqueness and the stabilizer's order automorphisms make j invariant under that stabilizer, hence N-supported by §1. If j were false, §2 would give j≤b_N, again contradicting an E-member. Therefore j is actually true although every E-member is actually false. This is exactly where algebraic join and actual material union separate.

## 5. Interaction with the disjoint-refinement argument

The disjoint-join reflection lemma in `choice-completeness-actuality.md`, §2, was rechecked here. Its use of BC at tt is essential: it joins the haecceities of an actual disjoint family, then uses the evaluation/right-adjoint identity to preserve the relevant joins. The disjointness facts are positive identities and so persist by NI; no necessity of distinctness is used. Its final witness is obtained by actual quantifier duality, not by moving a quantifier through a box.

Consequently the row E from §4 cannot have a represented pairwise-disjoint refinement with the same Boolean join: such a refinement would consist of false propositions, but its join would be true, contradicting that lemma. In particular E itself cannot be pairwise disjoint. This pinpoints the structural failure behind the missing selector: the model has joins, but cannot carry out the represented disjoint refinement which selection would supply.

The broader Choice ⇒ disjoint-refinement theorem also uses the canonical-chain portion of its saved fixed-point argument. That separate dependency is not certified by the present note. The direct support proof above already verifies the required RC_(t,t) failure in this model independently of that dependency.

There is a second, entirely model-specific check of disjoint-join reflection. Finite intersections of pinning supports are supports: for supports P,Q and surjections s,t agreeing on P∩Q, extend the compatible prescriptions u|P=s|P and u|Q=t|Q to a surjection, and compare the two profile values through u.

Let A:tt be N-supported, with actual members a false antichain E. If its join from the hull formula in `central-map-complete-gluing.md`, §2, were actually true, there would be p∈E and a surjection t fixing N with p_(1,t)=true. Take a support P⊇N of p and a permutation π fixing N and moving P\N disjointly off P. Since E is stabilizer-invariant, π·p∈E. Prescribe a surjection u with u|P=t|P and (uπ)|P=t|P; the prescriptions agree on N and extend. Both p and π·p are true at (1,u), so they overlap. They are distinct: otherwise p would have both supports P and πP, hence support N by the intersection observation, contradicting p_(1,t)=true and its actual falsity. This contradicts the antichain condition.

Thus the hull cannot make a represented false antichain's join true. Symmetry would duplicate any such new truth into two distinct overlapping members. This direct argument agrees with the abstract BC_(tt) reflection lemma and does not use the fixed-point or choice-to-refinement argument.

All arguments apply both to the singleton-individual construction and to its moving-individual variants, and to the cancellative and noncancellative choices of K. They do not assign any new verdict to the original pinned models.
