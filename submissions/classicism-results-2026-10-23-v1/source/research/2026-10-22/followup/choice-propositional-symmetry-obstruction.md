# A direct propositional choice obstruction in the symmetric surjection model

22 October 2026. New ordinary argument by OpenAI Codex, direct source `misc`, this note. Self-audited, not independently checked or formalized. The construction itself is the one in `central-map-complete-gluing.md`, §§1–2; that original note is unchanged.

## Claim and purpose

The symmetric surjection model already refutes Relational Choice at (tt,t) by a two-member property argument. It in fact refutes the lower input-type instance **RC_(t,t)**, using the single pure relation

    W(b,x) := [b≠⊤ ∧ ¬x ∧ x≰b] ∨ [b=⊤ ∧ x=⊥].

The proof below is direct. It uses neither Boolean Completeness nor the new RC+BC⇒Actuality proof. It therefore checks a sharper prediction of that proposed theorem by a different argument. It does not supply a countermodel to RC⇒TC: RC fails here.

## 1. Construction facts used

Work externally in ZFC. Fix infinite κ, |U|=κ⁺, a free monoid K (the original note calls it W), and the monoid M=K×Surj(U). Evaluation is at (1,id). A proposition is a truth-valued profile p(k,s) with a support L⊆U of size ≤κ: its value depends only on k and s|L. It also satisfies left-permutation symmetry

    p(k,πs)=p(k,s).

Relational profiles obey the corresponding equivariance on their lower-type arguments. Right translation gives transport. In particular permutations act as automorphisms of the actual typed structure. Every profile with the required support and symmetry is admitted. The word coordinate can be inspected arbitrarily; it is not subject to the pinning bound.

For a permutation π, the proposition entity π·p has profile (π·p)(k,s)=p(k,sπ). A graph supported by N is fixed as an entity by every π fixing N pointwise.

## 2. Support compression for invariant propositions

**Lemma.** If p is an admitted proposition entity fixed by every permutation fixing N pointwise, where |N|≤κ, then N itself supports p.

Let L be any support of p. Suppose s,t are surjections agreeing on N. Choose a permutation π fixing N and moving L\N off L. Then πL∩L⊆N. Choose a surjection r agreeing with s on L and satisfying rπ=t on L. The prescriptions agree on their overlap because s and t agree on N. Their combined domain has size at most κ, and the κ⁺ unprescribed arguments allow extension to a surjection.

For every k,

    p(k,s)=p(k,r)=p(k,rπ)=p(k,t).

The outer equalities use L-pinning; the middle equality uses π·p=p. This proves N-pinning. It does not assume an intersection-of-supports theorem or that N is finite.

Conversely, N-pinning plainly implies invariance under those right translations. Thus the fixed proposition entities of this pointwise stabilizer are exactly the N-supported propositions.

## 3. A largest false proposition in each fixed subalgebra

Define the admitted proposition

    b_N(k,s) := [k≠1 or s|N is not injective],
    a_N      := ¬b_N.

Both are N-supported and left-permutation invariant. At the evaluation point b_N is false and a_N is true. In particular b_N≠⊤. Both entities are fixed by every permutation fixing N pointwise.

Every **false N-supported** proposition p satisfies p≤b_N. To see this, the only case where b_N(k,s) is false has k=1 and s|N injective. Extend s|N to a permutation π of U; this is possible because both complements have cardinality κ⁺. Pinning and symmetry give

    p(1,s)=p(1,π)=p(1,id)=false.

Thus p has no true point outside b_N. Conversely b_N itself is false and N-supported, so it is the greatest false proposition in that fixed Boolean subalgebra. Dually a_N is its least actual truth, and an atom there: a nonzero element below a_N cannot be false, since every false element lies below its complement b_N.

This is only an atom in the stabilizer-fixed subalgebra. The global propositional algebra remains atomless, as proved in the source construction.

## 4. Seriality of the pure relation W

If b=⊤ use x=⊥. Otherwise choose a profile point (k,s) at which b is false, and a support L of b. Choose distinct u,v outside L. Let

    x(k',r) := [r(u)=r(v)].

This is an admitted proposition, supported by {u,v}, and false at (1,id). Extend s|L to a surjection r which collapses u,v. Then b(k,r) is still false while x(k,r) is true. Hence x≰b, and W(b,x). This proves seriality without invoking Actuality or the completeness theorem.

## 5. No admitted functional subrelation

Suppose S is an actually total functional subrelation of W, and let N support S. Apply it to b_N, obtaining its unique output x. Since b_N≠⊤, containment in W gives

    ¬x,                    x≰b_N.                       (1)

For every permutation π fixing N, both S and b_N are fixed entities. The automorphism property sends S(b_N,x) to S(b_N,π·x). Functionality therefore gives π·x=x. By §2, x is N-supported. Since x is actually false, §3 gives x≤b_N, contradicting (1).

Thus Serial(W) holds but W has no actual functional subrelation. The argument works with a singleton typed individual domain; U is only the external pinning set. It does not transfer the nonsymmetric model's constant-graph choice proof to this model.

## 6. An abstract stabilizer test for future constructions

The contradiction isolates a useful condition independently of this particular model. Suppose an actual automorphism subgroup H fixes a proposed selector S for W. If the H-fixed proposition entities have a greatest false member b with b≠⊤, then b is H-fixed, S's output at b must also be H-fixed, and W requires a false output not below b: impossible.

Consequently, in any model with ¬Actuality and a selector S for W, **no subgroup fixing S may have a principal actual-truth ultrafilter on its fixed propositional Boolean algebra**. Equivalently, there can be no H-fixed true u entailing every H-fixed actual truth: every H-fixed false proposition would then lie below ¬u, and the same argument applies to b=¬u. This is an external symmetry criterion, not an extra object-language axiom or a proof that every model has a useful automorphism group.

In the full symmetric pinning construction, a_N witnesses exactly this forbidden local principality for every possible support N. Merely allowing larger pinning sets does not remove the obstruction: the full domain still contains a_N for those sets. A smaller Henkin construction would have to avoid this local principal-truth phenomenon, as well as provide all the choice graphs and quantifier/lambda closure. Excluding a_N by fiat does not prove that closure or construct such a model.

The free monoid structure was not used here beyond an identity element and unrestricted dependence on its coordinate. The same proof works for the set-sized monoid variants described in the source note.
