# Relational atoms: projection, coordinates, and the exact collision relation

22 October 2026. Alternative ordinary mathematical proof by OpenAI Codex; direct source `misc`. No independent referee or formal verification claim. The original [world-representation note, §4, Theorem 2](../notes/structural-world-representation.md#4-atomic-normal-form-and-the-internal-truth-lemma) is preserved.

## Statement and improvement

The original theorem assumes T = C + □Plenitude and identifies the atoms at a relational type τ = σ₁…σₖt with pairs consisting of a proposition atom and an argument tuple.

The following factorization isolates much less machinery:

1. In **bare C**, existential projection sends every relational atom to a proposition atom. A world atom and a current tuple always produce a relational atom.
2. In bare C, a relational atom has such coordinates **iff it has a nonzero value at a current tuple**. The dual BF instance for that atom is sufficient. Thus BF for this argument tuple suffices to classify all atoms, without Atomicity, Actuality, Boolean Completeness, or Plenitude.
3. Before assuming ND, the exact collision relation is

   h(w,ā) = h(v,b̄) iff w = v and w ≤ (ā = b̄).

   ND at the argument types makes the coordinates unique. If Atomicity_t holds, uniqueness of these coordinates is conversely equivalent to ND for the tuple.

All conclusions concern the current domains and unboxed assumptions. No assumption is necessitated. For k = 0, the tuple is empty and the assertions reduce to the propositional case.

## 1. The scalar projection lemma

Write p↑ := λx̄.p and define the admitted terms

    π(X) := ∃x̄ X[x̄],
    h(p,ā) := λx̄. p ∧ (x̄ = ā).

These have relational output; no operation returning an individual is used. C proves

    π(h(p,ā)) = p,                  h(p,ā)[ā] = p,
    π(p↑ ∧ X) = p ∧ π(X),           X = ⊥τ iff π(X) = ⊥t.       (1)

The first and third identities follow from quantified propositional logic and reflexivity. The last follows from ∃x̄X[x̄] = ⊥ iff □∀x̄¬X[x̄], followed by Intensionality. Projection is order preserving, since necessary universal implication entails the corresponding necessary implication of existentials. These are C theorems, not applications of Logical Equivalence to optional hypotheses.

Let X be an atom and put w = π(X). By (1), w ≠ ⊥. If ⊥ ≠ p ≤ w, then

    π(p↑ ∧ X) = p ∧ w = p ≠ ⊥.

Thus p↑ ∧ X is a nonzero element below X and equals X. Projecting again gives p = w. Therefore w is an atom. This establishes the projection claim without BF or any Atomicity axiom.

## 2. Constructing and recovering coordinates

If w is a proposition atom, h(w,ā) is nonzero by evaluation at ā. For any current relation Y of type τ, w settles the proposition Y[ā]: either w ≤ Y[ā] or w ≤ ¬Y[ā]. Necessary Identity and substitution then give, respectively,

    h(w,ā) ≤ Y,                    h(w,ā) ≤ ¬Y.

Indeed, at every point where h(w,ā)[x̄] holds, x̄ = ā and w hold, so the chosen entailment determines Y[x̄]. A nonzero Boolean element deciding every current Y is an atom. This does not require w to settle future relations that are absent from the current domain.

Now let X be a relational atom with X[ā] ≠ ⊥ for some current ā. Set p = X[ā]. Substitution gives

    ⊥ ≠ h(p,ā) ≤ X,

so atomicity of this one element gives X = h(p,ā). Projecting and using (1) gives p = π(X). The scalar projection lemma already shows that p is a proposition atom. Consequently

    X = h(π(X),ā).                                           (2)

Conversely any h(w,ā) has nonzero value w at ā. This proves the exact current-witness criterion.

For a nonzero X, (1) gives ◇∃x̄X[x̄]. The single dual BF implication

    ◇∃x̄X[x̄] → ∃ā◇X[ā]                                  (3)

therefore supplies precisely the witness needed in (2). Full BF, C5, and boxed Plenitude are each sufficient but unnecessary packages. The proof needs only (3) for each atom being classified. In particular, the unboxed polyadic BF principle at σ̄ suffices; one need not derive that polyadic principle from separately assumed, unboxed unary BF instances.

## 3. Collision and uniqueness

Suppose h(w,ā) = h(v,b̄), with w,v atoms. Projection gives w = v. Evaluation at ā gives w = v ∧ (ā = b̄), so w ≤ (ā = b̄).

Conversely suppose w = v and w ≤ (ā = b̄). Under w, the two tuple equalities x̄ = ā and x̄ = b̄ are necessarily equivalent, by substitution. Hence the two h-relations are necessarily coextensive and are identical by Intensionality. This proves the collision formula in the statement.

If the tuple ND principle holds and ā ≠ b̄, then □(ā ≠ b̄). A nonzero w cannot be below both tuple equality and its negation. Thus coordinates are unique. ND for each of the finitely many argument types implies this tuple ND principle directly.

Conversely, suppose Atomicity_t holds and the map (w,ā) ↦ h(w,ā) is injective on atom–tuple pairs. If ◇(ā = b̄), Atomicity_t supplies an atom w ≤ (ā = b̄). The collision formula gives h(w,ā) = h(w,b̄), whence ā = b̄. This is the dual of tuple ND. Neither BF nor relational Atomicity is used in this converse.

The word “quotient” can describe the collision relation, but no new quotient object or quotient-choice operation has been constructed. The displayed formula itself is the complete assertion.

## 4. Atomicity transfers with local BF

As a useful consequence, polyadic BF at σ̄ plus Atomicity_t implies Atomicity_τ. Given X ≠ ⊥, (3) gives ā with X[ā] ≠ ⊥; choose one atom w ≤ X[ā]. Then h(w,ā) is an atom below X. No ND is needed.

Conversely Atomicity_τ implies Atomicity_t in C. For p ≠ ⊥, choose a single current tuple ā, using the standing nonempty types and only finitely many existential choices. Then h(p,ā) ≠ ⊥. An atom X below it projects to an atom π(X) ≤ p. For the empty tuple the assertion is immediate.

Thus, under this polyadic BF principle, Atomicity at τ and at t are equivalent. The construction in §2 already classifies all atoms even when neither algebra is atomic.

## Dependencies and boundary

The full Cartesian-product classification now needs only C + polyadic BF at the argument tuple + tuple ND. The two optional premises are genuinely weaker in scope than the original all-type □Plenitude package; no strict separation of these exact local packages is claimed here. Replacing BF by the current-witness condition is an exact criterion, not a claim that the criterion follows in C.

This refinement does not weaken the assumptions of the original **entire** encode/decode or Gallin-representation theorems. Their closure and modal obligations remain in the original note. It improves the atomic normal form used by those theorems and by the probability type-factorization theorem.

Background records: `classicism-implies-intensionality-r` (Classicism, draft 16 May 2023, §1.5, pp. 17–18); `classicism-implies-identity-necessary-r` (§2.1, p. 22); the definitions/dual forms in `barcan-r`, `distinctness-necessary-r`, and `atomicity-r` (§2.1, pp. 20–22; §2.2, p. 24). Those sources supply background only; the proof above is this note's alternative argument.
