import Classicism.Results.ChoiceHierarchyRealization

/-!
# Diagonal Choice has the same deductive union

The diagonal schemas and stages are sets of original boxed sentences.
There is no type quantifier or infinitary conjunction in any such sentence.
These are positive entailment/cofinality results; strictness is deliberately
absent because it requires the independent countermodel constructions.
-/

namespace Classicism.Meta.ChoiceHierarchy

open AxiomSet Classicism.ChoiceHierarchy

def diagonalStage (n : Nat) : AxiomSet Signature.pure :=
  single (P.NecFunctionalChoice.quoted (.rel (tower n)) (tower n))

/-- The all-relational-type diagonal schema. Individual-valued operations
are excluded intrinsically by the `RTy` parameter. -/
def diagonalChoice : AxiomSet Signature.pure :=
  fun a => ∃ ρ : RTy, ρ.Closed ∧ a = P.NecFunctionalChoice.quoted (.rel ρ) ρ

theorem selectorStage_entails_diagonalStage (n : Nat) :
    selectorStage n ⟹ diagonalStage n := by
  intro a ha
  change a = P.NecFunctionalChoice.quoted (.rel (tower n)) (tower n) at ha
  subst a
  exact (Theorem.ofC
    (necFunctionalChoice_of_necSelector.rule (.rel (tower n)) (tower n))).mp
    (Theorem.ax rfl)

private theorem diagonal_predicate_reduct (σ : Ty) :
    single (P.NecFunctionalChoice.quoted
      (.rel (.arr (.rel (.arr σ .t)) .t)) (.arr (.rel (.arr σ .t)) .t)) ⟹
    single (NecSelector.quoted (.arr σ .t)) := by
  intro a ha
  change a = NecSelector.quoted (.arr σ .t) at ha
  subst a
  exact (Theorem.ofC (necDiagonal_selector_predicate.rule σ)).mp (Theorem.ax rfl)

theorem diagonalSuccessor_entails_selectorStage (n : Nat) :
    diagonalStage (n + 1) ⟹ selectorStage n := by
  cases n with
  | zero => exact diagonal_predicate_reduct .e
  | succ n => exact diagonal_predicate_reduct (.rel (tower n))

theorem diagonalStage_successor (n : Nat) :
    diagonalStage (n + 1) ⟹ diagonalStage n :=
  (diagonalSuccessor_entails_selectorStage n).trans
    (selectorStage_entails_diagonalStage n)

theorem diagonalStage_entails_of_le {i j : Nat} (h : i ≤ j) :
    diagonalStage j ⟹ diagonalStage i := by
  induction h with
  | refl => exact Entails.refl _
  | @step j _ ih => exact (diagonalStage_successor j).trans ih

theorem diagonalStage_subset (n : Nat) : diagonalStage n ⊆ diagonalChoice := by
  intro a ha
  change a = P.NecFunctionalChoice.quoted (.rel (tower n)) (tower n) at ha
  subst a
  exact ⟨tower n, tower_closed n, rfl⟩

theorem diagonal_subset_fullChoice : diagonalChoice ⊆ P.NecFunctionalChoice.schema := by
  rintro a ⟨ρ, hρ, rfl⟩
  exact ⟨.rel ρ, ρ, hρ, hρ, rfl⟩

theorem fullChoice_entails_diagonalChoice : P.NecFunctionalChoice.schema ⟹ diagonalChoice :=
  Entails.of_subset diagonal_subset_fullChoice

theorem diagonalChoice_entails_allStages : diagonalChoice ⟹ allStages := by
  rintro a ⟨n, hn⟩
  exact Derivable.mono
    (fun b hb => hb.elim Or.inl (fun hd => Or.inr (diagonalStage_subset (n + 1) b hd)))
    (diagonalSuccessor_entails_selectorStage n a hn)

/-- Full boxed FC is equivalent over C to just the diagonal schema. -/
theorem diagonalChoice_entails_fullChoice : diagonalChoice ⟹ P.NecFunctionalChoice.schema :=
  diagonalChoice_entails_allStages.trans allStages_entails_fullChoice

/-- Every theorem of all-type boxed Choice follows from one explicit
diagonal instance, at a finite stage, and conversely. -/
theorem fullChoice_theorem_iff_diagonalStage (p : Sentence Signature.pure) :
    Theorem (C.axioms ∪ P.NecFunctionalChoice.schema) p ↔
      ∃ n, Theorem (C.axioms ∪ diagonalStage n) p := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (fullChoice_theorem_iff_stage p).mp h
    exact ⟨n + 1, Derivable.cut (diagonalSuccessor_entails_selectorStage n) hn⟩
  · rintro ⟨n, hn⟩
    exact Derivable.mono
      (fun a ha => ha.elim Or.inl
        (fun hd => Or.inr (diagonal_subset_fullChoice a (diagonalStage_subset n a hd)))) hn

end Classicism.Meta.ChoiceHierarchy
