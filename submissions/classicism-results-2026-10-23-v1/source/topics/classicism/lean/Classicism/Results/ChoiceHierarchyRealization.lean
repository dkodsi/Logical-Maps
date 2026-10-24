import Classicism.ChoiceHierarchyRealizationSteps

/-!
# Realizing the type budget and the cofinal selector hierarchy

This file performs the structural induction on the actual relational type
syntax. The premise is the single, explicit boxed Plenitude instance at t,t.
It supplies the boxed Functionality used in each graph step. The recursion
constructs a derivation of an existential injection at the computed level;
there is no assumed embedding-existence or schema-cofinality hypothesis.

Combining the construction with the exact Plenitude and selector rules gives
cofinality of the ascending selector stages in all-type boxed Functional
Choice. Strictness and nonfinite axiomatizability still require the separate
countermodel constructions and are not asserted here.
-/

namespace Classicism.Meta.ChoiceHierarchy

open AxiomSet
open Classicism.ChoiceHierarchyRealizationSteps

/-- Raise an already constructed injection by iterating haecceity coding.
The natural-number induction is in the metalanguage, not a new C rule. -/
theorem raiseEmbedding (Ax : AxiomSet Signature.pure) (σ : Ty) {i j : Nat}
    (hij : i ≤ j) :
    Theorem (C.axioms ∪ Ax) (NecEmbedding.quoted σ (tower i)) →
    Theorem (C.axioms ∪ Ax) (NecEmbedding.quoted σ (tower j)) := by
  induction hij with
  | refl => exact fun h => h
  | @step j _ ih =>
    intro h
    exact (Theorem.ofC (necEmbedding_lift.rule σ (tower j))).mp (ih h)

mutual
  /-- Every closed original type embeds at the explicit recursive budget.
  This includes individual inputs but never an individual operation output. -/
  theorem typeEmbedding : ∀ (σ : Ty), σ.Closed →
      Theorem (C.axioms ∪ plenitudeBase)
        (NecEmbedding.quoted σ (tower (embeddingBudget σ)))
    | .e, _ => Theorem.ofC necEmbedding_e.rule
    | .rel ρ, hρ => relationalEmbedding ρ hρ
    | .var _, h => False.elim h

  theorem relationalEmbedding : ∀ (ρ : RTy), ρ.Closed →
      Theorem (C.axioms ∪ plenitudeBase)
        (NecEmbedding.quoted (.rel ρ) (tower (relEmbeddingBudget ρ)))
    | .t, _ => Theorem.ofC necEmbedding_t.rule
    | .arr σ ρ, h => by
      let k := max (embeddingBudget σ) (relEmbeddingBudget ρ)
      have hi : Theorem (C.axioms ∪ plenitudeBase)
          (NecEmbedding.quoted σ (tower k)) :=
        raiseEmbedding plenitudeBase σ
          (Nat.le_max_left (embeddingBudget σ) (relEmbeddingBudget ρ))
          (typeEmbedding σ h.1)
      have hj : Theorem (C.axioms ∪ plenitudeBase)
          (NecEmbedding.quoted (.rel ρ) (tower k)) :=
        raiseEmbedding plenitudeBase (.rel ρ)
          (Nat.le_max_right (embeddingBudget σ) (relEmbeddingBudget ρ))
          (relationalEmbedding ρ h.2)
      exact ((Theorem.ofC (necEmbedding_graph.rule σ ρ (tower k))).mp₂ hi hj).mp
        (plenitudeBase_functionality σ ρ)
end

/-- A selector stage supplies the selector at each closed output type whose
recursive embedding budget is that stage. Every optional premise is boxed. -/
theorem stage_selects (ρ : RTy) (hρ : ρ.Closed) :
    Theorem (C.axioms ∪ selectorStage (relEmbeddingBudget ρ))
      (Classicism.ChoiceHierarchy.NecSelector.quoted ρ) := by
  let n := relEmbeddingBudget ρ
  have hi : Theorem (C.axioms ∪ selectorStage n)
      (NecEmbedding.quoted (.rel ρ) (tower n)) :=
    Derivable.cut (selectorStage_entails_plenitudeBase n) (relationalEmbedding ρ hρ)
  have hp : Theorem (C.axioms ∪ selectorStage n)
      (P.NecPlenitude.quoted (.rel (tower n)) ρ) :=
    Derivable.cut (selectorStage_entails_plenitudeBase n)
      (plenitudeBase_plenitude (.rel (tower n)) ρ (tower_closed n) hρ)
  have hs : Theorem (C.axioms ∪ selectorStage n)
      (Classicism.ChoiceHierarchy.NecSelector.quoted (tower n)) := Theorem.ax rfl
  exact ((Theorem.ofC (necSelector_of_necEmbedding_plenitude.rule ρ (tower n))).mp₂ hi hp).mp hs

/-- Every fixed original FC instance is supplied by an explicit selector
stage depending only on its output type. -/
theorem choice_at_output_stage (σ : Ty) (ρ : RTy) (_hσ : σ.Closed) (hρ : ρ.Closed) :
    Theorem (C.axioms ∪ selectorStage (relEmbeddingBudget ρ))
      (P.NecFunctionalChoice.quoted σ ρ) :=
  (Theorem.ofC (Classicism.ChoiceHierarchy.necFunctionalChoice_of_necSelector.rule σ ρ)).mp
    (stage_selects ρ hρ)

theorem allStages_entails_fullChoice : allStages ⟹ P.NecFunctionalChoice.schema := by
  rintro a ⟨σ, ρ, hσ, hρ, rfl⟩
  exact Derivable.mono
    (fun b hb => hb.elim Or.inl (fun hs => Or.inr ⟨relEmbeddingBudget ρ, hs⟩))
    (choice_at_output_stage σ ρ hσ hρ)

theorem fullChoice_entails_allStages : P.NecFunctionalChoice.schema ⟹ allStages := by
  rintro a ⟨n, hn⟩
  change a = Classicism.ChoiceHierarchy.NecSelector.quoted (tower n) at hn
  subst a
  exact (Theorem.ofC
    (Classicism.ChoiceHierarchy.necSelector_of_necFunctionalChoice.rule (tower n))).mp
    (Theorem.ax ⟨.rel (.arr (.rel (tower n)) .t), tower n,
      ⟨tower_closed n, trivial⟩, tower_closed n, rfl⟩)

/-- The exact finitary cofinality claim: a theorem of all-type boxed Choice
is already a theorem of one finite selector stage, and conversely. -/
theorem fullChoice_theorem_iff_stage (p : Sentence Signature.pure) :
    Theorem (C.axioms ∪ P.NecFunctionalChoice.schema) p ↔
      ∃ n, Theorem (C.axioms ∪ selectorStage n) p := by
  constructor
  · intro h
    exact theorem_at_selector_stage (Derivable.cut allStages_entails_fullChoice h)
  · rintro ⟨n, hn⟩
    exact Derivable.cut (fun a ha => fullChoice_entails_allStages a ⟨n, ha⟩) hn

end Classicism.Meta.ChoiceHierarchy
