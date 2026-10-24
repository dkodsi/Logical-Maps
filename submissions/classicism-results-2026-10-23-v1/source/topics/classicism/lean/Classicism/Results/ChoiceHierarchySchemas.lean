import Classicism.ChoiceHierarchy
import Classicism.Certified.Schemas
import Classicism.Syntax.ChoiceHierarchyTypes
import Classicism.Syntax.FiniteChoiceBasis

/-!
# The ascending selector stages as object-language axiom sets

The stage is the single original boxed sentence `□Sel_(A_n)`. This module
connects fixed-type certified rules with the actual C entailment relation.
It proves ascending inclusion and the finitary increasing-union theorem.
It does not prove strictness or that this union exhausts every FC instance;
the latter still needs the recursive encoding under boxed Plenitude.
-/

namespace Classicism.ChoiceHierarchy

def NecSelector (τ : Type) [Rel τ] : Prop := □ (Selector τ)

theorem necSelector_of_necFunctionalChoice {τ : Type} [Rel τ] :
    P.NecFunctionalChoice (τ → Prop) τ → NecSelector τ :=
  boxed_selector_of_boxed_functionalChoice

theorem necFunctionalChoice_of_necSelector {σ τ : Type} [Ty σ] [Rel τ] :
    NecSelector τ → P.NecFunctionalChoice σ τ :=
  boxed_functionalChoice_of_boxed_selector

theorem necSelector_down_predicate {σ : Type} [Ty σ] :
    NecSelector ((σ → Prop) → Prop) → NecSelector (σ → Prop) :=
  boxed_selector_down_predicate

theorem necSelector_prop_of_et : NecSelector (e → Prop) → NecSelector Prop :=
  boxed_selector_prop_of_selector_et

theorem necDiagonal_selector_predicate {σ : Type} [Ty σ] :
    P.NecFunctionalChoice ((σ → Prop) → Prop) ((σ → Prop) → Prop) →
      NecSelector (σ → Prop) := boxed_diagonal_selector_predicate

end Classicism.ChoiceHierarchy

#classicism_schema Classicism.ChoiceHierarchy.Selector Classicism.ChoiceHierarchy.NecSelector

#classicism_check
  Classicism.ChoiceHierarchy.necSelector_of_necFunctionalChoice
  Classicism.ChoiceHierarchy.necFunctionalChoice_of_necSelector
  Classicism.ChoiceHierarchy.necSelector_down_predicate
  Classicism.ChoiceHierarchy.necSelector_prop_of_et
  Classicism.ChoiceHierarchy.necDiagonal_selector_predicate

#classicism_types
  Classicism.ChoiceHierarchy.necSelector_of_necFunctionalChoice
  Classicism.ChoiceHierarchy.necFunctionalChoice_of_necSelector
  Classicism.ChoiceHierarchy.necSelector_down_predicate
  Classicism.ChoiceHierarchy.necSelector_prop_of_et
  Classicism.ChoiceHierarchy.necDiagonal_selector_predicate

#classicism_certify
  Classicism.ChoiceHierarchy.necSelector_of_necFunctionalChoice
  Classicism.ChoiceHierarchy.necFunctionalChoice_of_necSelector
  Classicism.ChoiceHierarchy.necSelector_down_predicate
  Classicism.ChoiceHierarchy.necSelector_prop_of_et
  Classicism.ChoiceHierarchy.necDiagonal_selector_predicate

namespace Classicism.Meta.ChoiceHierarchy

open AxiomSet
open Classicism.ChoiceHierarchy

def selectorStage (n : Nat) : AxiomSet Signature.pure :=
  single (NecSelector.quoted (tower n))

private theorem predicate_reduct (σ : Ty) :
    single (NecSelector.quoted (.arr (.rel (.arr σ .t)) .t)) ⟹
      single (NecSelector.quoted (.arr σ .t)) := by
  intro a ha
  change a = NecSelector.quoted (.arr σ .t) at ha
  subst a
  exact (Theorem.ofC (necSelector_down_predicate.rule σ)).mp (Theorem.ax rfl)

/-- The direction is stronger stage entails earlier stage. -/
theorem stage_successor (n : Nat) : selectorStage (n + 1) ⟹ selectorStage n := by
  cases n with
  | zero => exact predicate_reduct .e
  | succ n => exact predicate_reduct (.rel (tower n))

theorem stage_entails_of_le {i j : Nat} (h : i ≤ j) :
    selectorStage j ⟹ selectorStage i := by
  induction h with
  | refl => exact Entails.refl _
  | @step j _ ih => exact (stage_successor j).trans ih

/-- The exact FC instance giving one selector stage. -/
theorem choice_instance_entails_stage (n : Nat) :
    single (P.NecFunctionalChoice.quoted (.rel (.arr (.rel (tower n)) .t)) (tower n)) ⟹
      selectorStage n := by
  intro a ha
  change a = NecSelector.quoted (tower n) at ha
  subst a
  exact (Theorem.ofC (necSelector_of_necFunctionalChoice.rule (tower n))).mp
    (Theorem.ax rfl)

/-- One selector stage gives every input instance at its own output type. -/
theorem stage_entails_choice_instance (n : Nat) (σ : Ty) (_hσ : σ.Closed) :
    selectorStage n ⟹ single (P.NecFunctionalChoice.quoted σ (tower n)) := by
  intro a ha
  change a = P.NecFunctionalChoice.quoted σ (tower n) at ha
  subst a
  exact (Theorem.ofC (necFunctionalChoice_of_necSelector.rule σ (tower n))).mp
    (Theorem.ax rfl)

def cumulativeStages (n : Nat) : AxiomSet Signature.pure :=
  fun a => ∃ k, k ≤ n ∧ selectorStage k a

def allStages : AxiomSet Signature.pure := fun a => ∃ n, selectorStage n a

theorem cumulative_mono (i j : Nat) (h : i ≤ j) :
    cumulativeStages i ⊆ cumulativeStages j := by
  rintro a ⟨k, hk, ha⟩
  exact ⟨k, Nat.le_trans hk h, ha⟩

theorem stage_entails_cumulative (n : Nat) : selectorStage n ⟹ cumulativeStages n := by
  rintro a ⟨k, hk, ha⟩
  exact stage_entails_of_le hk a ha

theorem cumulative_entails_stage (n : Nat) : cumulativeStages n ⟹ selectorStage n :=
  Entails.of_subset (fun a ha => ⟨n, Nat.le_refl n, ha⟩)

/-- Cofinality for the deductive union of these stages themselves. This does
not assert cofinality in the whole all-type FC theory. -/
theorem theorem_at_selector_stage {p : Sentence Signature.pure}
    (h : Theorem (C.axioms ∪ allStages) p) :
    ∃ n, Theorem (C.axioms ∪ selectorStage n) p := by
  have h' : Theorem (C.axioms ∪ (fun a => ∃ n, cumulativeStages n a)) p :=
    Derivable.mono (fun a ha => ha.elim Or.inl
      (fun hs => hs.elim fun n hn => Or.inr ⟨n, n, Nat.le_refl n, hn⟩)) h
  obtain ⟨n, hn⟩ := FiniteChoiceBasis.theorem_at_stage cumulative_mono h'
  exact ⟨n, Derivable.cut (stage_entails_cumulative n) hn⟩

end Classicism.Meta.ChoiceHierarchy
