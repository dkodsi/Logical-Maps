import Classicism.Models.BooleanChoiceModel
import Classicism.Models.BooleanChoiceFragments
import Classicism.Models.BooleanFunctionalChoice
import Classicism.Models.BooleanSelectorFailure

/-!
# The concrete finite-Choice separators and the nonfinite-basis theorem

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md` sections 7--10
(unpaginated). For every finite fragment, the actual regular cutoff and
supported Boolean hierarchy give the actual countable extracted C-model.
It preserves every input instance at each protected output, and refutes
the next quoted selector. Soundness gives the finite-fragment gap, and
the existing finitary derivation-support theorem rules out any equivalent
finite list of original pure sentences.

The target remains full Functional Choice. The theorem is about an
equivalent finite basis over C; it does not rule out a finite strictly
stronger package implying Choice. No model-existence, Choice-failure,
extraction, or finite-fragment-gap hypothesis occurs in the final results.
-/

namespace Classicism.Meta.ChoiceBoolean.FiniteChoice

open AxiomSet ChoiceCutoff ProtectedCoverage ChoiceModel
open Classicism.Meta.ChoiceHierarchy

/-- Every input type is allowed: only the output has a protection bound. -/
theorem holds_functionalChoice (m : Nat) (σ : Ty) (ρ : RTy)
    (hρ : Protected (cutoff m) Nat (.rel ρ)) :
    (model m).HoldsSentence (P.FunctionalChoice.quoted σ ρ) :=
  (FunctionalChoice.small_realize_iff_quoted (typedStructure m) (isModel m) σ ρ).mp
    (small_transfer_one m (FunctionalChoice.small σ ρ)
      (FunctionalChoice.protected_value_one Nat (cutoff m) (cutoff_regular m) σ ρ hρ))

theorem holds_boxed_functionalChoice (m : Nat) (σ : Ty) (ρ : RTy)
    (hρ : Protected (cutoff m) Nat (.rel ρ)) :
    (model m).HoldsSentence (P.NecFunctionalChoice.quoted σ ρ) :=
  (FunctionalChoice.small_realize_iff_boxed (typedStructure m) (isModel m) σ ρ).mp
    (small_transfer_one m (FunctionalChoice.small σ ρ)
      (FunctionalChoice.protected_value_one Nat (cutoff m) (cutoff_regular m) σ ρ hρ))

/-- The higher failure comes from the actual constructed column family. -/
theorem fails_selector (m : Nat) :
    ¬ (model m).HoldsSentence
      (Classicism.ChoiceHierarchy.Selector.quoted (tower (m + 1))) := by
  intro h
  apply small_failure_zero m (SelectorFailure.small (tower (m + 1)))
    (SelectorFailure.small_value_zero Nat (tower (m + 1)) (ChoiceFamily.family m)
      (cutoff_regular m).aleph0_le)
  exact (SelectorFailure.small_realize_iff_quoted (typedStructure m)
    (small_comprehension m) (tower (m + 1))).mpr h

theorem fails_boxed_selector (m : Nat) :
    ¬ (model m).HoldsSentence
      (Classicism.ChoiceHierarchy.NecSelector.quoted (tower (m + 1))) := by
  intro h
  apply small_failure_zero m (SelectorFailure.small (tower (m + 1)))
    (SelectorFailure.small_value_zero Nat (tower (m + 1)) (ChoiceFamily.family m)
      (cutoff_regular m).aleph0_le)
  exact (SelectorFailure.small_realize_iff_necQuoted (typedStructure m)
    (small_comprehension m) (tower (m + 1))).mpr h

/-- The specific higher FC sentence which would yield the failed selector. -/
noncomputable def missingBoxedChoice (m : Nat) : Sentence Signature.pure :=
  P.NecFunctionalChoice.quoted
    (.rel (.arr (.rel (tower (m + 1))) .t)) (tower (m + 1))

noncomputable def missingChoice (m : Nat) : Sentence Signature.pure :=
  P.FunctionalChoice.quoted
    (.rel (.arr (.rel (tower (m + 1))) .t)) (tower (m + 1))

theorem missingBoxedChoice_mem (m : Nat) :
    P.NecFunctionalChoice.schema (missingBoxedChoice m) :=
  ⟨.rel (.arr (.rel (tower (m + 1))) .t), tower (m + 1),
    ⟨tower_closed (m + 1), trivial⟩, tower_closed (m + 1), rfl⟩

theorem missingChoice_mem (m : Nat) : P.FunctionalChoice.schema (missingChoice m) :=
  ⟨.rel (.arr (.rel (tower (m + 1))) .t), tower (m + 1),
    ⟨tower_closed (m + 1), trivial⟩, tower_closed (m + 1), rfl⟩

theorem fails_boxed_choice (m : Nat) : ¬ (model m).HoldsSentence (missingBoxedChoice m) := by
  intro h
  have hs := (model m).entails_holds (isModel m)
    (choice_instance_entails_stage (m + 1)) ((model m).holdsAx_single h)
  exact fails_boxed_selector m (hs _ rfl)

theorem fails_choice (m : Nat) : ¬ (model m).HoldsSentence (missingChoice m) := by
  intro h
  apply fails_boxed_choice m
  exact (FunctionalChoice.holdsSentence_box_iff (typedStructure m) (isModel m)
    (missingChoice m)).mpr h

/-- A finite fragment determines a concrete member of the constructed
model sequence. The last conjunct is an actual missing schema instance. -/
theorem finite_boxed_countermodel (L : List (Sentence Signature.pure))
    (hL : ∀ p ∈ L, P.NecFunctionalChoice.schema p) :
    ∃ m : Nat, (model m).IsModel ∧ (model m).HoldsAx (FiniteChoiceBasis.ofList L) ∧
      ¬ (model m).HoldsSentence (missingBoxedChoice m) := by
  obtain ⟨m, hm⟩ := ChoiceFragments.finite_boxed_protected L hL
  refine ⟨m, isModel m, ?_, fails_boxed_choice m⟩
  intro p hp
  obtain ⟨σ, ρ, _, _, he, hρ⟩ := hm p hp
  rw [he]
  exact holds_boxed_functionalChoice m σ ρ hρ

theorem finite_unboxed_countermodel (L : List (Sentence Signature.pure))
    (hL : ∀ p ∈ L, P.FunctionalChoice.schema p) :
    ∃ m : Nat, (model m).IsModel ∧ (model m).HoldsAx (FiniteChoiceBasis.ofList L) ∧
      ¬ (model m).HoldsSentence (missingChoice m) := by
  obtain ⟨m, hm⟩ := ChoiceFragments.finite_unboxed_protected L hL
  refine ⟨m, isModel m, ?_, fails_choice m⟩
  intro p hp
  obtain ⟨σ, ρ, _, _, he, hρ⟩ := hm p hp
  rw [he]
  exact holds_functionalChoice m σ ρ hρ

/-- This supplies the former separation hypothesis from the construction. -/
theorem boxed_finite_fragment_gap :
    FiniteChoiceBasis.FiniteFragmentGap P.NecFunctionalChoice.schema := by
  intro L hL
  obtain ⟨m, hM, hAx, hn⟩ := finite_boxed_countermodel L hL
  exact ⟨missingBoxedChoice m, missingBoxedChoice_mem m,
    fun hd => hn ((model m).theoremWith_holds hM hAx hd)⟩

theorem unboxed_finite_fragment_gap :
    FiniteChoiceBasis.FiniteFragmentGap P.FunctionalChoice.schema := by
  intro L hL
  obtain ⟨m, hM, hAx, hn⟩ := finite_unboxed_countermodel L hL
  exact ⟨missingChoice m, missingChoice_mem m,
    fun hd => hn ((model m).theoremWith_holds hM hAx hd)⟩

/-- No finite list of original pure sentences is equivalent over C to
the full boxed Functional Choice schema. -/
theorem boxed_not_finitely_axiomatizable :
    ¬ FiniteChoiceBasis.FinitelyAxiomatizable P.NecFunctionalChoice.schema :=
  FiniteChoiceBasis.not_finitely_axiomatizable boxed_finite_fragment_gap

/-- The same nonfinite-equivalent-basis conclusion holds without boxes. -/
theorem unboxed_not_finitely_axiomatizable :
    ¬ FiniteChoiceBasis.FinitelyAxiomatizable P.FunctionalChoice.schema :=
  FiniteChoiceBasis.not_finitely_axiomatizable unboxed_finite_fragment_gap

theorem holds_selector_stage (m : Nat) : (model m).HoldsAx (selectorStage m) :=
  (model m).entails_holds (isModel m) (choice_instance_entails_stage m)
    ((model m).holdsAx_single
      (holds_boxed_functionalChoice m (.rel (.arr (.rel (tower m)) .t)) (tower m)
        (tower_protected m)))

/-- The actual adjacent stages are strictly increasing in deductive strength. -/
theorem selector_stage_strict (m : Nat) :
    ¬ (selectorStage m ⟹ selectorStage (m + 1)) :=
  (model m).not_entails_of_model (isModel m) (holds_selector_stage m)
    rfl (fails_boxed_selector m)

theorem adjacent_selector_countermodel (m : Nat) :
    (model m).IsModel ∧ (model m).HoldsAx (selectorStage m) ∧
      ¬ (model m).HoldsSentence
        (Classicism.ChoiceHierarchy.NecSelector.quoted (tower (m + 1))) :=
  ⟨isModel m, holds_selector_stage m, fails_boxed_selector m⟩

end Classicism.Meta.ChoiceBoolean.FiniteChoice
