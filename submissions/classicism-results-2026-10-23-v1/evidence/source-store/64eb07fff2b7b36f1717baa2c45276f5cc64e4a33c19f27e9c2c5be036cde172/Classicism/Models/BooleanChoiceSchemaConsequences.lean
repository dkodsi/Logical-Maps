import Classicism.Models.BooleanFiniteChoice
import Classicism.Results.ChoiceHierarchyDiagonal

/-!
# Nonfinite bases for the equivalent boxed Choice schemas

Original supporting formalization (misc), 23 October 2026, of the positive
equivalence corollaries to `research/2026-10-23/boolean-valued-finite-choice.md`,
section 10 (unpaginated). The concrete boxed Functional Choice result transfers
along the existing deductive equivalences to the tower union, the all-type
diagonal schema, and the all-type boxed-selector schema.

All statements concern an equivalent finite list of original pure sentences
over C. This module makes no additional separation or stage-strictness claim
and assumes no countermodel or finite-fragment gap.
-/

namespace Classicism.Meta.ChoiceBoolean.SchemaConsequences

open AxiomSet FiniteChoiceBasis Classicism.Meta.ChoiceHierarchy

/-- A finite basis transfers across mutual entailment over the same C. -/
theorem not_finitely_axiomatizable_of_equiv {A B : AxiomSet Signature.pure}
    (hAB : A ⟹ B) (hBA : B ⟹ A) (hn : ¬ FinitelyAxiomatizable A) :
    ¬ FinitelyAxiomatizable B := by
  rintro ⟨L, hBL, hLB⟩
  exact hn ⟨L, hAB.trans hBL, hLB.trans hBA⟩

/-- The union of the existing tower-selector stages has no finite
equivalent basis over C. -/
theorem allStages_not_finitely_axiomatizable :
    ¬ FinitelyAxiomatizable allStages :=
  not_finitely_axiomatizable_of_equiv fullChoice_entails_allStages
    allStages_entails_fullChoice FiniteChoice.boxed_not_finitely_axiomatizable

/-- The all-relational-type diagonal Choice schema has no finite
equivalent basis over C. -/
theorem diagonalChoice_not_finitely_axiomatizable :
    ¬ FinitelyAxiomatizable diagonalChoice :=
  not_finitely_axiomatizable_of_equiv fullChoice_entails_diagonalChoice
    diagonalChoice_entails_fullChoice FiniteChoice.boxed_not_finitely_axiomatizable

/-- Every boxed selector instance follows from its actual boxed FC instance. -/
theorem fullChoice_entails_boxedSelector :
    P.NecFunctionalChoice.schema ⟹ Classicism.ChoiceHierarchy.NecSelector.schema := by
  rintro p ⟨ρ, hρ, rfl⟩
  exact (Theorem.ofC
    (Classicism.ChoiceHierarchy.necSelector_of_necFunctionalChoice.rule ρ)).mp
    (Theorem.ax ⟨.rel (.arr (.rel ρ) .t), ρ, ⟨hρ, trivial⟩, hρ, rfl⟩)

/-- A boxed selector for the output supplies every boxed FC input instance. -/
theorem boxedSelector_entails_fullChoice :
    Classicism.ChoiceHierarchy.NecSelector.schema ⟹ P.NecFunctionalChoice.schema := by
  rintro p ⟨σ, ρ, _hσ, hρ, rfl⟩
  exact (Theorem.ofC
    (Classicism.ChoiceHierarchy.necFunctionalChoice_of_necSelector.rule σ ρ)).mp
    (Theorem.ax ⟨ρ, hρ, rfl⟩)

/-- The full boxed-selector schema, not just its tower subfamily, has no
finite equivalent basis over C. -/
theorem boxedSelector_not_finitely_axiomatizable :
    ¬ FinitelyAxiomatizable Classicism.ChoiceHierarchy.NecSelector.schema :=
  not_finitely_axiomatizable_of_equiv fullChoice_entails_boxedSelector
    boxedSelector_entails_fullChoice FiniteChoice.boxed_not_finitely_axiomatizable

end Classicism.Meta.ChoiceBoolean.SchemaConsequences
