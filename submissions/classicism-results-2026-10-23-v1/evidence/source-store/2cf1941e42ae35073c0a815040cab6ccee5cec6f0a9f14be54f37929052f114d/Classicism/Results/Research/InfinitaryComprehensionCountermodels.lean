import Classicism.Results.Research.InfinitaryComprehensionActionFull
import Classicism.Models.FullActionModels

/-!
# Infinitary Comprehension does not imply ND or Barcan

Direct source: `research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md`, section 6, and
`logical-observer-separation.md`, section 4; misc, 23 October 2026.

The full action constructions and their finite-sentence verdicts are the
existing library models. The new assertion is that the SAME constructions
interpret every actual infinitary term and satisfy the actual infinitary
Comprehension schema. No C5 presentation is assumed in that extension.
-/

namespace Classicism.Research.InfinitaryComprehension.Countermodels
open Classicism.Meta
open Classicism.Meta.Intensional
open CategoryTheory

open FullActionModels

/-- The full surjection model has all the new Comprehension instances and
necessary Barcan at each original closed type, while ND already fails at t. -/
theorem surjection_comprehension_barcan_not_nd :
    Canonical.Closed (MSet.model surj) ∧
    Canonical.Comprehension (MSet.model surj) ∧
    (∀ σ : Classicism.Meta.Ty, σ.Closed → (MSet.model surj).HoldsSentence
      (Classicism.Meta.Term.box (Sentence.bf σ))) ∧
    ¬ (MSet.model surj).HoldsSentence (Sentence.nd Ty.t) := by
  refine ⟨Canonical.full_closed _ (MSet.model_full surj),
    Canonical.full_comprehension _ (MSet.model_full surj), ?_, surj_not_nd_t⟩
  intro σ hσ
  exact Premodel.holds_box_bf_of_epic (MSet.model_isModel surj)
    (MSet.model_full surj) surj_epic (𝟙 _) σ hσ

/-- Even propositional Barcan fails in the two-element idempotent model,
although the actual unrestricted infinitary Comprehension schema holds. -/
theorem idempotent_comprehension_not_barcan :
    Canonical.Closed (MSet.model Idem) ∧
    Canonical.Comprehension (MSet.model Idem) ∧
    ¬ (MSet.model Idem).HoldsSentence (Sentence.bf Ty.t) :=
  ⟨Canonical.full_closed _ (MSet.model_full Idem),
    Canonical.full_comprehension _ (MSet.model_full Idem), Idem.not_bf_t⟩

theorem idempotent_comprehension_not_nd :
    Canonical.Closed (MSet.model Idem) ∧
    Canonical.Comprehension (MSet.model Idem) ∧
    ¬ (MSet.model Idem).HoldsSentence (Sentence.nd Ty.t) :=
  ⟨Canonical.full_closed _ (MSet.model_full Idem),
    Canonical.full_comprehension _ (MSet.model_full Idem), Idem.not_nd_t⟩

#print axioms surjection_comprehension_barcan_not_nd
#print axioms idempotent_comprehension_not_barcan
#print axioms idempotent_comprehension_not_nd

end Classicism.Research.InfinitaryComprehension.Countermodels
