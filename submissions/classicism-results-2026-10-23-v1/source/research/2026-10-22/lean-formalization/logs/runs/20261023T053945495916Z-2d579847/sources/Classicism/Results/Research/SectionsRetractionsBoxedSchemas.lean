import Classicism.Results.Research.SectionsRetractionsBoxedCertificates

/-!
# Completely boxed splitting decompositions

Direct source: `research/2026-10-22/notes/functional-choice-by-sections.md`,
§4, and `notes/choice-uniformization.md`, §12 (misc; unpaginated).
These assemble the necessitated, discharged C implications. The stronger
benchmark with unboxed strong sections has a separate remaining obligation.
-/
namespace Classicism.Meta.Research.Splitting
open AxiomSet Classicism.Research.Splitting

private theorem boxed_schema_subset_output_args (q : Ty → RTy → Sentence Signature.pure) :
    (fun a => ∃ σ : Ty, ∃ ρ : RTy, σ.Closed ∧ ρ.Closed ∧ a = q σ ρ) ⊆
    (fun a => ∃ νs : List Ty, ∃ σ : Ty,
      Ty.AllClosed νs ∧ σ.Closed ∧ a = q σ (νs ⇒* .t)) :=
  fun _ ⟨σ, ρ, hσ, hρ, he⟩ =>
    ⟨ρ.args, σ, RTy.closed_args hρ, hσ,
      he.trans (congrArg (q σ) (RTy.ofArgs_args ρ).symm)⟩

abbrev NecessaryActualitySections := P.NecActuality.schema ∪ NecRightSplitting.schema
abbrev NecessaryActualityRetractions := P.NecActuality.schema ∪ NecLeftSplitting.schema

theorem necessary_actuality_sections_imply_necessary_choice :
    NecessaryActualitySections ⟹ P.NecFunctionalChoice.schema :=
  Entails.trans
    (Entails.union (Entails.refl NecessaryActualitySections)
      (Entails.union_right P.NecActuality.schema NecRightSplitting.schema))
    (Entails.mono_right (boxed_schema_subset_output_args P.NecFunctionalChoice.quoted)
      necessary_actuality_sections_choice.listEntails)

theorem necessary_choice_implies_necessary_actuality_sections :
    P.NecFunctionalChoice.schema ⟹ NecessaryActualitySections :=
  Entails.union necessary_choice_actuality.entails necessary_choice_sections.entails

theorem necessary_choice_equivalence :
    (P.NecFunctionalChoice.schema ⟹ NecessaryActualitySections) ∧
    (NecessaryActualitySections ⟹ P.NecFunctionalChoice.schema) :=
  ⟨necessary_choice_implies_necessary_actuality_sections,
    necessary_actuality_sections_imply_necessary_choice⟩

theorem necessary_actuality_retractions_imply_necessary_plenitude :
    NecessaryActualityRetractions ⟹ P.NecPlenitude.schema :=
  Entails.trans
    (Entails.union (Entails.refl NecessaryActualityRetractions)
      (Entails.union_right P.NecActuality.schema NecLeftSplitting.schema))
    (Entails.mono_right (boxed_schema_subset_output_args P.NecPlenitude.quoted)
      necessary_actuality_retractions_plenitude.listEntails)

theorem necessary_plenitude_implies_necessary_actuality_retractions :
    P.NecPlenitude.schema ⟹ NecessaryActualityRetractions :=
  Entails.union necessary_plenitude_actuality.entails necessary_plenitude_retractions.entails

theorem necessary_plenitude_equivalence :
    (P.NecPlenitude.schema ⟹ NecessaryActualityRetractions) ∧
    (NecessaryActualityRetractions ⟹ P.NecPlenitude.schema) :=
  ⟨necessary_plenitude_implies_necessary_actuality_retractions,
    necessary_actuality_retractions_imply_necessary_plenitude⟩

end Classicism.Meta.Research.Splitting

#print axioms Classicism.Meta.Research.Splitting.necessary_choice_equivalence
#print axioms Classicism.Meta.Research.Splitting.necessary_plenitude_equivalence
