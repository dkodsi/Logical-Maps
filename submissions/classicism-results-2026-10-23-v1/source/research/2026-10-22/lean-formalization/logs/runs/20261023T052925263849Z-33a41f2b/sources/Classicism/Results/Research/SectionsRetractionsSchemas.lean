import Classicism.Results.Research.SectionsRetractionsCharacterizationsCertificates

/-!
# Full-schema choice and unique-choice decompositions

These are metalinguistic entailments between axiom sets. No formula in C
quantifies over types. Every relational output is expanded into its finite
argument list, including the empty list for truth values.

Direct sources: `notes/functional-choice-by-sections.md`, §3, and
`notes/choice-uniformization.md`, §12 (under `research/2026-10-22/`).
The argument-list assembly follows `Classicism.Results.Lists.schema_subset_args₂`.
-/
namespace Classicism.Meta.Research.Splitting
open AxiomSet Classicism.Research.Splitting

private theorem schema_subset_output_args (q : Ty → RTy → Sentence Signature.pure) :
    (fun a => ∃ σ : Ty, ∃ ρ : RTy, σ.Closed ∧ ρ.Closed ∧ a = q σ ρ) ⊆
    (fun a => ∃ νs : List Ty, ∃ σ : Ty,
      Ty.AllClosed νs ∧ σ.Closed ∧ a = q σ (νs ⇒* .t)) :=
  fun _ ⟨σ, ρ, hσ, hρ, he⟩ =>
    ⟨ρ.args, σ, RTy.closed_args hρ, hσ,
      he.trans (congrArg (q σ) (RTy.ofArgs_args ρ).symm)⟩

abbrev ActualitySections := P.Actuality.schema ∪ RightSplitting.schema
abbrev ActualityRetractions := P.Actuality.schema ∪ LeftSplitting.schema

theorem actuality_sections_imply_functional_choice :
    ActualitySections ⟹ P.FunctionalChoice.schema :=
  Entails.trans
    (Entails.union (Entails.refl ActualitySections)
      (Entails.union_right P.Actuality.schema RightSplitting.schema))
    (Entails.mono_right (schema_subset_output_args P.FunctionalChoice.quoted)
      actuality_sections_choice.listEntails)

theorem functional_choice_implies_actuality_sections :
    P.FunctionalChoice.schema ⟹ ActualitySections :=
  Entails.union functional_choice_actuality.entails functional_choice_sections.entails

theorem functional_choice_equivalence :
    (P.FunctionalChoice.schema ⟹ ActualitySections) ∧
    (ActualitySections ⟹ P.FunctionalChoice.schema) :=
  ⟨functional_choice_implies_actuality_sections, actuality_sections_imply_functional_choice⟩

theorem actuality_retractions_imply_plenitude :
    ActualityRetractions ⟹ P.Plenitude.schema :=
  Entails.trans
    (Entails.union (Entails.refl ActualityRetractions)
      (Entails.union_right P.Actuality.schema LeftSplitting.schema))
    (Entails.mono_right (schema_subset_output_args P.Plenitude.quoted)
      actuality_retractions_plenitude.listEntails)

theorem plenitude_implies_actuality_retractions :
    P.Plenitude.schema ⟹ ActualityRetractions :=
  Entails.union plenitude_actuality.entails plenitude_retractions.entails

theorem plenitude_equivalence :
    (P.Plenitude.schema ⟹ ActualityRetractions) ∧
    (ActualityRetractions ⟹ P.Plenitude.schema) :=
  ⟨plenitude_implies_actuality_retractions, actuality_retractions_imply_plenitude⟩

end Classicism.Meta.Research.Splitting

#print axioms Classicism.Meta.Research.Splitting.functional_choice_equivalence
#print axioms Classicism.Meta.Research.Splitting.plenitude_equivalence
