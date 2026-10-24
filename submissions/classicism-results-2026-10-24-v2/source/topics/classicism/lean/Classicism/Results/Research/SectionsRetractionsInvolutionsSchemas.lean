import Classicism.Results.Research.SectionsRetractionsInvolutionsCertificates

/-! Direct source: `research/2026-10-22/notes/reversible-comprehension-and-algebraic-laws.md`,
§1 (misc; unpaginated). All relational outputs, including t, and all input types. -/
namespace Classicism.Meta.Research.Splitting
open AxiomSet Classicism.Research.Splitting

private theorem pairing_schema_subset_output_args (q : Ty → RTy → Sentence Signature.pure) :
    (fun a => ∃ σ : Ty, ∃ ρ : RTy, σ.Closed ∧ ρ.Closed ∧ a = q σ ρ) ⊆
    (fun a => ∃ νs : List Ty, ∃ σ : Ty,
      Ty.AllClosed νs ∧ σ.Closed ∧ a = q σ (νs ⇒* .t)) :=
  fun _ ⟨σ, ρ, hσ, hρ, he⟩ =>
    ⟨ρ.args, σ, RTy.closed_args hρ, hσ,
      he.trans (congrArg (q σ) (RTy.ofArgs_args ρ).symm)⟩

theorem pairing_representation_equivalence :
    (P.Plenitude.schema ⟹ PairingRepresentation.schema) ∧
    (PairingRepresentation.schema ⟹ P.Plenitude.schema) :=
  ⟨plenitude_pairing_representation.entails,
    Entails.mono_right (pairing_schema_subset_output_args P.Plenitude.quoted)
      pairing_representation_plenitude.listEntails⟩

end Classicism.Meta.Research.Splitting

#print axioms Classicism.Meta.Research.Splitting.pairing_representation_equivalence
