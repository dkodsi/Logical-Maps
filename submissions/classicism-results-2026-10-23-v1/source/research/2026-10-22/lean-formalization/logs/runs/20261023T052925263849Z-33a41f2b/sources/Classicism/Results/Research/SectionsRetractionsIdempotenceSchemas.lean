import Classicism.Results.Research.SectionsRetractionsIdempotenceCertificates
import Classicism.Results.Research.SectionsRetractionsExistence

/-! Direct source: `research/2026-10-22/notes/reversible-comprehension-and-algebraic-laws.md`,
§2 (misc; unpaginated). The tuple-existence premise is discharged in C. -/
namespace Classicism.Meta.Research.Splitting
open AxiomSet Classicism.Research.Splitting

private theorem idempotent_schema_subset_args (q : RTy → Sentence Signature.pure) :
    (fun a => ∃ ρ : RTy, ρ.Closed ∧ a = q ρ) ⊆
      (fun a => ∃ σs : List Ty, Ty.AllClosed σs ∧ a = q (σs ⇒* .t)) :=
  fun _ ⟨ρ, hρ, h⟩ =>
    ⟨ρ.args, RTy.closed_args hρ, h.trans (congrArg q (RTy.ofArgs_args ρ).symm)⟩

theorem idempotence_persistence_implies_relational_barcan :
    IdempotencePersists.schema ⟹ P.BarcanRelational.schema :=
  Entails.trans
    (Entails.union (Entails.mono_left (fun _ h => h.elim) mask_list_existence)
      (Entails.refl _))
    (Entails.mono_right (idempotent_schema_subset_args P.BarcanRelational.quoted)
      idempotence_relational_barcan.listEntails)

theorem idempotence_persistence_equivalence :
    (IdempotencePersists.schema ⟹ P.BarcanRelational.schema) ∧
    (P.BarcanRelational.schema ⟹ IdempotencePersists.schema) :=
  ⟨idempotence_persistence_implies_relational_barcan, relational_barcan_idempotence.entails⟩

end Classicism.Meta.Research.Splitting

#print axioms Classicism.Meta.Research.Splitting.idempotence_persistence_equivalence
