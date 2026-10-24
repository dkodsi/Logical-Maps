import Classicism.Results.Research.SectionsRetractionsPersistenceCertificates
import Classicism.Results.Arity

/-!
# Full-schema persistence and strong-section equivalences

Direct source: `research/2026-10-22/notes/choice-uniformization.md`, §§11,18
(misc; unpaginated). Existence at the argument tuple follows from C; it is
not a new optional assumption. The empty tuple includes the type t.
-/
namespace Classicism.Meta.Research.Splitting
open AxiomSet Classicism.Research.Splitting

private theorem persistence_schema_subset_args (q : RTy → Sentence Signature.pure) :
    (fun a => ∃ ρ : RTy, ρ.Closed ∧ a = q ρ) ⊆
      (fun a => ∃ σs : List Ty, Ty.AllClosed σs ∧ a = q (σs ⇒* .t)) :=
  fun _ ⟨ρ, hρ, h⟩ =>
    ⟨ρ.args, RTy.closed_args hρ, h.trans (congrArg q (RTy.ofArgs_args ρ).symm)⟩

private theorem tuple_existence (Ax : AxiomSet Signature.pure) : Ax ⟹ P.Existence.listSchema :=
  Entails.mono_left (fun _ h => h.elim)
    (Entails.trans classicism_implies_existence_r P.Existence.schema_entails_listSchema)

theorem persistent_surjections_imply_relational_barcan :
    SurjectivityPersists.schema ⟹ P.BarcanRelational.schema :=
  Entails.trans
    (Entails.union (tuple_existence _) (Entails.refl _))
    (Entails.mono_right (persistence_schema_subset_args P.BarcanRelational.quoted)
      relational_barcan_of_surjectivity.listEntails)

theorem relational_barcan_implies_persistent_surjections :
    P.BarcanRelational.schema ⟹ SurjectivityPersists.schema :=
  surjectivity_of_relational_barcan.entails

theorem persistence_surjectivity_equivalence :
    (SurjectivityPersists.schema ⟹ P.BarcanRelational.schema) ∧
    (P.BarcanRelational.schema ⟹ SurjectivityPersists.schema) :=
  ⟨persistent_surjections_imply_relational_barcan,
    relational_barcan_implies_persistent_surjections⟩

theorem strong_sections_imply_relational_barcan :
    StrongRightSplitting.schema ⟹ P.BarcanRelational.schema :=
  Entails.trans
    (Entails.union (tuple_existence _) (Entails.refl _))
    (Entails.mono_right (persistence_schema_subset_args P.BarcanRelational.quoted)
      relational_barcan_of_strong_sections.listEntails)

theorem strong_sections_equivalence :
    (StrongRightSplitting.schema ⟹ RightSplitting.schema ∪ P.BarcanRelational.schema) ∧
    (RightSplitting.schema ∪ P.BarcanRelational.schema ⟹ StrongRightSplitting.schema) :=
  ⟨Entails.union strong_sections_sections.entails strong_sections_imply_relational_barcan,
    strong_sections_of_sections_relational_barcan.entails⟩

end Classicism.Meta.Research.Splitting

#print axioms Classicism.Meta.Research.Splitting.persistence_surjectivity_equivalence
#print axioms Classicism.Meta.Research.Splitting.strong_sections_equivalence
