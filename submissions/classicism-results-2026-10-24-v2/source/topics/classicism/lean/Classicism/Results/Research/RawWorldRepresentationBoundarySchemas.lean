import Classicism.Results.Research.RawWorldRepresentationBoundaryCertificates
import Classicism.Results.Arity

/-! Every relational type is its finite argument list followed by t. This file
assembles actual translated C derivations; it does not insert an object-level
quantifier over types or assume an unknown constant-relation embedding. -/
namespace Classicism.Meta.Research.RawWorldRepresentationBoundary
open AxiomSet

private theorem schema_subset_args (q : RTy → Sentence Signature.pure) :
    (fun a => ∃ ρ : RTy, ρ.Closed ∧ a = q ρ) ⊆
      (fun a => ∃ σs : List Ty, Ty.AllClosed σs ∧ a = q (σs ⇒* .t)) :=
  fun _ ⟨ρ, hρ, h⟩ =>
    ⟨ρ.args, RTy.closed_args hρ, h.trans (congrArg q (RTy.ofArgs_args ρ).symm)⟩

theorem no_raw_wr_all_relational : empty ⟹
    Classicism.Research.RawWorldRepresentationBoundary.NoRawWRRelational.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.trans Classicism.Meta.classicism_implies_existence_r
        Classicism.P.Existence.schema_entails_listSchema)
      Classicism.Research.RawWorldRepresentationBoundary.existence_implies_no_raw_wr_unary.listEntails)

end Classicism.Meta.Research.RawWorldRepresentationBoundary

#print axioms Classicism.Meta.Research.RawWorldRepresentationBoundary.no_raw_wr_all_relational
