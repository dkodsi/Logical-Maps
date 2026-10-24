import Classicism.Results.Research.ModalPropagationCertificates.BoxedCompleteness

/-!
# All-schema modal propagation, assembled from object-language certificates

These are metalogical entailments between the existing C schemas. The
list-rule translation supplies finite tuples including the empty tuple;
`schema_subset_args` identifies each relational type with its argument list.
There is no type quantification within any C formula. This module cannot
compile unless its imported certificate chain has produced the list entailments.

Draft only until the sole integration owner checks the full dependency closure.
-/

namespace Classicism.Meta.Research.ModalPropagation
open AxiomSet

/-- The elementary type/list identification from Results/Lists, restated locally
so this narrow certificate does not import the all-record derivation batch. -/
private theorem schema_subset_args (q : RTy → Sentence Signature.pure) :
    (fun a => ∃ ρ : RTy, ρ.Closed ∧ a = q ρ) ⊆
      (fun a => ∃ σs : List Ty, Ty.AllClosed σs ∧ a = q (σs ⇒* .t)) :=
  fun _ ⟨ρ, hρ, h⟩ =>
    ⟨ρ.args, RTy.closed_args hρ, h.trans (congrArg q (RTy.ofArgs_args ρ).symm)⟩

abbrev Assumptions := P.StrongLeibniz.schema ∪ P.RigidComprehension.schema

theorem necessary_strong_leibniz : Assumptions ⟹ P.NecStrongLeibniz.schema :=
  Entails.mono_right (schema_subset_args _)
    Classicism.Research.SealedWorldCover.sl_rc_implies_necessary_strong_leibniz.listEntails

theorem necessary_relational_barcan : Assumptions ⟹ P.NecBarcanRelational.schema :=
  have sl := Entails.union_left P.StrongLeibniz.schema P.RigidComprehension.schema
  have rc := Entails.union_right P.StrongLeibniz.schema P.RigidComprehension.schema
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union (Entails.union sl sl) rc) rc)
      Classicism.Research.ModalPropagationConsequences.sl_rc_necessary_barcan_relational.listEntails)

theorem necessary_rigid_comprehension : Assumptions ⟹ P.NecRigidComprehension.schema :=
  have sl := Entails.union_left P.StrongLeibniz.schema P.RigidComprehension.schema
  have rc := Entails.union_right P.StrongLeibniz.schema P.RigidComprehension.schema
  have hs := Entails.union (Entails.union (Entails.union (Entails.union sl sl) sl) sl) sl
  have hr := Entails.union (Entails.union (Entails.union (Entails.union hs rc) rc) rc) rc
  Entails.mono_right (schema_subset_args _)
    (Entails.trans hr
      Classicism.Research.ModalPropagationConsequences.sl_rc_necessary_comprehension.listEntails)

theorem necessary_boolean_completeness : Assumptions ⟹ P.NecBooleanCompleteness.schema :=
  have sl := Entails.union_left P.StrongLeibniz.schema P.RigidComprehension.schema
  have rc := Entails.union_right P.StrongLeibniz.schema P.RigidComprehension.schema
  have hs := Entails.union (Entails.union (Entails.union (Entails.union sl sl) sl) sl) sl
  have hr := Entails.union (Entails.union (Entails.union (Entails.union hs rc) rc) rc) rc
  Entails.mono_right (schema_subset_args _)
    (Entails.trans hr
      Classicism.Research.ModalPropagationConsequences.sl_rc_necessary_completeness.listEntails)

/-- Full-schema conclusions, preserving the restriction of BF to relational types. -/
theorem all_four : Assumptions ⟹
    ((P.NecStrongLeibniz.schema ∪ P.NecBarcanRelational.schema) ∪
      P.NecRigidComprehension.schema) ∪ P.NecBooleanCompleteness.schema :=
  Entails.union
    (Entails.union (Entails.union necessary_strong_leibniz necessary_relational_barcan)
      necessary_rigid_comprehension) necessary_boolean_completeness

end Classicism.Meta.Research.ModalPropagation
