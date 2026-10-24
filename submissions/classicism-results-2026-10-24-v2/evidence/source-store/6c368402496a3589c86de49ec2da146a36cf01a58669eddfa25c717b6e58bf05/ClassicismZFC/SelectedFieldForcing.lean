import ClassicismZFC.CodedFieldForcing
import ClassicismZFC.CountableOrdinalForcing
import ClassicismZFC.OrdinalInitialSegments

/-!
# The positive real-field CH component without a general order-type theorem

The collapse model forces both the complete field/cardinal package and the
specific checked-omega-one criterion. They are conjoined BEFORE ordinary
model extraction. Internal Zorn supplies the structural cardinal dichotomy
from this actual ordinal, and internal bijections transport it to the very
field and least inductive set appearing in the package.

Original source, misc, 23 October 2026. Ambient metatheory as in OppositeCH;
no finitistic relative-consistency reduction or compiler acceptance claimed.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open Fol bSet
open scoped FirstOrder Fol Flypitch

namespace ClassicismZFC.SelectedFieldForcing

def Statement : L.Sentence :=
  CodedFieldSentence.ExistsPackage ⊓ CountableOrdinalForcing.Criterion

theorem forced : ⊤ ⊩[V collapse_algebra.𝔹_collapse] tr Statement := by
  change (⊤ : collapse_algebra.𝔹_collapse) ≤ ⟦tr Statement⟧[V collapse_algebra.𝔹_collapse]
  simp only [Statement, tr_inf, boolean_realize_sentence,
    boolean_realize_bounded_formula_and]
  exact le_inf CodedFieldForcing.positive_package_forced
    CountableOrdinalForcing.collapse_forced

noncomputable def selectedModel :
    Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {Statement}) :=
  BooleanWitnesses.smallModel (V collapse_algebra.𝔹_collapse)
    bSet_models_ZFC Statement forced

theorem modelsZFC : selectedModel.Carrier ⊨ Erdos501.FOL.ZFC :=
  (Theory.model_union_iff.mp selectedModel.is_model).1

theorem package_and_criterion :
    (selectedModel.Carrier ⊨ CodedFieldSentence.ExistsPackage) ∧
      (selectedModel.Carrier ⊨ CountableOrdinalForcing.Criterion) := by
  have h := Theory.model_singleton_iff.mp
    (Theory.model_union_iff.mp selectedModel.is_model).2
  simpa only [Statement, Sentence.realize_inf] using h

/-- The original structural CH matrix for an actual field and its actual
least inductive subset, with no structural-CH or order-type premise. -/
theorem positive_real_witnesses :
    ∃ R Plus Times Lt zero one N : selectedModel.Carrier,
      RealFieldSentence.IsField R Plus Times Lt zero one ∧
      LeastInductive.LeastInductive R zero one Plus N ∧
      CHFieldTransport.StructuralCH R N := by
  obtain ⟨R, Plus, Times, Lt, zero, one, N, G, hF, hN, hG, hRP, hPR⟩ :=
    CodedFieldSentence.field_cardinal_witnesses modelsZFC package_and_criterion.1
  obtain ⟨A, hA, hc, hcover⟩ :=
    CountableOrdinalForcing.criterion_witnesses modelsZFC package_and_criterion.2
  have hbase := OrdinalInitialSegments.structuralCH_of_ordinal_atMost
    modelsZFC hA hc hcover
  have hR := CHCardinality.schroeder_bernstein modelsZFC hPR hRP
  have hωN : CHCardinality.Equinumerous SetLaws.omegaM N := ⟨G, hG⟩
  exact ⟨R, Plus, Times, Lt, zero, one, N, hF, hN,
    (CHFieldTransport.structural_transport modelsZFC hR hωN).mp hbase⟩

#print axioms forced
#print axioms positive_real_witnesses

end ClassicismZFC.SelectedFieldForcing
