import ClassicismZFC.CodedFieldSentence
import ClassicismZFC.RealFieldCardinalCoding

/-!
# Small ordinary models retaining the complete real-cardinal package

Original source, misc, 23 October 2026. Each field, its least inductive subset,
omega bijection, continuum injections and CH verdict come from ONE finite
sentence in ONE forcing model. This is stronger than independently extracting
a real field and unrelated cardinal witnesses. The ambient-metatheory caveat
of OppositeCH remains unchanged: this is not a finitistic Con(ZFC) reduction.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open Fol bSet Flypitch.Erdos501
open scoped FirstOrder Fol Flypitch

namespace ClassicismZFC.CodedFieldForcing

set_option pp.maxSteps 100

open CodedFieldSentence

noncomputable def collapseField : Fld collapse_algebra.𝔹_collapse :=
  ⟨CheckReals.Rc, CheckReals.plusC, CheckReals.timesC,
    CheckReals.ltC, CheckReals.zeroC, CheckReals.oneC⟩

noncomputable def randomField : Fld Flypitch.𝔹_random :=
  ⟨RandomForcing.Rdot (ι := PSet.pSet_aleph2.Type),
    RandomForcing.plusDot (ι := PSet.pSet_aleph2.Type),
    RandomForcing.timesDot (ι := PSet.pSet_aleph2.Type),
    RandomForcing.ltDot (ι := PSet.pSet_aleph2.Type),
    RandomForcing.zeroDot (ι := PSet.pSet_aleph2.Type),
    RandomForcing.oneDot (ι := PSet.pSet_aleph2.Type)⟩

theorem positive_package_forced :
    ⊤ ⊩[V collapse_algebra.𝔹_collapse] tr ExistsPackage :=
  forced_package_of_field_and_cardinal_maps collapseField
    CheckReals.completeOrderedField_Rc_collapse
    RealFieldCardinalCoding.collapse_real_to_powerset
    RealFieldCardinalCoding.collapse_powerset_to_real

theorem negative_package_forced : ⊤ ⊩[V Flypitch.𝔹_random] tr ExistsPackage :=
  forced_package_of_field_and_cardinal_maps randomField
    (RandomForcing.completeOrderedField_Rdot (ι := PSet.pSet_aleph2.Type))
    (RealFieldCardinalCoding.random_real_to_powerset (ι := PSet.pSet_aleph2.Type))
    (RealFieldCardinalCoding.random_powerset_to_real (ι := PSet.pSet_aleph2.Type))

theorem positive_forced :
    ⊤ ⊩[V collapse_algebra.𝔹_collapse] tr Positive := by
  change (⊤ : collapse_algebra.𝔹_collapse) ≤ ⟦tr Positive⟧[V collapse_algebra.𝔹_collapse]
  simp only [Positive, tr_inf, boolean_realize_sentence,
    boolean_realize_bounded_formula_and]
  exact le_inf positive_package_forced
    (by simpa only [Fol.forced_in, boolean_realize_sentence, CHTranslation.tr_CH]
      using V_𝔹_collapse_models_CH)

theorem negative_forced : ⊤ ⊩[V Flypitch.𝔹_random] tr Negative := by
  change (⊤ : Flypitch.𝔹_random) ≤ ⟦tr Negative⟧[V Flypitch.𝔹_random]
  simp only [Negative, tr_inf, boolean_realize_sentence,
    boolean_realize_bounded_formula_and]
  exact le_inf negative_package_forced
    (by simpa only [Fol.forced_in, boolean_realize_sentence, tr_not, CHTranslation.tr_CH]
      using V_𝔹_random_models_neg_CH)

noncomputable def positiveModel :
    Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {Positive}) :=
  BooleanWitnesses.smallModel (V collapse_algebra.𝔹_collapse)
    bSet_models_ZFC Positive positive_forced

noncomputable def negativeModel :
    Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {Negative}) :=
  BooleanWitnesses.smallModel (V Flypitch.𝔹_random) bSet_models_ZFC Negative negative_forced

theorem positive_modelsZFC : positiveModel.Carrier ⊨ Erdos501.FOL.ZFC :=
  (Theory.model_union_iff.mp positiveModel.is_model).1

theorem negative_modelsZFC : negativeModel.Carrier ⊨ Erdos501.FOL.ZFC :=
  (Theory.model_union_iff.mp negativeModel.is_model).1

theorem positive_package_and_CH :
    (positiveModel.Carrier ⊨ ExistsPackage) ∧
      (positiveModel.Carrier ⊨ CHTranslation.CH) := by
  have h := Theory.model_singleton_iff.mp
    (Theory.model_union_iff.mp positiveModel.is_model).2
  simpa only [Positive, Sentence.realize_inf] using h

theorem negative_package_and_not_CH :
    (negativeModel.Carrier ⊨ ExistsPackage) ∧
      ¬ (negativeModel.Carrier ⊨ CHTranslation.CH) := by
  have h := Theory.model_singleton_iff.mp
    (Theory.model_union_iff.mp negativeModel.is_model).2
  simpa only [Negative, Sentence.realize_inf, Sentence.realize_not] using h

/-- The natural and cardinal witnesses remain attached to the very same field. -/
theorem positive_cardinal_witnesses :
    ∃ R Plus Times Lt zero one N G : positiveModel.Carrier,
      RealFieldSentence.IsField R Plus Times Lt zero one ∧
      LeastInductive.LeastInductive R zero one Plus N ∧
      CHCardinality.Bijection SetLaws.omegaM N G ∧
      CHCardinality.Injects R (SetLaws.powerM SetLaws.omegaM) ∧
      CHCardinality.Injects (SetLaws.powerM SetLaws.omegaM) R :=
  field_cardinal_witnesses positive_modelsZFC positive_package_and_CH.1

theorem negative_cardinal_witnesses :
    ∃ R Plus Times Lt zero one N G : negativeModel.Carrier,
      RealFieldSentence.IsField R Plus Times Lt zero one ∧
      LeastInductive.LeastInductive R zero one Plus N ∧
      CHCardinality.Bijection SetLaws.omegaM N G ∧
      CHCardinality.Injects R (SetLaws.powerM SetLaws.omegaM) ∧
      CHCardinality.Injects (SetLaws.powerM SetLaws.omegaM) R :=
  field_cardinal_witnesses negative_modelsZFC negative_package_and_not_CH.1

#print axioms positive_forced
#print axioms negative_forced
#print axioms positive_cardinal_witnesses
#print axioms negative_cardinal_witnesses

end ClassicismZFC.CodedFieldForcing
