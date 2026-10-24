import ClassicismZFC.BooleanWitnesses
import ClassicismZFC.RealFieldSentence
import Flypitch4.Erdos501.CheckReals
import Flypitch4.Erdos501.InternalReals
import Flypitch4.ForcingRandom

/-!
# Actual field-bearing ordinary ZFC models with opposite ordinal CH verdicts

The positive Boolean witness is the checked field in the collapse algebra.
The negative witness is the constructed measurable-name field in exactly the
aleph-two random algebra used by `V_𝔹_random_models_neg_CH`. Thus the negative
side does not mix a Cohen CH theorem with a random-algebra field theorem.

Both field existence and the CH verdict are retained in one finite sentence
before ordinary completeness and small-model extraction are applied. No
construction of reals in an arbitrary first-order ZFC model is assumed.

All forcing inputs are the actual pinned Flypitch proofs, with unchanged
Apache-2.0 sources and hashes recorded in real-field-external-provenance.json.
These ambient-metatheoretic existence results are not a finitistic Con(ZFC)
reduction. The structural CH/cardinality correspondence is a separate theorem.
-/

open FirstOrder FirstOrder.Language Erdos501.FOL
open Fol bSet Flypitch.Erdos501
open scoped FirstOrder Fol Flypitch

namespace ClassicismZFC.RealFieldForcing

open RealFieldSentence

/-- The check-name construction proves real-field existence in the collapse model. -/
theorem positive_field_forced :
    ⊤ ⊩[V collapse_algebra.𝔹_collapse] tr ExistsRealField :=
  forced_exists_of_field CheckReals.Rc CheckReals.plusC CheckReals.timesC
    CheckReals.ltC CheckReals.zeroC CheckReals.oneC
    CheckReals.completeOrderedField_Rc_collapse

/-- The measurable-name construction proves field existence in the random model. -/
theorem negative_field_forced : ⊤ ⊩[V Flypitch.𝔹_random] tr ExistsRealField :=
  forced_exists_of_field (β := Flypitch.𝔹_random)
    (RandomForcing.Rdot (ι := PSet.pSet_aleph2.Type))
    (RandomForcing.plusDot (ι := PSet.pSet_aleph2.Type))
    (RandomForcing.timesDot (ι := PSet.pSet_aleph2.Type))
    (RandomForcing.ltDot (ι := PSet.pSet_aleph2.Type))
    (RandomForcing.zeroDot (ι := PSet.pSet_aleph2.Type))
    (RandomForcing.oneDot (ι := PSet.pSet_aleph2.Type))
    (RandomForcing.completeOrderedField_Rdot (ι := PSet.pSet_aleph2.Type))

/-- The actual positive forcing model satisfies the entire conjunction. -/
theorem positive_forced :
    ⊤ ⊩[V collapse_algebra.𝔹_collapse] tr Positive := by
  change (⊤ : collapse_algebra.𝔹_collapse) ≤ ⟦tr Positive⟧[V collapse_algebra.𝔹_collapse]
  simp only [Positive, tr_inf, boolean_realize_sentence,
    boolean_realize_bounded_formula_and]
  exact le_inf positive_field_forced
    (by simpa only [Fol.forced_in, boolean_realize_sentence, CHTranslation.tr_CH]
      using V_𝔹_collapse_models_CH)

/-- The same random model simultaneously has its real field and fails CH. -/
theorem negative_forced : ⊤ ⊩[V Flypitch.𝔹_random] tr Negative := by
  change (⊤ : Flypitch.𝔹_random) ≤ ⟦tr Negative⟧[V Flypitch.𝔹_random]
  simp only [Negative, tr_inf, boolean_realize_sentence,
    boolean_realize_bounded_formula_and]
  exact le_inf negative_field_forced
    (by simpa only [Fol.forced_in, boolean_realize_sentence, tr_not, CHTranslation.tr_CH]
      using V_𝔹_random_models_neg_CH)

theorem positive_satisfiable : (Erdos501.FOL.ZFC ∪ {Positive}).IsSatisfiable :=
  BooleanWitnesses.small_model_satisfiable (V collapse_algebra.𝔹_collapse)
    bSet_models_ZFC Positive positive_forced

theorem negative_satisfiable : (Erdos501.FOL.ZFC ∪ {Negative}).IsSatisfiable :=
  BooleanWitnesses.small_model_satisfiable (V Flypitch.𝔹_random)
    bSet_models_ZFC Negative negative_forced

/-- A small model selected from the proved positive field-bearing satisfiability. -/
noncomputable def positiveModel :
    Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {Positive}) :=
  Classical.choice positive_satisfiable

/-- A small model selected from the proved negative field-bearing satisfiability. -/
noncomputable def negativeModel :
    Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {Negative}) :=
  Classical.choice negative_satisfiable

theorem positive_nonempty : Nonempty positiveModel.Carrier := inferInstance
theorem negative_nonempty : Nonempty negativeModel.Carrier := inferInstance

theorem positive_modelsZFC : positiveModel.Carrier ⊨ Erdos501.FOL.ZFC :=
  (Theory.model_union_iff.mp positiveModel.is_model).1

theorem negative_modelsZFC : negativeModel.Carrier ⊨ Erdos501.FOL.ZFC :=
  (Theory.model_union_iff.mp negativeModel.is_model).1

theorem positive_field_and_CH :
    (∃ R plus times lt zero one : positiveModel.Carrier,
      IsField R plus times lt zero one) ∧
      (positiveModel.Carrier ⊨ CHTranslation.CH) :=
  realize_Positive.mp (Theory.model_singleton_iff.mp
    (Theory.model_union_iff.mp positiveModel.is_model).2)

theorem negative_field_and_not_CH :
    (∃ R plus times lt zero one : negativeModel.Carrier,
      IsField R plus times lt zero one) ∧
      ¬ (negativeModel.Carrier ⊨ CHTranslation.CH) :=
  realize_Negative.mp (Theory.model_singleton_iff.mp
    (Theory.model_union_iff.mp negativeModel.is_model).2)

/-- The two actual models carry actual field witnesses, not additional assumptions. -/
theorem exists_opposite_field_models :
    ∃ Mpos : Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {Positive}),
    ∃ Mneg : Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {Negative}),
      ((∃ R plus times lt zero one : Mpos.Carrier,
        IsField R plus times lt zero one) ∧ (Mpos.Carrier ⊨ CHTranslation.CH)) ∧
      ((∃ R plus times lt zero one : Mneg.Carrier,
        IsField R plus times lt zero one) ∧ ¬ (Mneg.Carrier ⊨ CHTranslation.CH)) :=
  ⟨positiveModel, negativeModel, positive_field_and_CH, negative_field_and_not_CH⟩

#print axioms positive_forced
#print axioms negative_forced
#print axioms positive_field_and_CH
#print axioms negative_field_and_not_CH
#print axioms exists_opposite_field_models

end ClassicismZFC.RealFieldForcing
