import ClassicismZFC.OppositeCH
import Erdos501.FOL.Axioms

/-!
# CH translation and small ordinary ZFC models

The sentence below spells out Flypitch's `CH_f` in the depth-polymorphic
Mathlib syntax of `Erdos501.FOL.Statement`. The translation equality is a
syntactic theorem, not an assumed semantic correspondence.

`atMostF smaller larger` says that a subset of `larger` admits a functional,
total, surjective graph onto `smaller`. Thus `CH` says that every ordinal is
at most countable or at least as large as the power set of omega, in the
exact cardinal-comparison formulation used by Flypitch.

We transfer the actual models from `OppositeCH` using the proved
`toM_models_ZFC` and `realize_sentence_tr`. Mathlib's
`Theory.Model.isSatisfiable` then supplies models whose carriers are in
`Type 0`, since both symbol families of `Erdos501.FOL.L` are in `Type 0`.
The named small models are chosen from these proved existence statements.

This does not assert external countability, standardness, or transitivity.
It also does not yet identify this first-order ordinal CH sentence with
the Classicism real-field CH formula. The ambient metatheory qualification
in `OppositeCH` continues to apply.
-/

open FirstOrder FirstOrder.Language
open Erdos501.FOL
open scoped FirstOrder Fol

namespace ClassicismZFC.CHTranslation

/-- Functionality of a graph, with the exact quantifier order in `is_func_f`. -/
def functionalGraphF (f : Tm) : Fm :=
  allF fun a => allF fun b => allF fun c => allF fun d =>
    impF
      (andF
        (memF (pairT (varT a) (varT c)) f)
        (memF (pairT (varT b) (varT d)) f))
      (impF (eqF (varT a) (varT b)) (eqF (varT c) (varT d)))

/-- Totality from `domain` to `codomain`, following `is_total'_f₂`. -/
def totalGraphF (domain codomain f : Tm) : Fm :=
  allF fun a => impF (memF (varT a) domain)
    (exF fun b => andF (memF (varT b) codomain)
      (memF (pairT (varT a) (varT b)) f))

/-- A subset of `larger` surjects onto `smaller` by a functional graph. -/
def atMostF (smaller larger : Tm) : Fm :=
  exF fun s => exF fun f =>
    andF
      (andF
        (subsetF (varT s) larger)
        (andF
          (functionalGraphF (varT f))
          (totalGraphF (varT s) smaller (varT f))))
      (allF fun b => impF (memF (varT b) smaller)
        (exF fun a => andF (memF (varT a) (varT s))
          (memF (pairT (varT a) (varT b)) (varT f))))

/-- Every ordinal is at most countable or at least as large as `P(omega)`. -/
def CH : L.Sentence := toSentence <|
  allF fun a => impF (ordF a)
    (orF (atMostF (varT a) omT) (atMostF (powT omT) (varT a)))

/-- The graph-functionality template has exactly Flypitch's syntax. -/
theorem tr_functionalGraphF :
    tr (functionalGraphF (varT 0) 1) = is_func_f := rfl

/-- The cardinal-comparison template has exactly Flypitch's syntax.
Mathlib levels `[larger, smaller]` become Flypitch indices `[smaller, larger]`. -/
theorem tr_atMostF : tr (atMostF (varT 1) (varT 0) 2) = at_most_f := rfl

/-- The Mathlib ordinal-CH sentence translates literally to Flypitch's `CH_f`. -/
theorem tr_CH : tr CH = CH_f := rfl

section Transfer

attribute [local instance] Erdos501.FOL.toM

/-- Truth of the exact CH sentence is preserved by the proved translation. -/
theorem realize_CH (S : Fol.Structure L_ZFC) :
    (S.carrier ⊨ CH) ↔ (S ⊨ₘ CH_f) := by
  rw [realize_sentence_tr, tr_CH]

end Transfer

/-- Mathlib ZFC plus the exact CH sentence has a nonempty small model. -/
theorem isSatisfiable_CH : (Erdos501.FOL.ZFC ∪ {CH}).IsSatisfiable := by
  obtain ⟨S, hne, hZFC, hCH⟩ := OppositeCH.exists_model_CH
  letI : Nonempty S.carrier := hne
  letI : L.Structure S.carrier := toM S
  have hCH' : S.carrier ⊨ CH := (realize_CH S).mpr hCH
  letI : S.carrier ⊨ Erdos501.FOL.ZFC ∪ {CH} :=
    Theory.model_union_iff.mpr
      ⟨toM_models_ZFC S hZFC, Theory.model_singleton_iff.mpr hCH'⟩
  exact Theory.Model.isSatisfiable S.carrier

/-- Mathlib ZFC plus the negation of the exact CH sentence has a nonempty small model. -/
theorem isSatisfiable_not_CH : (Erdos501.FOL.ZFC ∪ {CH.not}).IsSatisfiable := by
  obtain ⟨S, hne, hZFC, hCH⟩ := OppositeCH.exists_model_not_CH
  letI : Nonempty S.carrier := hne
  letI : L.Structure S.carrier := toM S
  have hCH' : S.carrier ⊨ CH.not := by
    rw [Sentence.realize_not, realize_CH S]
    exact hCH
  letI : S.carrier ⊨ Erdos501.FOL.ZFC ∪ {CH.not} :=
    Theory.model_union_iff.mpr
      ⟨toM_models_ZFC S hZFC, Theory.model_singleton_iff.mpr hCH'⟩
  exact Theory.Model.isSatisfiable S.carrier

/-- A chosen nonempty ZFC+CH model with carrier in `Type 0`. -/
noncomputable def positiveSmallModel :
    Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {CH}) :=
  Classical.choice isSatisfiable_CH

/-- A chosen nonempty ZFC+not-CH model with carrier in `Type 0`. -/
noncomputable def negativeSmallModel :
    Theory.ModelType.{0, 0, 0} (Erdos501.FOL.ZFC ∪ {CH.not}) :=
  Classical.choice isSatisfiable_not_CH

theorem positiveSmall_nonempty : Nonempty positiveSmallModel.Carrier := inferInstance

theorem negativeSmall_nonempty : Nonempty negativeSmallModel.Carrier := inferInstance

theorem positiveSmall_modelsZFC : positiveSmallModel.Carrier ⊨ Erdos501.FOL.ZFC :=
  (Theory.model_union_iff.mp positiveSmallModel.is_model).1

theorem negativeSmall_modelsZFC : negativeSmallModel.Carrier ⊨ Erdos501.FOL.ZFC :=
  (Theory.model_union_iff.mp negativeSmallModel.is_model).1

theorem positiveSmall_CH : positiveSmallModel.Carrier ⊨ CH :=
  Theory.model_singleton_iff.mp
    (Theory.model_union_iff.mp positiveSmallModel.is_model).2

theorem negativeSmall_not_CH : ¬ (negativeSmallModel.Carrier ⊨ CH) := by
  have h : negativeSmallModel.Carrier ⊨ CH.not :=
    Theory.model_singleton_iff.mp
      (Theory.model_union_iff.mp negativeSmallModel.is_model).2
  exact (Sentence.realize_not negativeSmallModel.Carrier).mp h

#print axioms tr_functionalGraphF
#print axioms tr_atMostF
#print axioms tr_CH
#print axioms realize_CH
#print axioms isSatisfiable_CH
#print axioms isSatisfiable_not_CH
#print axioms positiveSmall_nonempty
#print axioms negativeSmall_nonempty
#print axioms positiveSmall_modelsZFC
#print axioms negativeSmall_modelsZFC
#print axioms positiveSmall_CH
#print axioms negativeSmall_not_CH

end ClassicismZFC.CHTranslation
