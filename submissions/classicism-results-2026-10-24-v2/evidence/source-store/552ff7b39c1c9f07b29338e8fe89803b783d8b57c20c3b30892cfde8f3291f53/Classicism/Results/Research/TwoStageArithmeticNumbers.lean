import Classicism.Results.Research.TwoStageArithmeticNumbersBase

/-! Final semantic endpoints. Supporting lemmas are compiled separately to keep
the unchanged theorem statements within bounded compiler checks. -/

noncomputable section

namespace Classicism.Meta.Research.TwoStageArithmeticNumbers

open CategoryTheory Intensional TwoStageArithmeticModel
open Classicism.Research.FregeModelRules

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers endpoint: before root_arithmetic"
  out.flush : IO Unit)

theorem root_arithmetic : infiniteModel.HoldsSentence (Arithmetic.quoted .e) := by
  apply (holds_conv infiniteModel infiniteModel_isModel (𝟙 _) (arithmetic_conversion .e)).2
  exact possible_at infiniteModel infiniteModel_isModel (entrance Nat 0) terminal_peano

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers endpoint: before root_infinite_number_field"
  out.flush : IO Unit)

theorem root_infinite_number_field :
    infiniteModel.HoldsSentence (NumbersInfinite.quoted .e) := by
  have hr := infiniteModel.theorem_holds infiniteModel_isModel
    (arithmetic_implies_infinite_numbers.rule .e)
  exact (infiniteModel.holds_imp infiniteModel_isModel _ _ _ _).1 hr root_arithmetic

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers endpoint: before finite_individuals_arithmetic_infinite_numbers"
  out.flush : IO Unit)

theorem finite_individuals_arithmetic_infinite_numbers :
    ¬ infiniteModel.HoldsSentence (ActualInfinity.quoted .e) ∧
      infiniteModel.HoldsSentence (Arithmetic.quoted .e) ∧
      infiniteModel.HoldsSentence (NumbersInfinite.quoted .e) := by
  refine ⟨?_, root_arithmetic, root_infinite_number_field⟩
  intro h
  exact infiniteModel_internal_verdicts.1
    ((holds_conv infiniteModel infiniteModel_isModel (𝟙 _) (actualInfinity_conversion .e)).1 h)

end Classicism.Meta.Research.TwoStageArithmeticNumbers

#print axioms Classicism.Meta.Research.TwoStageArithmeticNumbers.root_arithmetic
#print axioms Classicism.Meta.Research.TwoStageArithmeticNumbers.root_infinite_number_field
#print axioms Classicism.Meta.Research.TwoStageArithmeticNumbers.finite_individuals_arithmetic_infinite_numbers
