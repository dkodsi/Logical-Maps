import Classicism.Results.Research.TwoStageArithmeticModel
import Classicism.Results.Research.FregeModelRules
import Classicism.Syntax.Normalize

/-!
# Finite current individuals with an internally infinite number field

Direct source: finite-type-propagation.md, section 9; unpaginated original
research (misc), 23 October 2026. The terminal domain realizes quantified
Infinity. The certified C implication yields the Peano condition there, so
ArithmeticI holds at the root by its actual diamond semantics. The certified
noncollapse theorem then gives internal infinitude of the root's number field.
No C5 assumption or external-standardness premise is used.
-/

noncomputable section

namespace Classicism.Meta.Research.TwoStageArithmeticNumbers

open CategoryTheory Intensional TwoStageArithmeticModel
open Classicism.Research.FregeModelRules

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers base: before holds_conv"
  out.flush : IO Unit)

theorem holds_conv {C : Type} [SmallCategory C]
    (B : Premodel Signature.pure C) (M : B.IsModel) {W : C}
    (h : B.W₀ ⟶ W) {p q : Sentence Signature.pure} (c : Conv p q) :
    B.Holds h p .nil ↔ B.Holds h q .nil := by
  unfold Premodel.Holds
  rw [B.sem_conv M c h .nil]

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers base: before holds_C_at"
  out.flush : IO Unit)

theorem holds_C_at {C : Type} [SmallCategory C]
    (B : Premodel Signature.pure C) (M : B.IsModel) {W : C}
    (h : B.W₀ ⟶ W) {p : Sentence Signature.pure} (hp : Classicism.Meta.C.Theorem p) :
    B.Holds h p .nil :=
  B.sound M h (B.axioms_holds M h) hp .nil (fun _ h => nomatch h)

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers base: before possible_at"
  out.flush : IO Unit)

theorem possible_at {C : Type} [SmallCategory C]
    (B : Premodel Signature.pure C) (M : B.IsModel) {W : C}
    (h : B.W₀ ⟶ W) {p : Sentence Signature.pure} (hp : B.Holds h p .nil) :
    B.HoldsSentence (Term.dia p) :=
  (B.dia_iff_truncate M p).2 ⟨W, h, (B.holdsSentence_truncate h p).2 hp⟩

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers base: before actualInfinity_conversion"
  out.flush : IO Unit)

theorem actualInfinity_conversion (σ : Ty) :
    Conv (ActualInfinity.quoted σ) (axInf σ) := Conv.of_nf 64 _ _ rfl

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers base: before arithmetic_conversion"
  out.flush : IO Unit)

theorem arithmetic_conversion (σ : Ty) :
    Conv (Arithmetic.quoted σ) (Term.dia (Peano.quoted σ)) := Conv.of_nf 64 _ _ rfl

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers base: before terminal_actual_infinity"
  out.flush : IO Unit)

theorem terminal_actual_infinity :
    infiniteModel.Holds (entrance Nat 0) (ActualInfinity.quoted .e) .nil := by
  letI : Infinite (infiniteModel.Dom (terminal Nat 0) .e) := inferInstanceAs (Infinite Nat)
  apply (holds_conv infiniteModel infiniteModel_isModel (entrance Nat 0)
    (actualInfinity_conversion .e)).2
  exact Premodel.holds_axInf_of_infinite infiniteModel_isModel (isExtFull Nat 0)
    (entrance Nat 0) .e

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers base: before terminal_peano"
  out.flush : IO Unit)

theorem terminal_peano :
    infiniteModel.Holds (entrance Nat 0) (Peano.quoted .e) .nil := by
  have hr := holds_C_at infiniteModel infiniteModel_isModel (entrance Nat 0)
    (infinity_implies_peano.rule .e)
  exact (infiniteModel.holds_imp infiniteModel_isModel _ _ _ _).1 hr terminal_actual_infinity

#eval (do
  let out ← IO.getStdout
  out.putStrLn "Numbers base: complete"
  out.flush : IO Unit)

end Classicism.Meta.Research.TwoStageArithmeticNumbers
