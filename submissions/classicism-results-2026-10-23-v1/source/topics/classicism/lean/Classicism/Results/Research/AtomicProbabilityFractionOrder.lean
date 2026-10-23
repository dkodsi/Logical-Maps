import Classicism.Results.Research.AtomicProbabilityFractionInverse
import Classicism.Results.Research.AtomicProbabilityNumericComparison

/-!
# The concrete linear order on nonnegative fractions

Order is the existence of a nonnegative additive difference. Its totality is
derived from common denominators and internal numerical comparison. Order
compatibility, strict multiplication and reciprocal order are proved below.
Source: new internal-real bridge formalization, 22 October 2026.
-/

namespace Classicism.Research.ProbabilityFractions
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ProbabilityNumericOperations

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)

def QLe (w : Prop) (X Y : φ) : Prop :=
  FractionField w X ∧ FractionField w Y ∧ ∃ Z, FractionField w Z ∧ qplus w X Z = Y
def QLt (w : Prop) (X Y : φ) : Prop := QLe w X Y ∧ X ≠ Y

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem qle_refl (X : φ) (hX : FractionField w X) : QLe w X X :=
  ⟨hX, hX, qzero w, qzero_in_field w hw hInf, qplus_zero_right w hw hInf X hX⟩

include hw hInf in
theorem qle_zero (X : φ) (hX : FractionField w X) : QLe w (qzero w) X :=
  ⟨qzero_in_field w hw hInf, hX, X, hX, qplus_zero_left w hw hInf X hX⟩

include hw hInf in
theorem qle_total (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    QLe w X Y ∨ QLe w Y X := by
  obtain ⟨d, a, b, hd, hnd, ha, hb, hXa, hYb⟩ :=
    common_denominator_two w hw hInf X Y hX hY
  rcases nle_total w hw hInf a b ha hb with hab | hba
  · obtain ⟨c, hc, hac⟩ := hab.2.2
    refine Or.inl ⟨hX, hY, fractionCode w c d, fractionCode_in_field w hw c d ⟨hc, hd, hnd⟩, ?_⟩
    rw [hXa, hYb, qplus_common_denominator w hw hInf a c d ha hc hd hnd, hac]
  · obtain ⟨c, hc, hbc⟩ := hba.2.2
    refine Or.inr ⟨hY, hX, fractionCode w c d, fractionCode_in_field w hw c d ⟨hc, hd, hnd⟩, ?_⟩
    rw [hXa, hYb, qplus_common_denominator w hw hInf b c d hb hc hd hnd, hbc]

include hw hInf in
theorem qle_trans (X Y Z : φ) (hXY : QLe w X Y) (hYZ : QLe w Y Z) : QLe w X Z := by
  obtain ⟨A, hA, hXA⟩ := hXY.2.2
  obtain ⟨B, hB, hYB⟩ := hYZ.2.2
  refine ⟨hXY.1, hYZ.2.1, qplus w A B, qplus_in_field w hw hInf A B hA hB, ?_⟩
  rw [← qplus_assoc w hw hInf X A B hXY.1 hA hB, hXA, hYB]

include hw hInf in
theorem qle_antisymm (X Y : φ) (hXY : QLe w X Y) (hYX : QLe w Y X) : X = Y := by
  obtain ⟨A, hA, hXA⟩ := hXY.2.2
  obtain ⟨B, hB, hYB⟩ := hYX.2.2
  have hsum : qplus w X (qplus w A B) = qplus w X (qzero w) := by
    rw [← qplus_assoc w hw hInf X A B hXY.1 hA hB, hXA, hYB,
      qplus_zero_right w hw hInf X hXY.1]
  have hAB := qplus_cancel_left w hw hInf _ _ X
    (qplus_in_field w hw hInf A B hA hB) (qzero_in_field w hw hInf) hXY.1 hsum
  have hA0 := (qplus_eq_zero w hw hInf A B hA hB hAB).1
  rw [hA0, qplus_zero_right w hw hInf X hXY.1] at hXA
  exact hXA

include hw hInf in
theorem qle_add_right (X Y Z : φ) (hXY : QLe w X Y) (hZ : FractionField w Z) :
    QLe w (qplus w X Z) (qplus w Y Z) := by
  obtain ⟨A, hA, hXA⟩ := hXY.2.2
  refine ⟨qplus_in_field w hw hInf X Z hXY.1 hZ,
    qplus_in_field w hw hInf Y Z hXY.2.1 hZ, A, hA, ?_⟩
  rw [qplus_right_comm w hw hInf X Z A hXY.1 hZ hA, hXA]

include hw hInf in
theorem qle_mul_right (X Y Z : φ) (hXY : QLe w X Y) (hZ : FractionField w Z) :
    QLe w (qtimes w X Z) (qtimes w Y Z) := by
  obtain ⟨A, hA, hXA⟩ := hXY.2.2
  refine ⟨qtimes_in_field w hw hInf X Z hXY.1 hZ,
    qtimes_in_field w hw hInf Y Z hXY.2.1 hZ,
    qtimes w A Z, qtimes_in_field w hw hInf A Z hA hZ, ?_⟩
  rw [← qadd_times w hw hInf X A Z hXY.1 hA hZ, hXA]

include hw hInf in
theorem qlt_mul_right (X Y Z : φ) (hXY : QLt w X Y)
    (hZ : FractionField w Z) (hnZ : Z ≠ qzero w) :
    QLt w (qtimes w X Z) (qtimes w Y Z) :=
  ⟨qle_mul_right w hw hInf X Y Z hXY.1 hZ,
    fun he => hXY.2 (qtimes_cancel_right w hw hInf X Y Z hXY.1.1 hXY.1.2.1 hZ hnZ he)⟩

include hw hInf in
theorem qlt_of_le_of_lt (X Y Z : φ) (hXY : QLe w X Y) (hYZ : QLt w Y Z) : QLt w X Z := by
  refine ⟨qle_trans w hw hInf X Y Z hXY hYZ.1, ?_⟩
  intro he
  have hZY : QLe w Z Y := he ▸ hXY
  exact hYZ.2 (qle_antisymm w hw hInf Y Z hYZ.1 hZY)

include hw hInf in
theorem qtimes_right_comm (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) :
    qtimes w (qtimes w X Y) Z = qtimes w (qtimes w X Z) Y := by
  rw [qtimes_assoc w hw hInf X Y Z hX hY hZ, qtimes_comm w hw hInf Y Z hY hZ,
    ← qtimes_assoc w hw hInf X Z Y hX hZ hY]

include hw hInf in
theorem qinverse_antitone (X Y : φ) (hXY : QLe w X Y)
    (hnX : X ≠ qzero w) (hnY : Y ≠ qzero w) : QLe w (qinverse w Y) (qinverse w X) := by
  have hIX := qinverse_in_field w hw hInf X hXY.1 hnX
  have hIY := qinverse_in_field w hw hInf Y hXY.2.1 hnY
  have h := qle_mul_right w hw hInf X Y (qtimes w (qinverse w X) (qinverse w Y)) hXY
    (qtimes_in_field w hw hInf _ _ hIX hIY)
  rw [← qtimes_assoc w hw hInf X _ _ hXY.1 hIX hIY,
    qtimes_inverse w hw hInf X hXY.1 hnX, qtimes_one_left w hw hInf _ hIY,
    ← qtimes_assoc w hw hInf Y _ _ hXY.2.1 hIX hIY,
    qtimes_right_comm w hw hInf Y _ _ hXY.2.1 hIX hIY,
    qtimes_inverse w hw hInf Y hXY.2.1 hnY, qtimes_one_left w hw hInf _ hIX] at h
  exact h

include hw hInf in
theorem qinverse_strict_antitone (X Y : φ) (hXY : QLt w X Y)
    (hnX : X ≠ qzero w) (hnY : Y ≠ qzero w) : QLt w (qinverse w Y) (qinverse w X) := by
  refine ⟨qinverse_antitone w hw hInf X Y hXY.1 hnX hnY, ?_⟩
  intro he
  have he' := congrArg (qinverse w) he
  rw [qinverse_involution w hw hInf Y hXY.1.2.1 hnY,
    qinverse_involution w hw hInf X hXY.1.1 hnX] at he'
  exact hXY.2 he'.symm

end Classicism.Research.ProbabilityFractions
