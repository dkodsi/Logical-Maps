import Classicism.Results.Research.AtomicProbabilityRationalAdditive
import Classicism.Results.Research.AtomicProbabilityFractionDensity

/-!
# Linear order, density and Archimedean bounds on signed rational codes

R ≤ S means S is R plus an embedded nonnegative fraction. Cross-addition
identifies this with the constructed fraction order, proving totality and
antisymmetry. Strict density and natural upper bounds are then constructed.
Source: new internal-real bridge formalization, 22 October 2026.
-/

namespace Classicism.Research.ProbabilityRationals
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ProbabilityNumericOperations
open Classicism.Research.ProbabilityFractions

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)
local notation "ρ" => (φ → φ → Prop)

def RLe (w : Prop) (R S : ρ) : Prop :=
  RationalField w R ∧ RationalField w S ∧ ∃ X, FractionField w X ∧ rplus w R (embed w X) = S
def RLt (w : Prop) (R S : ρ) : Prop := RLe w R S ∧ R ≠ S

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem rplus_right_comm (R S U : ρ) (hR : RationalField w R)
    (hS : RationalField w S) (hU : RationalField w U) :
    rplus w (rplus w R S) U = rplus w (rplus w R U) S := by
  rw [rplus_assoc w hw hInf R S U hR hS hU, rplus_comm w hw hInf S U hS hU,
    ← rplus_assoc w hw hInf R U S hR hU hS]

include hw hInf in
theorem rplus_cancel_left (R S U : ρ) (hR : RationalField w R)
    (hS : RationalField w S) (hU : RationalField w U)
    (he : rplus w U R = rplus w U S) : R = S := by
  apply rplus_cancel_right w hw hInf R S U hR hS hU
  rw [rplus_comm w hw hInf R U hR hU, rplus_comm w hw hInf S U hS hU]
  exact he

include hw hInf in
theorem rle_codes_iff (A B C D : φ) (hA : FractionField w A) (hB : FractionField w B)
    (hC : FractionField w C) (hD : FractionField w D) :
    RLe w (signedCode w A B) (signedCode w C D) ↔ QLe w (qplus w A D) (qplus w C B) := by
  constructor
  · intro h
    obtain ⟨X, hX, he⟩ := h.2.2
    change rplus w (signedCode w A B) (signedCode w X (qzero w)) = signedCode w C D at he
    rw [rplus_codes w hw hInf A B X _ hA hB hX (qzero_in_field w hw hInf),
      qplus_zero_right w hw hInf B hB] at he
    have hd := (signedCode_identity_iff w hw hInf _ B C D
      (qplus_in_field w hw hInf A X hA hX) hB hC hD).1 he
    refine ⟨qplus_in_field w hw hInf A D hA hD, qplus_in_field w hw hInf C B hC hB, X, hX, ?_⟩
    exact (qplus_right_comm w hw hInf A D X hA hD hX).trans hd
  · intro h
    obtain ⟨X, hX, he⟩ := h.2.2
    refine ⟨signedCode_in_field w hw A B hA hB, signedCode_in_field w hw C D hC hD, X, hX, ?_⟩
    change rplus w (signedCode w A B) (signedCode w X (qzero w)) = signedCode w C D
    rw [rplus_codes w hw hInf A B X _ hA hB hX (qzero_in_field w hw hInf),
      qplus_zero_right w hw hInf B hB]
    apply (signedCode_identity_iff w hw hInf _ B C D
      (qplus_in_field w hw hInf A X hA hX) hB hC hD).2
    exact (qplus_right_comm w hw hInf A X D hA hX hD).trans he

include hw hInf in
theorem rle_refl (R : ρ) (hR : RationalField w R) : RLe w R R :=
  ⟨hR, hR, qzero w, qzero_in_field w hw hInf, rplus_zero_right w hw hInf R hR⟩

include hw hInf in
theorem rle_total (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    RLe w R S ∨ RLe w S R := by
  obtain ⟨A, B, hA, hB, hRa⟩ := hR.2
  obtain ⟨C, D, hC, hD, hSc⟩ := hS.2
  rw [hRa, hSc]
  rcases qle_total w hw hInf _ _ (qplus_in_field w hw hInf A D hA hD)
    (qplus_in_field w hw hInf C B hC hB) with h | h
  · exact Or.inl ((rle_codes_iff w hw hInf A B C D hA hB hC hD).2 h)
  · exact Or.inr ((rle_codes_iff w hw hInf C D A B hC hD hA hB).2 h)

include hw hInf in
theorem rle_antisymm (R S : ρ) (hRS : RLe w R S) (hSR : RLe w S R) : R = S := by
  obtain ⟨A, B, hA, hB, hRa⟩ := hRS.1.2
  obtain ⟨C, D, hC, hD, hSc⟩ := hRS.2.1.2
  rw [hRa, hSc] at hRS hSR ⊢
  have h₁ := (rle_codes_iff w hw hInf A B C D hA hB hC hD).1 hRS
  have h₂ := (rle_codes_iff w hw hInf C D A B hC hD hA hB).1 hSR
  exact (signedCode_identity_iff w hw hInf A B C D hA hB hC hD).2
    (qle_antisymm w hw hInf _ _ h₁ h₂)

include hw hInf in
theorem rle_trans (R S U : ρ) (hRS : RLe w R S) (hSU : RLe w S U) : RLe w R U := by
  obtain ⟨X, hX, hRX⟩ := hRS.2.2
  obtain ⟨Y, hY, hSY⟩ := hSU.2.2
  refine ⟨hRS.1, hSU.2.1, qplus w X Y, qplus_in_field w hw hInf X Y hX hY, ?_⟩
  rw [← embed_add w hw hInf X Y hX hY,
    ← rplus_assoc w hw hInf R _ _ hRS.1 (embed_in_field w hw hInf X hX)
      (embed_in_field w hw hInf Y hY), hRX, hSY]

include hw hInf in
theorem rlt_of_le_of_lt (R S U : ρ) (hRS : RLe w R S) (hSU : RLt w S U) : RLt w R U := by
  refine ⟨rle_trans w hw hInf R S U hRS hSU.1, ?_⟩
  intro he
  have hUS : RLe w U S := he ▸ hRS
  exact hSU.2 (rle_antisymm w hw hInf S U hSU.1 hUS)

include hw hInf in
theorem rlt_trans (R S U : ρ) (hRS : RLt w R S) (hSU : RLt w S U) : RLt w R U :=
  rlt_of_le_of_lt w hw hInf R S U hRS.1 hSU

include hw hInf in
theorem rlt_of_lt_of_le (R S U : ρ) (hRS : RLt w R S) (hSU : RLe w S U) : RLt w R U := by
  refine ⟨rle_trans w hw hInf R S U hRS.1 hSU, ?_⟩
  intro he
  have hSR : RLe w S R := he.symm ▸ hSU
  exact hRS.2 (rle_antisymm w hw hInf R S hRS.1 hSR)

theorem rlt_irrefl (R : ρ) : ¬ RLt w R R := fun h => h.2 rfl

include hw hInf in
theorem rle_add_right (R S U : ρ) (hRS : RLe w R S) (hU : RationalField w U) :
    RLe w (rplus w R U) (rplus w S U) := by
  obtain ⟨X, hX, hRX⟩ := hRS.2.2
  refine ⟨rplus_in_field w hw hInf R U hRS.1 hU,
    rplus_in_field w hw hInf S U hRS.2.1 hU, X, hX, ?_⟩
  rw [rplus_right_comm w hw hInf R U _ hRS.1 hU (embed_in_field w hw hInf X hX), hRX]

include hw hInf in
theorem embed_order (X Y : φ) (hXY : QLe w X Y) : RLe w (embed w X) (embed w Y) := by
  apply (rle_codes_iff w hw hInf X (qzero w) Y (qzero w)
    hXY.1 (qzero_in_field w hw hInf) hXY.2.1 (qzero_in_field w hw hInf)).2
  rw [qplus_zero_right w hw hInf X hXY.1, qplus_zero_right w hw hInf Y hXY.2.1]
  exact hXY

include hw hInf in
theorem embed_strict_order (X Y : φ) (hXY : QLt w X Y) : RLt w (embed w X) (embed w Y) :=
  ⟨embed_order w hw hInf X Y hXY.1,
    fun he => hXY.2 (embed_injective w hw hInf X Y hXY.1.1 hXY.1.2.1 he)⟩

include hw hInf in
theorem rlt_add_positive (R : ρ) (X : φ) (hR : RationalField w R)
    (hX : FractionField w X) (hnX : X ≠ qzero w) : RLt w R (rplus w R (embed w X)) := by
  refine ⟨⟨hR, rplus_in_field w hw hInf R _ hR (embed_in_field w hw hInf X hX), X, hX, rfl⟩, ?_⟩
  intro he
  have he' : rplus w R (rzero w) = rplus w R (embed w X) := (rplus_zero_right w hw hInf R hR).trans he
  have h0X := rplus_cancel_left w hw hInf _ _ R
    (rzero_in_field w hw hInf) (embed_in_field w hw hInf X hX) hR he'
  exact hnX (embed_injective w hw hInf X (qzero w) hX (qzero_in_field w hw hInf) h0X.symm)

include hw hInf in
theorem rational_order_dense (R S : ρ) (hRS : RLt w R S) :
    ∃ M, RationalField w M ∧ RLt w R M ∧ RLt w M S := by
  obtain ⟨X, hX, hRX⟩ := hRS.1.2.2
  have hnX : X ≠ qzero w := by
    intro hx0
    change rplus w R (embed w X) = S at hRX
    rw [hx0] at hRX
    have h0 : rplus w R (embed w (qzero w)) = R := rplus_zero_right w hw hInf R hRS.1.1
    exact hRS.2 (h0.symm.trans hRX)
  have hH := qhalf_in_field w hw hInf X hX
  have hnH := qhalf_ne_zero w hw hInf X hX hnX
  have hEH := embed_in_field w hw hInf _ hH
  have hM := rplus_in_field w hw hInf R _ hRS.1.1 hEH
  refine ⟨rplus w R (embed w (qhalf w X)), hM,
    rlt_add_positive w hw hInf R _ hRS.1.1 hH hnH, ?_⟩
  have h := rlt_add_positive w hw hInf _ _ hM hH hnH
  rw [rplus_assoc w hw hInf R _ _ hRS.1.1 hEH hEH,
    embed_add w hw hInf _ _ hH hH, qhalf_add_half w hw hInf X hX, hRX] at h
  exact h

include hw hInf in
theorem signedCode_le_positive_part (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    RLe w (signedCode w X Y) (embed w X) := by
  apply (rle_codes_iff w hw hInf X Y X (qzero w) hX hY hX (qzero_in_field w hw hInf)).2
  rw [qplus_zero_right w hw hInf X hX]
  exact ⟨hX, qplus_in_field w hw hInf X Y hX hY, Y, hY, rfl⟩

include hw hInf in
theorem rational_has_natural_bound (R : ρ) (hR : RationalField w R) :
    ∃ n, Numbers w n ∧ RLt w R (embed w (naturalCode w n)) := by
  obtain ⟨X, Y, hX, hY, he⟩ := hR.2
  obtain ⟨n, hn, hbound⟩ := fraction_has_natural_bound w hw hInf X hX
  refine ⟨n, hn, ?_⟩
  rw [he]
  exact rlt_of_le_of_lt w hw hInf _ _ _ (signedCode_le_positive_part w hw hInf X Y hX hY)
    (embed_strict_order w hw hInf _ _ hbound)

include hw hInf in
theorem rational_positive_representation (R : ρ) (hR : RLt w (rzero w) R) :
    ∃ X, FractionField w X ∧ X ≠ qzero w ∧ R = embed w X := by
  obtain ⟨X, hX, he⟩ := hR.1.2.2
  rw [rplus_zero_left w hw hInf _ (embed_in_field w hw hInf X hX)] at he
  refine ⟨X, hX, ?_, he.symm⟩
  intro hx0
  have he0 : R = rzero w := he.symm.trans (congrArg (embed w) hx0)
  exact hR.2 he0.symm

include hw hInf in
theorem positive_rational_small_reciprocal (R : ρ) (hR : RLt w (rzero w) R) :
    ∃ n, Numbers w n ∧ naturalCode w n ≠ qzero w ∧
      RLt w (embed w (qinverse w (naturalCode w n))) R := by
  obtain ⟨X, hX, hnX, he⟩ := rational_positive_representation w hw hInf R hR
  obtain ⟨n, hn, hn0, hs⟩ := reciprocal_natural_small w hw hInf X hX hnX
  refine ⟨n, hn, hn0, ?_⟩
  rw [he]
  exact embed_strict_order w hw hInf _ _ hs

include hw hInf in
theorem rational_no_upper_endpoint (R : ρ) (hR : RationalField w R) :
    ∃ S, RationalField w S ∧ RLt w R S :=
  ⟨rplus w R (rone w), rplus_in_field w hw hInf R _ hR (rone_in_field w hw hInf),
    rlt_add_positive w hw hInf R _ hR (qone_in_field w hw hInf) (qone_ne_zero w hw hInf)⟩

include hw hInf in
theorem rational_no_lower_endpoint (R : ρ) (hR : RationalField w R) :
    ∃ S, RationalField w S ∧ RLt w S R := by
  have h1 := rone_in_field (σ := σ) w hw hInf
  have hn1 := rneg_in_field w hw hInf _ h1
  have hS := rplus_in_field w hw hInf R _ hR hn1
  refine ⟨rplus w R (rneg w (rone w)), hS, ?_⟩
  have h := rlt_add_positive w hw hInf _ _ hS (qone_in_field w hw hInf) (qone_ne_zero w hw hInf)
  change RLt w (rplus w R (rneg w (rone w)))
    (rplus w (rplus w R (rneg w (rone w))) (rone w)) at h
  rw [rplus_assoc w hw hInf R _ _ hR hn1 h1,
    rplus_comm w hw hInf _ _ hn1 h1, rplus_neg w hw hInf _ h1,
    rplus_zero_right w hw hInf R hR] at h
  exact h

end Classicism.Research.ProbabilityRationals
