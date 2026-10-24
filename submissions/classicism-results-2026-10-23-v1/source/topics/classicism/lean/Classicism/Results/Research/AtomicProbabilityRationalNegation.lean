import Classicism.Results.Research.AtomicProbabilityRationalTranslation

/-! Rational negation identities used by the cut inverse construction.
Source: new internal-real bridge argument, 23 October 2026. -/

namespace Classicism.Research.ProbabilityRationals
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)
local notation "ρ" => (φ → φ → Prop)
variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem rneg_zero : rneg (σ := σ) w (rzero w) = rzero w := by
  have h0 := rzero_in_field (σ := σ) w hw hInf
  have h := rplus_neg w hw hInf _ h0
  rw [rplus_zero_left w hw hInf _ (rneg_in_field w hw hInf _ h0)] at h
  exact h

include hw hInf in
theorem rneg_reverses (R S : ρ) (hRS : RLt w R S) : RLt w (rneg w S) (rneg w R) := by
  have hNR := rneg_in_field w hw hInf R hRS.1.1
  have hNS := rneg_in_field w hw hInf S hRS.1.2.1
  have h := rlt_add_right w hw hInf R S (rneg w R) hRS hNR
  rw [rplus_neg w hw hInf R hRS.1.1] at h
  have h' := rlt_add_right w hw hInf _ _ (rneg w S) h hNS
  rw [rplus_zero_left w hw hInf _ hNS,
    rplus_right_comm w hw hInf S _ _ hRS.1.2.1 hNR hNS,
    rplus_neg w hw hInf S hRS.1.2.1, rplus_zero_left w hw hInf _ hNR] at h'
  exact h'

include hw hInf in
theorem rneg_sub (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    rneg w (rsub w R S) = rsub w S R := by
  change rneg w (rplus w R (rneg w S)) = rplus w S (rneg w R)
  rw [rneg_add w hw hInf R _ hR (rneg_in_field w hw hInf S hS),
    rneg_involution w hw hInf S hS,
    rplus_comm w hw hInf _ S (rneg_in_field w hw hInf R hR) hS]

include hw hInf in
theorem rsub_sub_self (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    rsub w (rsub w R S) R = rneg w S := by
  change rplus w (rplus w R (rneg w S)) (rneg w R) = rneg w S
  rw [rplus_right_comm w hw hInf R _ _ hR
      (rneg_in_field w hw hInf S hS) (rneg_in_field w hw hInf R hR),
    rplus_neg w hw hInf R hR,
    rplus_zero_left w hw hInf _ (rneg_in_field w hw hInf S hS)]

end Classicism.Research.ProbabilityRationals
