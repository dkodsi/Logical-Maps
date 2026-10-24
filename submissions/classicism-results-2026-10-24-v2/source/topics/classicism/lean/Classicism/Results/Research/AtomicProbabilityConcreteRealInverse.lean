import Classicism.Results.Research.AtomicProbabilityCutCrossing
import Classicism.Results.Research.AtomicProbabilityRationalNegation

/-!
# Concrete additive inverses for supported rational cuts

Negation is the open reflection of the complement inside the actual rational
domain. The reverse inverse inclusion uses the internal small-gap theorem,
whose finite crossing proof is supplied by CutCrossing; it is not an extra
hypothesis. The resulting literal identities give additive cancellation and
the guarded additive-order/subtraction equivalence needed by probability.
Real multiplication and normalization remain separate obligations.
Source: new internal-real bridge argument, 23 October 2026.
-/

namespace Classicism.Research.ProbabilityConcreteReals
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ProbabilityRationals
open Classicism.Research.ProbabilityCuts
open Classicism.Research.ProbabilitySupportedReals
open Classicism.Research.ProbabilityCutCrossing

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)
local notation "ρ" => (φ → φ → Prop)

def realNeg (w : Prop) (P : ρ → Prop) : ρ → Prop :=
  fun R => w ∧ RationalField w R ∧ ∃ S, RationalField w S ∧ ¬ P S ∧ RLt w R (rneg w S)
def realSub (w : Prop) (P Q : ρ → Prop) : ρ → Prop := realAdd w P (realNeg w Q)

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

theorem realNeg_below (P : ρ → Prop) : realNeg w P ≤ BaseSupport w (RationalField w) :=
  le_of_box_incl (nec% (fun (R : ρ) (h : realNeg w P R) => ⟨h.1, h.2.1⟩))

theorem realNeg_supported (P : ρ → Prop) : Supported w (realNeg w P) :=
  le_trans_rel _ _ _ (realNeg_below w P) (baseSupport_supported w (RationalField w))

include hw hInf in
theorem negative_member_not_neg (P : ρ → Prop) (hP : RealField w P)
    (R : ρ) (hPR : P R) : ¬ realNeg w P (rneg w R) := by
  intro h
  obtain ⟨S, hS, hnPS, hlt⟩ := h.2.2
  have hR := hP.2.2.1 R hPR
  have hSR := rneg_reverses w hw hInf _ _ hlt
  rw [rneg_involution w hw hInf S hS, rneg_involution w hw hInf R hR] at hSR
  exact hnPS (hP.2.2.2.2.2.1 S R hS hR hSR hPR)

include hw hInf in
theorem realNeg_in_field (P : ρ → Prop) (hP : RealField w P) : RealField w (realNeg w P) := by
  have hcP := hP.2.2
  refine ⟨hw.1, realNeg_below w P, ?_, ?_, ?_, ?_, ?_⟩
  · intro R hR
    exact hR.2.1
  · obtain ⟨S, hS, hnPS⟩ := hcP.2.2.1
    obtain ⟨R, hR, hRS⟩ := rational_no_lower_endpoint w hw hInf _ (rneg_in_field w hw hInf S hS)
    exact ⟨R, hw.1, hR, S, hS, hnPS, hRS⟩
  · obtain ⟨R, hPR⟩ := hcP.2.1
    exact ⟨rneg w R, rneg_in_field w hw hInf R (hcP.1 R hPR),
      negative_member_not_neg w hw hInf P hP R hPR⟩
  · intro R S hR hS hRS hN
    obtain ⟨T, hT, hnPT, hST⟩ := hN.2.2
    exact ⟨hw.1, hR, T, hT, hnPT, rlt_trans w hw hInf R S _ hRS hST⟩
  · intro R hN
    obtain ⟨S, hS, hnPS, hRS⟩ := hN.2.2
    obtain ⟨T, hT, hRT, hTS⟩ := rational_order_dense w hw hInf R _ hRS
    exact ⟨T, ⟨hw.1, hT, S, hS, hnPS, hTS⟩, hRT⟩

include hw in
theorem realNeg_antitone (P Q : ρ → Prop) (hPQ : P ≤ Q) : realNeg w Q ≤ realNeg w P := by
  apply localized_le w hw _ _ (realNeg_supported w Q)
  intro R hR
  obtain ⟨S, hS, hnQS, hRS⟩ := hR.2.2
  exact ⟨hR.1, hR.2.1, S, hS, fun hp => hnQS (incl_of_le hPQ S hp), hRS⟩

include hw hInf in
theorem realNeg_involution (P : ρ → Prop) (hP : RealField w P) : realNeg w (realNeg w P) = P := by
  have hcP := hP.2.2
  apply localized_eq w hw _ _ (realNeg_supported w _) (realCode_supported w _ _ P hP.2)
  intro R
  constructor
  · intro hR
    obtain ⟨S, hS, hnNS, hRS⟩ := hR.2.2
    obtain ⟨T, hT, hRT, hTS⟩ := rational_order_dense w hw hInf R _ hRS
    rcases Classicism.em (P T) with hPT | hnPT
    · exact hcP.2.2.2.1 R T hR.2.1 hT hRT hPT
    · have hST := rneg_reverses w hw hInf T _ hTS
      rw [rneg_involution w hw hInf S hS] at hST
      exact False.elim (hnNS ⟨hw.1, hS, T, hT, hnPT, hST⟩)
  · intro hPR
    obtain ⟨T, hPT, hRT⟩ := hcP.2.2.2.2 R hPR
    have hT := hcP.1 T hPT
    refine ⟨hw.1, hcP.1 R hPR, rneg w T, rneg_in_field w hw hInf T hT,
      negative_member_not_neg w hw hInf P hP T hPT, ?_⟩
    rw [rneg_involution w hw hInf T hT]
    exact hRT

include hw hInf in
theorem realAdd_neg (P : ρ → Prop) (hP : RealField w P) :
    realAdd w P (realNeg w P) = principal w (rzero w) := by
  apply localized_eq w hw _ _ (realAdd_supported w P _)
    (realCode_supported w _ _ _ (principal_real w hw hInf _ (rzero_in_field w hw hInf)))
  intro R
  constructor
  · intro h
    obtain ⟨A, B, hPA, hNB, hG⟩ := h
    obtain ⟨S, hS, hnPS, hBS⟩ := hNB.2.2
    have hAS := member_below_nonmember w hw hInf P hP A S hPA hS hnPS
    have hsum := rlt_add_both w hw hInf A S B (rneg w S) hAS hBS
    rw [hG.2.2.2.2, rplus_neg w hw hInf S hS] at hsum
    exact ⟨hw.1, hG.2.2.2.1, hsum⟩
  · intro hR
    have hE := rneg_reverses w hw hInf R (rzero w) hR.2.2
    rw [rneg_zero w hw hInf] at hE
    obtain ⟨A, B, hA, hB, hPA, hnPB, hgap⟩ := cut_has_small_gap w hw hInf P hP _ hE
    have hdiff := rneg_reverses w hw hInf _ _ hgap
    rw [rneg_involution w hw hInf R hR.2.1, rneg_sub w hw hInf B A hB hA] at hdiff
    have hQB := rlt_add_right w hw hInf R (rsub w A B) (rneg w A) hdiff
      (rneg_in_field w hw hInf A hA)
    change RLt w (rsub w R A) (rsub w (rsub w A B) A) at hQB
    rw [rsub_sub_self w hw hInf A B hA hB] at hQB
    have hQ := rsub_in_field w hw hInf R A hR.2.1 hA
    exact ⟨A, rsub w R A, hPA, ⟨hw.1, hQ, B, hB, hnPB, hQB⟩,
      hw.1, hA, hQ, hR.2.1, radd_sub_cancel_left w hw hInf R A hR.2.1 hA⟩

include hw hInf in
theorem realSub_in_field (P Q : ρ → Prop) (hP : RealField w P) (hQ : RealField w Q) :
    RealField w (realSub w P Q) := realAdd_in_field w hw hInf P _ hP (realNeg_in_field w hw hInf Q hQ)

include hw hInf in
theorem realSub_self (P : ρ → Prop) (hP : RealField w P) :
    realSub w P P = principal w (rzero w) := realAdd_neg w hw hInf P hP

include hw hInf in
theorem realAdd_cancel_right (P Q U : ρ → Prop) (hP : RealField w P)
    (hQ : RealField w Q) (hU : RealField w U)
    (he : realAdd w P U = realAdd w Q U) : P = Q := by
  have he' := congrArg (fun V => realAdd w V (realNeg w U)) he
  rw [realAdd_assoc w hw hInf P U _, realAdd_assoc w hw hInf Q U _,
    realAdd_neg w hw hInf U hU, realAdd_zero_right w hw hInf P hP,
    realAdd_zero_right w hw hInf Q hQ] at he'
  exact he'

include hw hInf in
theorem realAdd_le_iff_le_sub (P Q U : ρ → Prop)
    (hP : RealField w P) (hQ : RealField w Q) (hU : RealField w U) :
    realAdd w P Q ≤ U ↔ P ≤ realSub w U Q := by
  constructor
  · intro h
    have h' := realAdd_mono w hw _ _ _ _ h (le_refl_rel (realNeg w Q))
    rw [realAdd_assoc w hw hInf P Q _, realAdd_neg w hw hInf Q hQ,
      realAdd_zero_right w hw hInf P hP] at h'
    exact h'
  · intro h
    have h' := realAdd_mono w hw _ _ _ _ h (le_refl_rel Q)
    change realAdd w P Q ≤ realAdd w (realAdd w U (realNeg w Q)) Q at h'
    rw [realAdd_assoc w hw hInf U _ Q, realAdd_comm w hw hInf (realNeg w Q) Q,
      realAdd_neg w hw hInf Q hQ, realAdd_zero_right w hw hInf U hU] at h'
    exact h'

end Classicism.Research.ProbabilityConcreteReals
