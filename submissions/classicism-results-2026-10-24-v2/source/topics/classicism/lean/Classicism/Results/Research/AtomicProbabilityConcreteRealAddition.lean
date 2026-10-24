import Classicism.Results.Research.AtomicProbabilityConcreteReals
import Classicism.Results.Research.AtomicProbabilityRationalTranslation

/-!
# Concrete addition of the supported rational cuts

The represented rational graph supplies all arithmetic used here. Addition
preserves proper rounded cuts, is literally associative and commutative,
has the principal zero cut as identity, is monotone, and commutes with the
represented union-supremum operation. No assumed cut operation/field is used.
Additive inverses and multiplicative real structure are separate obligations.
Source: new internal-real bridge formalization, 23 October 2026.
-/

namespace Classicism.Research.ProbabilityConcreteReals
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ProbabilityRationals
open Classicism.Research.ProbabilityCuts
open Classicism.Research.ProbabilitySupportedReals

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)
local notation "ρ" => (φ → φ → Prop)

def realAdd (w : Prop) (P Q : ρ → Prop) : ρ → Prop := cutAdd (RationalSumGraph w) P Q
def realAddFamily (w : Prop) (F : (ρ → Prop) → Prop) (Q : ρ → Prop) : (ρ → Prop) → Prop :=
  fun T => w ∧ ∃ P, F P ∧ T = realAdd w P Q

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

theorem realAdd_below (P Q : ρ → Prop) : realAdd w P Q ≤ BaseSupport w (RationalField w) :=
  le_of_box_incl (nec% (fun (R : ρ) (h : realAdd w P Q R) => by
    obtain ⟨A, B, hA, hB, hG⟩ := h
    exact ⟨hG.1, hG.2.2.2.1⟩))

theorem realAdd_supported (P Q : ρ → Prop) : Supported w (realAdd w P Q) :=
  le_trans_rel _ _ _ (realAdd_below w P Q) (baseSupport_supported w (RationalField w))

include hw hInf in
theorem member_below_nonmember (P : ρ → Prop) (hP : RealField w P)
    (R S : ρ) (hPR : P R) (hS : RationalField w S) (hnPS : ¬ P S) : RLt w R S := by
  have hc := hP.2.2
  have hR := hc.1 R hPR
  rcases rle_total w hw hInf R S hR hS with hRS | hSR
  · refine ⟨hRS, ?_⟩
    intro he
    exact hnPS (he ▸ hPR)
  · rcases Classicism.em (S = R) with he | hne
    · exact False.elim (hnPS (he.symm ▸ hPR))
    · exact False.elim (hnPS (hc.2.2.2.1 S R hS hR ⟨hSR, hne⟩ hPR))

include hw hInf in
theorem realAdd_in_field (P Q : ρ → Prop) (hP : RealField w P) (hQ : RealField w Q) :
    RealField w (realAdd w P Q) := by
  have hcP := hP.2.2
  have hcQ := hQ.2.2
  refine ⟨hw.1, realAdd_below w P Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro R h
    obtain ⟨A, B, hA, hB, hG⟩ := h
    exact hG.2.2.2.1
  · obtain ⟨A, hPA⟩ := hcP.2.1
    obtain ⟨B, hQB⟩ := hcQ.2.1
    have hA := hcP.1 A hPA
    have hB := hcQ.1 B hQB
    exact ⟨rplus w A B, A, B, hPA, hQB, hw.1, hA, hB,
      rplus_in_field w hw hInf A B hA hB, rfl⟩
  · obtain ⟨A, hA, hnPA⟩ := hcP.2.2.1
    obtain ⟨B, hB, hnQB⟩ := hcQ.2.2.1
    refine ⟨rplus w A B, rplus_in_field w hw hInf A B hA hB, ?_⟩
    intro h
    obtain ⟨C, D, hPC, hQD, hG⟩ := h
    have hlt := rlt_add_both w hw hInf C A D B
      (member_below_nonmember w hw hInf P hP C A hPC hA hnPA)
      (member_below_nonmember w hw hInf Q hQ D B hQD hB hnQB)
    exact hlt.2 hG.2.2.2.2
  · intro R S hR hS hRS hsum
    obtain ⟨A, B, hPA, hQB, hG⟩ := hsum
    have hA := hG.2.1
    have hB := hG.2.2.1
    have hT := rsub_in_field w hw hInf R B hR hB
    have hTA := rlt_add_right w hw hInf R S (rneg w B) hRS (rneg_in_field w hw hInf B hB)
    change RLt w (rsub w R B) (rsub w S B) at hTA
    rw [← hG.2.2.2.2, radd_sub_cancel w hw hInf A B hA hB] at hTA
    refine ⟨rsub w R B, B, hcP.2.2.2.1 _ A hT hA hTA hPA, hQB,
      hw.1, hT, hB, hR, rsub_add_cancel w hw hInf R B hR hB⟩
  · intro R hsum
    obtain ⟨A, B, hPA, hQB, hG⟩ := hsum
    obtain ⟨C, hPC, hAC⟩ := hcP.2.2.2.2 A hPA
    have hC := hcP.1 C hPC
    have hB := hG.2.2.1
    have hlt := rlt_add_right w hw hInf A C B hAC hB
    rw [hG.2.2.2.2] at hlt
    exact ⟨rplus w C B,
      ⟨C, B, hPC, hQB, hw.1, hC, hB, rplus_in_field w hw hInf C B hC hB, rfl⟩, hlt⟩

include hw hInf in
theorem realAdd_comm (P Q : ρ → Prop) : realAdd w P Q = realAdd w Q P :=
  localized_eq w hw _ _ (realAdd_supported w P Q) (realAdd_supported w Q P)
    (cutAdd_comm (RationalSumGraph w) (rationalSumGraph_comm w hw hInf) P Q)

include hw hInf in
theorem realAdd_assoc (P Q U : ρ → Prop) :
    realAdd w (realAdd w P Q) U = realAdd w P (realAdd w Q U) :=
  localized_eq w hw _ _ (realAdd_supported w _ U) (realAdd_supported w P _)
    (cutAdd_assoc (RationalSumGraph w) (rationalSumGraph_associative w hw hInf) P Q U)

include hw in
theorem realAdd_mono (P Q U V : ρ → Prop) (hPU : P ≤ U) (hQV : Q ≤ V) :
    realAdd w P Q ≤ realAdd w U V :=
  localized_le w hw _ _ (realAdd_supported w P Q)
    (cutAdd_mono (RationalSumGraph w) P Q U V (incl_of_le hPU) (incl_of_le hQV))

include hw hInf in
theorem realAdd_zero_right (P : ρ → Prop) (hP : RealField w P) :
    realAdd w P (principal w (rzero w)) = P := by
  have hcP := hP.2.2
  apply localized_eq w hw _ _ (realAdd_supported w P _) (realCode_supported w _ _ P hP.2)
  intro R
  constructor
  · intro h
    obtain ⟨A, B, hPA, hQB, hG⟩ := h
    have h := rlt_add_right w hw hInf B (rzero w) A hQB.2.2 hG.2.1
    rw [rplus_comm w hw hInf B A hG.2.2.1 hG.2.1,
      rplus_zero_left w hw hInf A hG.2.1, hG.2.2.2.2] at h
    exact hcP.2.2.2.1 R A hG.2.2.2.1 hG.2.1 h hPA
  · intro hPR
    obtain ⟨A, hPA, hRA⟩ := hcP.2.2.2.2 R hPR
    have hR := hcP.1 R hPR
    have hA := hcP.1 A hPA
    have hB := rsub_in_field w hw hInf R A hR hA
    exact ⟨A, rsub w R A, hPA, ⟨hw.1, hB, rsub_lt_zero w hw hInf R A hRA⟩,
      hw.1, hA, hB, hR, radd_sub_cancel_left w hw hInf R A hR hA⟩

include hw hInf in
theorem realAdd_zero_left (P : ρ → Prop) (hP : RealField w P) :
    realAdd w (principal w (rzero w)) P = P := by
  rw [realAdd_comm w hw hInf _ P, realAdd_zero_right w hw hInf P hP]

include hw in
theorem realAdd_sup_left (F : (ρ → Prop) → Prop) (Q : ρ → Prop) :
    realAdd w (realSup w F) Q = realSup w (realAddFamily w F Q) := by
  have hsup : Supported w (realSup w (realAddFamily w F Q)) :=
    le_trans_rel _ _ _ (supremum_below w (RationalField w) _) (baseSupport_supported w (RationalField w))
  apply localized_eq w hw _ _ (realAdd_supported w _ Q) hsup
  intro R
  constructor
  · intro h
    obtain ⟨A, B, hA, hB, hG⟩ := h
    obtain ⟨P, hFP, hPA⟩ := hA.2.2
    exact ⟨hw.1, hG.2.2.2.1, realAdd w P Q, ⟨hw.1, P, hFP, rfl⟩,
      A, B, hPA, hB, hG⟩
  · intro h
    obtain ⟨T, hT, hTR⟩ := h.2.2
    obtain ⟨P, hFP, hTe⟩ := hT.2
    rw [hTe] at hTR
    obtain ⟨A, B, hPA, hB, hG⟩ := hTR
    exact ⟨A, B, ⟨hw.1, hG.2.1, P, hFP, hPA⟩, hB, hG⟩

end Classicism.Research.ProbabilityConcreteReals
