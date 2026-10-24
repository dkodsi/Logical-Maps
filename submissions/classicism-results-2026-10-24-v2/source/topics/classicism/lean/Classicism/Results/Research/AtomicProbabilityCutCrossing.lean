import Classicism.Results.Research.AtomicProbabilityConcreteRealAddition

/-!
# Internal finite-step crossing of a represented cut

Positive steps are embedded nonnegative fraction codes. Their natural
multiples eventually exceed the span between a cut member and a nonmember,
by the constructed rational Archimedean theorem. Internal induction locates
an adjacent crossing. No external list, chosen enumeration or assumed
finite-step crossing principle occurs in the statement or proof.
Source: new internal-real bridge argument, 23 October 2026.
-/

namespace Classicism.Research.ProbabilityCutCrossing
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ProbabilityNumericOperations
open Classicism.Research.ProbabilityFractions
open Classicism.Research.ProbabilityRationals
open Classicism.Research.ProbabilityConcreteReals

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)
local notation "ρ" => (φ → φ → Prop)

def stepTerm (w : Prop) (A : ρ) (X : φ) (n : ν) : ρ :=
  rplus w A (embed w (qtimes w (naturalCode w n) X))

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw in
theorem represented_adjacent_exit (P : ν → Prop) (hz : P (coreZero w)) :
    ∀ n, Numbers w n → ¬ P n →
      ∃ k, Numbers w k ∧ P k ∧ ¬ P (coreSuc w k) := by
  apply number_induction w hw
    (fun n => ¬ P n → ∃ k, Numbers w k ∧ P k ∧ ¬ P (coreSuc w k))
  · intro h
    exact False.elim (h hz)
  · intro n hn ih hnext
    rcases Classicism.em (P n) with hp | hnp
    · exact ⟨n, hn, hp, hnext⟩
    · exact ih hnp

include hw hInf in
theorem natural_multiple_exceeds_fraction (X Y : φ)
    (hX : FractionField w X) (hY : FractionField w Y) (hnX : X ≠ qzero w) :
    ∃ n, Numbers w n ∧ QLt w Y (qtimes w (naturalCode w n) X) := by
  have hI := qinverse_in_field w hw hInf X hX hnX
  obtain ⟨n, hn, hbound⟩ := fraction_has_natural_bound w hw hInf _
    (qtimes_in_field w hw hInf Y _ hY hI)
  have h := qlt_mul_right w hw hInf _ _ X hbound hX hnX
  rw [qtimes_assoc w hw hInf Y _ X hY hI hX,
    qtimes_comm w hw hInf _ X hI hX, qtimes_inverse w hw hInf X hX hnX,
    qtimes_one_right w hw hInf Y hY] at h
  exact ⟨n, hn, h⟩

include hw hInf in
theorem stepTerm_in_field (A : ρ) (X : φ) (n : ν)
    (hA : RationalField w A) (hX : FractionField w X) (hn : Numbers w n) :
    RationalField w (stepTerm w A X n) :=
  rplus_in_field w hw hInf A _ hA (embed_in_field w hw hInf _
    (qtimes_in_field w hw hInf _ X (naturalCode_in_field w hw hInf n hn) hX))

include hw hInf in
theorem stepTerm_zero (A : ρ) (X : φ) (hA : RationalField w A) (hX : FractionField w X) :
    stepTerm w A X (coreZero w) = A := by
  change rplus w A (embed w (qtimes w (qzero w) X)) = A
  rw [qtimes_zero_left w hw hInf X hX, rplus_zero_right w hw hInf A hA]

include hw hInf in
theorem stepTerm_suc (A : ρ) (X : φ) (n : ν)
    (hA : RationalField w A) (hX : FractionField w X) (hn : Numbers w n) :
    stepTerm w A X (coreSuc w n) = rplus w (stepTerm w A X n) (embed w X) := by
  have hN := naturalCode_in_field w hw hInf n hn
  have hNX := qtimes_in_field w hw hInf _ X hN hX
  change rplus w A (embed w (qtimes w (naturalCode w (coreSuc w n)) X)) =
    rplus w (rplus w A (embed w (qtimes w (naturalCode w n) X))) (embed w X)
  rw [← naturalCode_suc w hw hInf n hn,
    qadd_times w hw hInf _ _ X hN (qone_in_field w hw hInf) hX,
    qtimes_one_left w hw hInf X hX, ← embed_add w hw hInf _ X hNX hX]
  exact (rplus_assoc w hw hInf A _ _ hA (embed_in_field w hw hInf _ hNX)
    (embed_in_field w hw hInf X hX)).symm

include hw hInf in
theorem cut_step_eventually_outside (P : ρ → Prop) (hP : RealField w P)
    (A : ρ) (hPA : P A) (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    ∃ n, Numbers w n ∧ ¬ P (stepTerm w A X n) := by
  have hcP := hP.2.2
  have hA := hcP.1 A hPA
  obtain ⟨B, hB, hnPB⟩ := hcP.2.2.1
  have hAB := member_below_nonmember w hw hInf P hP A B hPA hB hnPB
  have hspan := rlt_add_right w hw hInf A B (rneg w A) hAB (rneg_in_field w hw hInf A hA)
  rw [rplus_neg w hw hInf A hA] at hspan
  change RLt w (rzero w) (rsub w B A) at hspan
  obtain ⟨Y, hY, hnY, hspanY⟩ := rational_positive_representation w hw hInf _ hspan
  obtain ⟨n, hn, hbound⟩ := natural_multiple_exceeds_fraction w hw hInf X Y hX hY hnX
  have hbound' := rlt_add_left w hw hInf _ _ A (embed_strict_order w hw hInf _ _ hbound) hA
  have hab : rplus w A (embed w Y) = B := by
    rw [← hspanY]
    exact radd_sub_cancel_left w hw hInf B A hB hA
  rw [hab] at hbound'
  refine ⟨n, hn, ?_⟩
  intro hPn
  exact hnPB (hcP.2.2.2.1 B (stepTerm w A X n) hB
    (stepTerm_in_field w hw hInf A X n hA hX hn) hbound' hPn)

include hw hInf in
theorem cut_has_adjacent_step (P : ρ → Prop) (hP : RealField w P)
    (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    ∃ A B, RationalField w A ∧ RationalField w B ∧
      P A ∧ ¬ P B ∧ B = rplus w A (embed w X) := by
  have hcP := hP.2.2
  obtain ⟨C, hPC⟩ := hcP.2.1
  have hC := hcP.1 C hPC
  obtain ⟨n, hn, hPn⟩ := cut_step_eventually_outside w hw hInf P hP C hPC X hX hnX
  have hz : P (stepTerm w C X (coreZero w)) :=
    (stepTerm_zero w hw hInf C X hC hX).symm ▸ hPC
  obtain ⟨k, hk, hPk, hPnext⟩ := represented_adjacent_exit w hw
    (fun n => P (stepTerm w C X n)) hz n hn hPn
  exact ⟨stepTerm w C X k, stepTerm w C X (coreSuc w k),
    stepTerm_in_field w hw hInf C X k hC hX hk,
    stepTerm_in_field w hw hInf C X _ hC hX (numbers_suc w hw k hk),
    hPk, hPnext, stepTerm_suc w hw hInf C X k hC hX hk⟩

include hw hInf in
theorem cut_has_small_gap (P : ρ → Prop) (hP : RealField w P)
    (E : ρ) (hE : RLt w (rzero w) E) :
    ∃ A B, RationalField w A ∧ RationalField w B ∧ P A ∧ ¬ P B ∧
      RLt w (rsub w B A) E := by
  obtain ⟨X, hX, hnX, he⟩ := rational_positive_representation w hw hInf E hE
  have hH := qhalf_in_field w hw hInf X hX
  have hnH := qhalf_ne_zero w hw hInf X hX hnX
  obtain ⟨A, B, hA, hB, hPA, hnPB, hab⟩ := cut_has_adjacent_step w hw hInf P hP _ hH hnH
  have hhalf := qlt_add_nonzero w hw hInf _ _ hH hH hnH
  rw [qhalf_add_half w hw hInf X hX] at hhalf
  have hgap : rsub w B A = embed w (qhalf w X) := by
    rw [hab, rplus_comm w hw hInf A _ hA (embed_in_field w hw hInf _ hH)]
    exact radd_sub_cancel w hw hInf _ A (embed_in_field w hw hInf _ hH) hA
  refine ⟨A, B, hA, hB, hPA, hnPB, ?_⟩
  rw [hgap, he]
  exact embed_strict_order w hw hInf _ _ hhalf

end Classicism.Research.ProbabilityCutCrossing
