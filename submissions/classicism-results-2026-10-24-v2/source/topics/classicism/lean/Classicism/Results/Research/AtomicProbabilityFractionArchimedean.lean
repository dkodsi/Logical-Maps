import Classicism.Results.Research.AtomicProbabilityFractionOrder

/-!
# Internal Archimedean bounds and small reciprocal naturals

The witness is an actual Numbers w code. A fraction a/b is at most the
embedded a because its nonzero natural denominator is at least one; the
successor of a gives a strict bound. Reciprocal order then gives an explicit
existence proof for a reciprocal natural below every positive fraction.
These are current internal assertions, not claims that Numbers is externally
standard or that the signed real construction is already complete.
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
variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem naturalCode_in_field (a : ν) (ha : Numbers w a) : FractionField w (naturalCode w a) :=
  fractionCode_in_field w hw a (one w) ⟨ha, one_numbers w hw, one_ne_zero w hw hInf⟩

include hw hInf in
theorem naturalCode_add (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    qplus w (naturalCode w a) (naturalCode w b) = naturalCode w (plus w a b) :=
  qplus_common_denominator w hw hInf a b (one w) ha hb (one_numbers w hw) (one_ne_zero w hw hInf)

include hw hInf in
theorem naturalCode_mul (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    qtimes w (naturalCode w a) (naturalCode w b) = naturalCode w (times w a b) := by
  change qtimes w (fractionCode w a (one w)) (fractionCode w b (one w)) =
    fractionCode w (times w a b) (one w)
  rw [qtimes_codes w hw hInf a _ b _ ⟨ha, one_numbers w hw, one_ne_zero w hw hInf⟩
    ⟨hb, one_numbers w hw, one_ne_zero w hw hInf⟩]
  change fractionCode w (times w a b) (times w (one w) (one w)) =
    fractionCode w (times w a b) (one w)
  rw [times_one_right w hw hInf _ (one_numbers w hw)]

include hw hInf in
theorem naturalCode_suc (a : ν) (ha : Numbers w a) :
    qplus w (naturalCode w a) (qone w) = naturalCode w (coreSuc w a) := by
  change qplus w (naturalCode w a) (naturalCode w (one w)) = naturalCode w (coreSuc w a)
  rw [naturalCode_add w hw hInf a _ ha (one_numbers w hw), plus_one w hw hInf a ha]

include hw hInf in
theorem naturalCode_lt_suc (a : ν) (ha : Numbers w a) :
    QLt w (naturalCode w a) (naturalCode w (coreSuc w a)) := by
  refine ⟨⟨naturalCode_in_field w hw hInf a ha,
    naturalCode_in_field w hw hInf _ (numbers_suc w hw a ha), qone w,
    qone_in_field w hw hInf, naturalCode_suc w hw hInf a ha⟩, ?_⟩
  intro he
  exact number_ne_successor w hw hInf a ha
    (naturalCode_injective w hw hInf a _ ha (numbers_suc w hw a ha) he)

include hw hInf in
theorem fraction_below_numerator (a b : ν) (hab : Valid w a b) :
    QLe w (fractionCode w a b) (naturalCode w a) := by
  obtain ⟨c, hc, hbc⟩ := (one_le_nonzero w hw hInf b hab.2.1 hab.2.2).2.2
  have hac := times_numbers w hw hInf a c hab.1 hc
  refine ⟨fractionCode_in_field w hw a b hab, naturalCode_in_field w hw hInf a hab.1,
    fractionCode w (times w a c) b, fractionCode_in_field w hw _ b ⟨hac, hab.2.1, hab.2.2⟩, ?_⟩
  rw [qplus_common_denominator w hw hInf a _ b hab.1 hac hab.2.1 hab.2.2]
  apply (fractionCode_identity_iff w hw hInf _ b a (one w)
    ⟨plus_numbers w hw hInf a _ hab.1 hac, hab.2.1, hab.2.2⟩
    ⟨hab.1, one_numbers w hw, one_ne_zero w hw hInf⟩).2
  change times w (plus w a (times w a c)) (one w) = times w a b
  rw [times_one_right w hw hInf _ (plus_numbers w hw hInf a _ hab.1 hac),
    ← hbc, times_add w hw hInf a _ c hab.1 (one_numbers w hw) hc,
    times_one_right w hw hInf a hab.1]

include hw hInf in
theorem fraction_has_natural_bound (X : φ) (hX : FractionField w X) :
    ∃ n, Numbers w n ∧ QLt w X (naturalCode w n) := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  refine ⟨coreSuc w a, numbers_suc w hw a hab.1, ?_⟩
  rw [hXa]
  exact qlt_of_le_of_lt w hw hInf _ _ _ (fraction_below_numerator w hw hInf a b hab)
    (naturalCode_lt_suc w hw hInf a hab.1)

include hw hInf in
theorem reciprocal_natural_small (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    ∃ n, Numbers w n ∧ naturalCode w n ≠ qzero w ∧
      QLt w (qinverse w (naturalCode w n)) X := by
  have hIX := qinverse_in_field w hw hInf X hX hnX
  obtain ⟨n, hn, hbound⟩ := fraction_has_natural_bound w hw hInf _ hIX
  have hn0 : naturalCode w n ≠ qzero w := by
    intro he
    have hIZ : QLe w (qinverse w X) (qzero w) := he ▸ hbound.1
    exact qinverse_ne_zero w hw hInf X hX hnX
      (qle_antisymm w hw hInf _ _ hIZ (qle_zero w hw hInf _ hIX))
  have hsmall := qinverse_strict_antitone w hw hInf _ _ hbound
    (qinverse_ne_zero w hw hInf X hX hnX) hn0
  rw [qinverse_involution w hw hInf X hX hnX] at hsmall
  exact ⟨n, hn, hn0, hsmall⟩

include hw hInf in
theorem natural_multiple_exceeds_one (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    ∃ n, Numbers w n ∧ QLt w (qone w) (qtimes w (naturalCode w n) X) := by
  have hIX := qinverse_in_field w hw hInf X hX hnX
  obtain ⟨n, hn, hbound⟩ := fraction_has_natural_bound w hw hInf _ hIX
  have h := qlt_mul_right w hw hInf _ _ X hbound hX hnX
  rw [qtimes_comm w hw hInf _ X hIX hX, qtimes_inverse w hw hInf X hX hnX] at h
  exact ⟨n, hn, h⟩

end Classicism.Research.ProbabilityFractions
