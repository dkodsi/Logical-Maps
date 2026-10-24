import Classicism.Results.Research.AtomicProbabilityNumericAddition

/-! Multiplication, distributivity and nonzero cancellation for the actual
supported numerical operations. These are direct internal C proofs, not an
assumed semiring instance; no external arithmetic library is imported. -/

namespace Classicism.Research.ProbabilityNumericOperations
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ActualityNumericalRelations

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem times_zero_left (b : ν) (hb : Numbers w b) :
    times w (coreZero w) b = coreZero w := by
  apply number_induction w hw (fun n => times w (coreZero w) n = coreZero w) ?_ ?_ b hb
  · exact times_zero_right w hw hInf _ (numbers_zero w hw)
  · intro n hn ih
    rw [times_suc_right w hw hInf _ n (numbers_zero w hw) hn,
      plus_zero_left w hw hInf _ (times_numbers w hw hInf _ n (numbers_zero w hw) hn), ih]

include hw hInf in
theorem times_suc_left (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    times w (coreSuc w a) b = plus w b (times w a b) := by
  apply number_induction w hw (fun n =>
    times w (coreSuc w a) n = plus w n (times w a n)) ?_ ?_ b hb
  · rw [times_zero_right w hw hInf _ (numbers_suc w hw a ha),
      times_zero_right w hw hInf a ha, plus_zero_left w hw hInf _ (numbers_zero w hw)]
  · intro n hn ih
    have htn := times_numbers w hw hInf a n ha hn
    rw [times_suc_right w hw hInf _ n (numbers_suc w hw a ha) hn, ih,
      times_suc_right w hw hInf a n ha hn,
      plus_suc_left w hw hInf a _ ha (plus_numbers w hw hInf n _ hn htn),
      plus_suc_left w hw hInf n _ hn (plus_numbers w hw hInf a _ ha htn)]
    exact congrArg (coreSuc w) (plus_left_comm w hw hInf a n _ ha hn htn)

include hw hInf in
theorem times_comm (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    times w a b = times w b a := by
  apply number_induction w hw (fun n => times w a n = times w n a) ?_ ?_ b hb
  · rw [times_zero_right w hw hInf a ha, times_zero_left w hw hInf a ha]
  · intro n hn ih
    rw [times_suc_right w hw hInf a n ha hn, times_suc_left w hw hInf n a hn ha, ih]

include hw hInf in
theorem times_add (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c) :
    times w a (plus w b c) = plus w (times w a b) (times w a c) := by
  apply number_induction w hw (fun n =>
    times w a (plus w b n) = plus w (times w a b) (times w a n)) ?_ ?_ c hc
  · rw [plus_zero_right w hw hInf b hb, times_zero_right w hw hInf a ha,
      plus_zero_right w hw hInf _ (times_numbers w hw hInf a b ha hb)]
  · intro n hn ih
    rw [plus_suc_right w hw hInf b n hb hn,
      times_suc_right w hw hInf a _ ha (plus_numbers w hw hInf b n hb hn),
      times_suc_right w hw hInf a n ha hn, ih]
    exact plus_left_comm w hw hInf a (times w a b) (times w a n) ha
      (times_numbers w hw hInf a b ha hb) (times_numbers w hw hInf a n ha hn)

include hw hInf in
theorem add_times (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c) :
    times w (plus w a b) c = plus w (times w a c) (times w b c) := by
  rw [times_comm w hw hInf _ c (plus_numbers w hw hInf a b ha hb) hc,
    times_add w hw hInf c a b hc ha hb,
    times_comm w hw hInf c a hc ha, times_comm w hw hInf c b hc hb]

include hw hInf in
theorem times_assoc (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c) :
    times w (times w a b) c = times w a (times w b c) := by
  apply number_induction w hw (fun n =>
    times w (times w a b) n = times w a (times w b n)) ?_ ?_ c hc
  · rw [times_zero_right w hw hInf _ (times_numbers w hw hInf a b ha hb),
      times_zero_right w hw hInf b hb, times_zero_right w hw hInf a ha]
  · intro n hn ih
    rw [times_suc_right w hw hInf _ n (times_numbers w hw hInf a b ha hb) hn,
      times_suc_right w hw hInf b n hb hn,
      times_add w hw hInf a b _ ha hb (times_numbers w hw hInf b n hb hn), ih]

def one (w : Prop) : ν := coreSuc w (coreZero w)

include hw in
theorem one_numbers : Numbers (σ := σ) w (one w) :=
  numbers_suc w hw (coreZero w) (numbers_zero w hw)

include hw hInf in
theorem one_ne_zero : one (σ := σ) w ≠ coreZero w :=
  fun h => core_zero_ne_suc w hw hInf (coreZero w) (numbers_zero w hw) h.symm

include hw hInf in
theorem times_one_right (a : ν) (ha : Numbers w a) : times w a (one w) = a := by
  change times w a (coreSuc w (coreZero w)) = a
  rw [times_suc_right w hw hInf a _ ha (numbers_zero w hw),
    times_zero_right w hw hInf a ha, plus_zero_right w hw hInf a ha]

include hw hInf in
theorem times_one_left (a : ν) (ha : Numbers w a) : times w (one w) a = a := by
  rw [times_comm w hw hInf _ a (one_numbers w hw) ha, times_one_right w hw hInf a ha]

include hw hInf in
theorem times_eq_zero (a b : ν) (ha : Numbers w a) (hb : Numbers w b)
    (he : times w a b = coreZero w) : a = coreZero w ∨ b = coreZero w := by
  refine (number_cases w hw b hb).elim (fun hb0 => ?_) (fun hs => ?_)
  · exact Or.inr hb0
  ·
    obtain ⟨c, hc, hbc⟩ := hs
    have he' : plus w a (times w a c) = coreZero w :=
      (times_suc_right w hw hInf a c ha hc).symm.trans (hbc ▸ he)
    exact Or.inl (plus_eq_zero w hw hInf a _ ha (times_numbers w hw hInf a c ha hc) he').1

include hw hInf in
theorem times_ne_zero (a b : ν) (ha : Numbers w a) (hb : Numbers w b)
    (hna : a ≠ coreZero w) (hnb : b ≠ coreZero w) : times w a b ≠ coreZero w :=
  fun h => (times_eq_zero w hw hInf a b ha hb h).elim hna hnb

include hw hInf in
theorem times_cancel_left (a : ν) (ha : Numbers w a) (hna : a ≠ coreZero w)
    (b : ν) (hb : Numbers w b) :
    ∀ c, Numbers w c → times w a b = times w a c → b = c := by
  apply number_induction w hw (fun n => ∀ c, Numbers w c →
    times w a n = times w a c → n = c) ?_ ?_ b hb
  · intro c hc he
    have hz := he.symm.trans (times_zero_right w hw hInf a ha)
    exact (times_eq_zero w hw hInf a c ha hc hz).elim
      (fun ha0 => False.elim (hna ha0)) (fun hc0 => hc0.symm)
  · intro n hn ih c hc he
    refine (number_cases w hw c hc).elim (fun hc0 => ?_) (fun hs => ?_)
    ·
      have hz := (hc0 ▸ he).trans (times_zero_right w hw hInf a ha)
      exact False.elim (times_ne_zero w hw hInf a (coreSuc w n) ha
        (numbers_suc w hw n hn) hna
        (fun hs => core_zero_ne_suc w hw hInf n hn hs.symm) hz)
    ·
      obtain ⟨d, hd, hcd⟩ := hs
      have he' : times w a (coreSuc w n) = times w a (coreSuc w d) := hcd ▸ he
      rw [times_suc_right w hw hInf a n ha hn, times_suc_right w hw hInf a d ha hd] at he'
      have heq := plus_cancel_left w hw hInf a ha _ _
        (times_numbers w hw hInf a n ha hn) (times_numbers w hw hInf a d ha hd) he'
      exact (congrArg (coreSuc w) (ih d hd heq)).trans hcd.symm

include hw hInf in
theorem times_cancel_right (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c)
    (hnc : c ≠ coreZero w) (he : times w a c = times w b c) : a = b := by
  rw [times_comm w hw hInf a c ha hc, times_comm w hw hInf b c hb hc] at he
  exact times_cancel_left w hw hInf c hc hnc a ha b hb he

end Classicism.Research.ProbabilityNumericOperations
