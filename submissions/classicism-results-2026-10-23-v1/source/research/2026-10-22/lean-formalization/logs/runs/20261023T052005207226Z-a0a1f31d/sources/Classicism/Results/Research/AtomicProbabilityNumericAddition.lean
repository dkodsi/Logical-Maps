import Classicism.Results.Research.AtomicProbabilityNumericOperations

/-! Concrete additive laws on the actual supported number field. No semiring
instance or operation law is assumed: the operations are the terms just defined. -/

namespace Classicism.Research.ProbabilityNumericOperations
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ActualityNumericalRelations

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem plus_zero_left (b : ν) (hb : Numbers w b) : plus w (coreZero w) b = b := by
  apply number_induction w hw (fun n => plus w (coreZero w) n = n) ?_ ?_ b hb
  · exact plus_zero_right w hw hInf (coreZero w) (numbers_zero w hw)
  · intro n hn ih
    rw [plus_suc_right w hw hInf _ n (numbers_zero w hw) hn, ih]

include hw hInf in
theorem plus_suc_left (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    plus w (coreSuc w a) b = coreSuc w (plus w a b) := by
  apply number_induction w hw (fun n =>
    plus w (coreSuc w a) n = coreSuc w (plus w a n)) ?_ ?_ b hb
  · rw [plus_zero_right w hw hInf _ (numbers_suc w hw a ha), plus_zero_right w hw hInf a ha]
  · intro n hn ih
    rw [plus_suc_right w hw hInf _ n (numbers_suc w hw a ha) hn,
      plus_suc_right w hw hInf a n ha hn, ih]

include hw hInf in
theorem plus_comm (a b : ν) (ha : Numbers w a) (hb : Numbers w b) : plus w a b = plus w b a := by
  apply number_induction w hw (fun n => plus w a n = plus w n a) ?_ ?_ b hb
  · rw [plus_zero_right w hw hInf a ha, plus_zero_left w hw hInf a ha]
  · intro n hn ih
    rw [plus_suc_right w hw hInf a n ha hn, plus_suc_left w hw hInf n a hn ha, ih]

include hw hInf in
theorem plus_assoc (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c) :
    plus w (plus w a b) c = plus w a (plus w b c) := by
  apply number_induction w hw (fun n =>
    plus w (plus w a b) n = plus w a (plus w b n)) ?_ ?_ c hc
  · rw [plus_zero_right w hw hInf _ (plus_numbers w hw hInf a b ha hb),
      plus_zero_right w hw hInf b hb]
  · intro n hn ih
    rw [plus_suc_right w hw hInf _ n (plus_numbers w hw hInf a b ha hb) hn,
      plus_suc_right w hw hInf b n hb hn,
      plus_suc_right w hw hInf a _ ha (plus_numbers w hw hInf b n hb hn), ih]

include hw hInf in
theorem plus_left_comm (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c) :
    plus w a (plus w b c) = plus w b (plus w a c) := by
  rw [← plus_assoc w hw hInf a b c ha hb hc, plus_comm w hw hInf a b ha hb,
    plus_assoc w hw hInf b a c hb ha hc]

include hw hInf in
theorem plus_cancel_left (a : ν) (ha : Numbers w a) :
    ∀ b c, Numbers w b → Numbers w c → plus w a b = plus w a c → b = c := by
  apply number_induction w hw (fun n => ∀ b c, Numbers w b → Numbers w c →
    plus w n b = plus w n c → b = c) ?_ ?_ a ha
  · intro b c hb hc he
    exact (plus_zero_left w hw hInf b hb).symm.trans
      (he.trans (plus_zero_left w hw hInf c hc))
  · intro n hn ih b c hb hc he
    rw [plus_suc_left w hw hInf n b hn hb, plus_suc_left w hw hInf n c hn hc] at he
    exact ih b c hb hc (core_suc_injective w hw hInf _ _
      (plus_numbers w hw hInf n b hn hb) (plus_numbers w hw hInf n c hn hc) he)

include hw hInf in
theorem plus_cancel_right (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c)
    (he : plus w a c = plus w b c) : a = b := by
  rw [plus_comm w hw hInf a c ha hc, plus_comm w hw hInf b c hb hc] at he
  exact plus_cancel_left w hw hInf c hc a b ha hb he

include hw hInf in
theorem plus_eq_zero (a b : ν) (ha : Numbers w a) (hb : Numbers w b)
    (he : plus w a b = coreZero w) : a = coreZero w ∧ b = coreZero w := by
  refine (number_cases w hw a ha).elim (fun ha0 => ?_) (fun hs => ?_)
  ·
    subst a
    exact ⟨rfl, (plus_zero_left w hw hInf b hb).symm.trans he⟩
  ·
    obtain ⟨c, hc, hac⟩ := hs
    have he' : coreSuc w (plus w c b) = coreZero w :=
      (plus_suc_left w hw hInf c b hc hb).symm.trans (hac ▸ he)
    exact False.elim (core_zero_ne_suc w hw hInf _ (plus_numbers w hw hInf c b hc hb) he'.symm)

end Classicism.Research.ProbabilityNumericOperations
