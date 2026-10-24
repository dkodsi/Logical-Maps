import Classicism.Results.Research.AtomicProbabilityNumericMultiplication

/-!
# Additive comparison of actual internal numbers

Totality is proved by internal number induction and predecessor cases. The
positive lower bound by one is explicit. The domain is Numbers w, not Lean Nat.
Source: new internal-real bridge formalization, 22 October 2026.
-/

namespace Classicism.Research.ProbabilityNumericOperations
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)

def NLe (w : Prop) (a b : ν) : Prop :=
  Numbers w a ∧ Numbers w b ∧ ∃ c, Numbers w c ∧ plus w a c = b

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem nle_refl (a : ν) (ha : Numbers w a) : NLe w a a :=
  ⟨ha, ha, coreZero w, numbers_zero w hw, plus_zero_right w hw hInf a ha⟩

include hw hInf in
theorem nle_zero (a : ν) (ha : Numbers w a) : NLe w (coreZero w) a :=
  ⟨numbers_zero w hw, ha, a, ha, plus_zero_left w hw hInf a ha⟩

include hw hInf in
theorem nle_total (a b : ν) (ha : Numbers w a) (hb : Numbers w b) :
    NLe w a b ∨ NLe w b a := by
  refine number_induction w hw (fun a => ∀ b, Numbers w b → NLe w a b ∨ NLe w b a)
    (fun b hb => Or.inl (nle_zero w hw hInf b hb)) ?_ a ha b hb
  intro a ha ih b hb
  refine (number_cases w hw b hb).elim (fun hb0 => ?_) (fun hs => ?_)
  · exact Or.inr (hb0.symm ▸ nle_zero w hw hInf _ (numbers_suc w hw a ha))
  · obtain ⟨c, hc, hbc⟩ := hs
    refine (ih c hc).elim (fun hac => ?_) (fun hca => ?_)
    · obtain ⟨d, hd, had⟩ := hac.2.2
      exact Or.inl ⟨numbers_suc w hw a ha, hb, d, hd,
        (plus_suc_left w hw hInf a d ha hd).trans
          ((congrArg (coreSuc w) had).trans hbc.symm)⟩
    · obtain ⟨d, hd, hcd⟩ := hca.2.2
      refine Or.inr ⟨hb, numbers_suc w hw a ha, d, hd, ?_⟩
      rw [hbc, plus_suc_left w hw hInf c d hc hd, hcd]

include hw hInf in
theorem nle_trans (a b c : ν) (hab : NLe w a b) (hbc : NLe w b c) : NLe w a c := by
  obtain ⟨d, hd, had⟩ := hab.2.2
  obtain ⟨e, he, hbe⟩ := hbc.2.2
  refine ⟨hab.1, hbc.2.1, plus w d e, plus_numbers w hw hInf d e hd he, ?_⟩
  rw [← plus_assoc w hw hInf a d e hab.1 hd he, had, hbe]

include hw hInf in
theorem nle_antisymm (a b : ν) (hab : NLe w a b) (hba : NLe w b a) : a = b := by
  obtain ⟨c, hc, hac⟩ := hab.2.2
  obtain ⟨d, hd, hbd⟩ := hba.2.2
  have hsum : plus w a (plus w c d) = plus w a (coreZero w) := by
    rw [← plus_assoc w hw hInf a c d hab.1 hc hd, hac, hbd,
      plus_zero_right w hw hInf a hab.1]
  have hcd := plus_cancel_left w hw hInf a hab.1 _ _
    (plus_numbers w hw hInf c d hc hd) (numbers_zero w hw) hsum
  have hc0 := (plus_eq_zero w hw hInf c d hc hd hcd).1
  rw [hc0, plus_zero_right w hw hInf a hab.1] at hac
  exact hac

include hw hInf in
theorem one_le_nonzero (a : ν) (ha : Numbers w a) (hna : a ≠ coreZero w) :
    NLe w (one w) a := by
  refine (number_cases w hw a ha).elim (fun ha0 => ?_) (fun hs => ?_)
  · exact False.elim (hna ha0)
  · obtain ⟨b, hb, hab⟩ := hs
    refine ⟨one_numbers w hw, ha, b, hb, ?_⟩
    change plus w (coreSuc w (coreZero w)) b = a
    rw [plus_suc_left w hw hInf _ b (numbers_zero w hw) hb,
      plus_zero_left w hw hInf b hb, ← hab]

include hw hInf in
theorem plus_one (a : ν) (ha : Numbers w a) : plus w a (one w) = coreSuc w a := by
  change plus w a (coreSuc w (coreZero w)) = coreSuc w a
  rw [plus_suc_right w hw hInf a _ ha (numbers_zero w hw), plus_zero_right w hw hInf a ha]

include hw hInf in
theorem number_ne_successor (a : ν) (ha : Numbers w a) : a ≠ coreSuc w a := by
  intro he
  have hp : plus w a (one w) = plus w a (coreZero w) :=
    (plus_one w hw hInf a ha).trans (he.symm.trans (plus_zero_right w hw hInf a ha).symm)
  exact one_ne_zero w hw hInf
    (plus_cancel_left w hw hInf a ha _ _ (one_numbers w hw) (numbers_zero w hw) hp)

end Classicism.Research.ProbabilityNumericOperations
