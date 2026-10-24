import Classicism.Results.Research.AtomicProbabilityNumericMultiplication

/-!
# Concrete nonnegative fraction codes in the actual supported core

A fraction is represented by its supported binary equivalence-class predicate
on pairs of internal natural codes. There is no external quotient, chosen
representative, external Nat, or field axiom. Cross-multiplication transitivity
is proved from the concrete internal numerical laws and nonzero cancellation.
Literal identity of codes follows from actual-world localization.

These are nonnegative fractions. Signed completion, order/density and the
Archimedean construction are still separate work; this file does not claim a
completed rational field. Source: internal-real bridge in the probability notes;
the explicit code/proofs are new formalization work, 22 October 2026.
-/

namespace Classicism.Research.ProbabilityFractions
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ProbabilityNumericOperations

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)

def Valid (w : Prop) (a b : ν) : Prop :=
  Numbers w a ∧ Numbers w b ∧ b ≠ coreZero w

def CrossEq (w : Prop) (a b c d : ν) : Prop := times w a d = times w c b

def fractionCode (w : Prop) (a b : ν) : φ :=
  fun c d => w ∧ Valid w c d ∧ CrossEq w a b c d

def FractionField (w : Prop) : φ → Prop :=
  fun X => w ∧ ∃ a b, Valid w a b ∧ X = fractionCode w a b

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem times_right_comm (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c) :
    times w (times w a b) c = times w (times w a c) b := by
  rw [times_assoc w hw hInf a b c ha hb hc, times_comm w hw hInf b c hb hc,
    ← times_assoc w hw hInf a c b ha hc hb]

include hw hInf in
theorem times_left_comm (a b c : ν) (ha : Numbers w a) (hb : Numbers w b) (hc : Numbers w c) :
    times w a (times w b c) = times w b (times w a c) := by
  rw [← times_assoc w hw hInf a b c ha hb hc, times_comm w hw hInf a b ha hb,
    times_assoc w hw hInf b a c hb ha hc]

include hw hInf in
theorem times_four (a b c d : ν) (ha : Numbers w a) (hb : Numbers w b)
    (hc : Numbers w c) (hd : Numbers w d) :
    times w (times w a b) (times w c d) = times w (times w a c) (times w b d) := by
  rw [times_assoc w hw hInf a b _ ha hb (times_numbers w hw hInf c d hc hd),
    times_left_comm w hw hInf b c d hb hc hd,
    ← times_assoc w hw hInf a c _ ha hc (times_numbers w hw hInf b d hb hd)]

include hw hInf in
theorem times_four_cross (a b c d : ν) (ha : Numbers w a) (hb : Numbers w b)
    (hc : Numbers w c) (hd : Numbers w d) :
    times w (times w a b) (times w c d) = times w (times w a d) (times w b c) := by
  rw [times_comm w hw hInf c d hc hd, times_four w hw hInf a b d c ha hb hd hc]

theorem cross_refl (a b : ν) : CrossEq w a b a b := rfl

theorem cross_symm (a b c d : ν) (h : CrossEq w a b c d) : CrossEq w c d a b := h.symm

include hw hInf in
theorem cross_trans (a b c d e f : ν) (hab : Valid w a b) (hcd : Valid w c d)
    (hef : Valid w e f) (h₁ : CrossEq w a b c d) (h₂ : CrossEq w c d e f) :
    CrossEq w a b e f := by
  apply times_cancel_right w hw hInf (times w a f) (times w e b) d
    (times_numbers w hw hInf a f hab.1 hef.2.1)
    (times_numbers w hw hInf e b hef.1 hab.2.1) hcd.2.1 hcd.2.2
  calc
    times w (times w a f) d = times w (times w a d) f :=
      times_right_comm w hw hInf a f d hab.1 hef.2.1 hcd.2.1
    _ = times w (times w c b) f := congrArg (fun x => times w x f) h₁
    _ = times w (times w c f) b :=
      times_right_comm w hw hInf c b f hcd.1 hab.2.1 hef.2.1
    _ = times w (times w e d) b := congrArg (fun x => times w x b) h₂
    _ = times w (times w e b) d :=
      times_right_comm w hw hInf e d b hef.1 hcd.2.1 hab.2.1

theorem fractionCode_supported (a b : ν) : Supported w (fractionCode w a b) :=
  le_of_box_incl (nec% (fun (c d : ν) (h : fractionCode w a b c d) => h.1))

theorem fractionField_supported : Supported w (FractionField (σ := σ) w) :=
  le_of_box_incl (nec% (fun (X : φ) (h : FractionField w X) => h.1))

include hw in
theorem fractionCode_self (a b : ν) (hab : Valid w a b) : fractionCode w a b a b :=
  ⟨hw.1, hab, rfl⟩

include hw hInf in
theorem fractionCode_identity_iff (a b c d : ν) (hab : Valid w a b) (hcd : Valid w c d) :
    fractionCode w a b = fractionCode w c d ↔ CrossEq w a b c d := by
  constructor
  · intro he
    have h := Eq.mpr (congrFun (congrFun he c) d) (fractionCode_self w hw c d hcd)
    exact h.2.2
  · intro he
    apply localized_eq w hw _ _ (fractionCode_supported w a b) (fractionCode_supported w c d)
    intro x y
    constructor
    · intro h
      exact ⟨h.1, h.2.1, cross_trans w hw hInf c d a b x y hcd hab h.2.1 he.symm h.2.2⟩
    · intro h
      exact ⟨h.1, h.2.1, cross_trans w hw hInf a b c d x y hab hcd h.2.1 he h.2.2⟩

include hw in
theorem fractionCode_in_field (a b : ν) (hab : Valid w a b) :
    FractionField w (fractionCode w a b) := ⟨hw.1, a, b, hab, rfl⟩

theorem field_code_supported (X : φ) (hX : FractionField w X) : Supported w X := by
  obtain ⟨a, b, hab, he⟩ := hX.2
  exact he.symm ▸ fractionCode_supported w a b

def naturalCode (w : Prop) (a : ν) : φ := fractionCode w a (one w)

include hw hInf in
theorem naturalCode_injective (a b : ν) (ha : Numbers w a) (hb : Numbers w b)
    (he : naturalCode w a = naturalCode w b) : a = b := by
  have hcross := (fractionCode_identity_iff w hw hInf a (one w) b (one w)
    ⟨ha, one_numbers w hw, one_ne_zero w hw hInf⟩
    ⟨hb, one_numbers w hw, one_ne_zero w hw hInf⟩).1 he
  change times w a (one w) = times w b (one w) at hcross
  rw [times_one_right w hw hInf a ha, times_one_right w hw hInf b hb] at hcross
  exact hcross

include hw hInf in
theorem fractionCode_zero_iff (a b : ν) (hab : Valid w a b) :
    fractionCode w a b = naturalCode w (coreZero w) ↔ a = coreZero w := by
  constructor
  · intro he
    have hcross := (fractionCode_identity_iff w hw hInf a b (coreZero w) (one w) hab
      ⟨numbers_zero w hw, one_numbers w hw, one_ne_zero w hw hInf⟩).1 he
    change times w a (one w) = times w (coreZero w) b at hcross
    rw [times_one_right w hw hInf a hab.1, times_zero_left w hw hInf b hab.2.1] at hcross
    exact hcross
  · intro ha0
    apply (fractionCode_identity_iff w hw hInf a b (coreZero w) (one w) hab
      ⟨numbers_zero w hw, one_numbers w hw, one_ne_zero w hw hInf⟩).2
    change times w a (one w) = times w (coreZero w) b
    rw [ha0, times_zero_left w hw hInf _ (one_numbers w hw),
      times_zero_left w hw hInf b hab.2.1]

end Classicism.Research.ProbabilityFractions
