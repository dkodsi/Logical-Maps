import Classicism.Results.Research.AtomicProbabilityFractionArithmetic

/-!
# Common denominators and the cancellative additive fraction monoid

The shared denominators are explicit products of internal numbers. All
existential witnesses below are constructed from the witnesses already in
FractionField; no representative selection operation or choice is used.
These are current C-language claims under ActualWorld and quantified Infinity.
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
theorem fractionCode_scale (a b c : ν) (hab : Valid w a b)
    (hc : Numbers w c) (hnc : c ≠ coreZero w) :
    fractionCode w a b = fractionCode w (times w a c) (times w b c) := by
  apply (fractionCode_identity_iff w hw hInf _ _ _ _ hab
    ⟨times_numbers w hw hInf a c hab.1 hc,
      times_numbers w hw hInf b c hab.2.1 hc,
      times_ne_zero w hw hInf b c hab.2.1 hc hab.2.2 hnc⟩).2
  change times w a (times w b c) = times w (times w a c) b
  exact (times_assoc w hw hInf a b c hab.1 hab.2.1 hc).symm.trans
    (times_right_comm w hw hInf a b c hab.1 hab.2.1 hc)

include hw hInf in
theorem fractionCode_same_denominator (a b d : ν) (ha : Numbers w a)
    (hb : Numbers w b) (hd : Numbers w d) (hnd : d ≠ coreZero w) :
    fractionCode w a d = fractionCode w b d ↔ a = b := by
  constructor
  · intro he
    exact times_cancel_right w hw hInf a b d ha hb hd hnd
      ((fractionCode_identity_iff w hw hInf a d b d ⟨ha, hd, hnd⟩ ⟨hb, hd, hnd⟩).1 he)
  · intro he
    exact congrArg (fun x => fractionCode w x d) he

include hw hInf in
theorem common_denominator_two (X Y : φ) (hX : FractionField w X)
    (hY : FractionField w Y) :
    ∃ d a b, Numbers w d ∧ d ≠ coreZero w ∧ Numbers w a ∧ Numbers w b ∧
      X = fractionCode w a d ∧ Y = fractionCode w b d := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  obtain ⟨c, d, hcd, hYc⟩ := hY.2
  refine ⟨times w b d, times w a d, times w c b,
    times_numbers w hw hInf b d hab.2.1 hcd.2.1,
    times_ne_zero w hw hInf b d hab.2.1 hcd.2.1 hab.2.2 hcd.2.2,
    times_numbers w hw hInf a d hab.1 hcd.2.1,
    times_numbers w hw hInf c b hcd.1 hab.2.1,
    hXa.trans (fractionCode_scale w hw hInf a b d hab hcd.2.1 hcd.2.2), ?_⟩
  have he := hYc.trans (fractionCode_scale w hw hInf c d b hcd hab.2.1 hab.2.2)
  rw [times_comm w hw hInf d b hcd.2.1 hab.2.1] at he
  exact he

include hw hInf in
theorem common_denominator_three (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) :
    ∃ d a b c, Numbers w d ∧ d ≠ coreZero w ∧
      Numbers w a ∧ Numbers w b ∧ Numbers w c ∧
      X = fractionCode w a d ∧ Y = fractionCode w b d ∧ Z = fractionCode w c d := by
  obtain ⟨d, a, b, hd, hnd, ha, hb, hXa, hYb⟩ :=
    common_denominator_two w hw hInf X Y hX hY
  obtain ⟨c, e, hce, hZc⟩ := hZ.2
  refine ⟨times w d e, times w a e, times w b e, times w c d,
    times_numbers w hw hInf d e hd hce.2.1,
    times_ne_zero w hw hInf d e hd hce.2.1 hnd hce.2.2,
    times_numbers w hw hInf a e ha hce.2.1,
    times_numbers w hw hInf b e hb hce.2.1,
    times_numbers w hw hInf c d hce.1 hd,
    hXa.trans (fractionCode_scale w hw hInf a d e ⟨ha, hd, hnd⟩ hce.2.1 hce.2.2),
    hYb.trans (fractionCode_scale w hw hInf b d e ⟨hb, hd, hnd⟩ hce.2.1 hce.2.2), ?_⟩
  have he := hZc.trans (fractionCode_scale w hw hInf c e d hce hd hnd)
  rw [times_comm w hw hInf e d hce.2.1 hd] at he
  exact he

include hw hInf in
theorem qplus_common_denominator (a b d : ν) (ha : Numbers w a)
    (hb : Numbers w b) (hd : Numbers w d) (hnd : d ≠ coreZero w) :
    qplus w (fractionCode w a d) (fractionCode w b d) = fractionCode w (plus w a b) d := by
  calc
    qplus w (fractionCode w a d) (fractionCode w b d) =
        fractionCode w (plus w (times w a d) (times w b d)) (times w d d) :=
      qplus_codes w hw hInf a d b d ⟨ha, hd, hnd⟩ ⟨hb, hd, hnd⟩
    _ = fractionCode w (times w (plus w a b) d) (times w d d) :=
      congrArg (fun x => fractionCode w x (times w d d))
        (add_times w hw hInf a b d ha hb hd).symm
    _ = fractionCode w (plus w a b) d :=
      (fractionCode_scale w hw hInf _ d d
        ⟨plus_numbers w hw hInf a b ha hb, hd, hnd⟩ hd hnd).symm

def qzero (w : Prop) : φ := naturalCode w (coreZero w)
def qone (w : Prop) : φ := naturalCode w (one w)

include hw hInf in
theorem qzero_in_field : FractionField (σ := σ) w (qzero w) :=
  fractionCode_in_field w hw _ _
    ⟨numbers_zero w hw, one_numbers w hw, one_ne_zero w hw hInf⟩

include hw hInf in
theorem qone_in_field : FractionField (σ := σ) w (qone w) :=
  fractionCode_in_field w hw _ _
    ⟨one_numbers w hw, one_numbers w hw, one_ne_zero w hw hInf⟩

include hw hInf in
theorem qone_ne_zero : qone (σ := σ) w ≠ qzero w := by
  intro he
  exact one_ne_zero w hw hInf
    (naturalCode_injective w hw hInf _ _ (one_numbers w hw) (numbers_zero w hw) he)

include hw hInf in
theorem qplus_comm (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    qplus w X Y = qplus w Y X := by
  obtain ⟨d, a, b, hd, hnd, ha, hb, hXa, hYb⟩ :=
    common_denominator_two w hw hInf X Y hX hY
  rw [hXa, hYb, qplus_common_denominator w hw hInf a b d ha hb hd hnd,
    qplus_common_denominator w hw hInf b a d hb ha hd hnd,
    plus_comm w hw hInf a b ha hb]

include hw hInf in
theorem qplus_assoc (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) :
    qplus w (qplus w X Y) Z = qplus w X (qplus w Y Z) := by
  obtain ⟨d, a, b, c, hd, hnd, ha, hb, hc, hXa, hYb, hZc⟩ :=
    common_denominator_three w hw hInf X Y Z hX hY hZ
  rw [hXa, hYb, hZc,
    qplus_common_denominator w hw hInf a b d ha hb hd hnd,
    qplus_common_denominator w hw hInf b c d hb hc hd hnd,
    qplus_common_denominator w hw hInf _ c d (plus_numbers w hw hInf a b ha hb) hc hd hnd,
    qplus_common_denominator w hw hInf a _ d ha (plus_numbers w hw hInf b c hb hc) hd hnd,
    plus_assoc w hw hInf a b c ha hb hc]

include hw hInf in
theorem qplus_zero_right (X : φ) (hX : FractionField w X) : qplus w X (qzero w) = X := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  have hz := (fractionCode_zero_iff w hw hInf (coreZero w) b
    ⟨numbers_zero w hw, hab.2.1, hab.2.2⟩).2 rfl
  change fractionCode w (coreZero w) b = qzero w at hz
  rw [hXa, ← hz,
    qplus_common_denominator w hw hInf a _ b hab.1 (numbers_zero w hw) hab.2.1 hab.2.2,
    plus_zero_right w hw hInf a hab.1]

include hw hInf in
theorem qplus_zero_left (X : φ) (hX : FractionField w X) : qplus w (qzero w) X = X := by
  rw [qplus_comm w hw hInf _ X (qzero_in_field w hw hInf) hX,
    qplus_zero_right w hw hInf X hX]

include hw hInf in
theorem qplus_cancel_right (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z)
    (he : qplus w X Z = qplus w Y Z) : X = Y := by
  obtain ⟨d, a, b, c, hd, hnd, ha, hb, hc, hXa, hYb, hZc⟩ :=
    common_denominator_three w hw hInf X Y Z hX hY hZ
  rw [hXa, hYb, hZc,
    qplus_common_denominator w hw hInf a c d ha hc hd hnd,
    qplus_common_denominator w hw hInf b c d hb hc hd hnd] at he
  have he' := (fractionCode_same_denominator w hw hInf _ _ d
    (plus_numbers w hw hInf a c ha hc) (plus_numbers w hw hInf b c hb hc) hd hnd).1 he
  have hab := plus_cancel_right w hw hInf a b c ha hb hc he'
  exact hXa.trans ((congrArg (fun x => fractionCode w x d) hab).trans hYb.symm)

include hw hInf in
theorem qplus_cancel_left (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z)
    (he : qplus w Z X = qplus w Z Y) : X = Y := by
  apply qplus_cancel_right w hw hInf X Y Z hX hY hZ
  rw [qplus_comm w hw hInf X Z hX hZ, qplus_comm w hw hInf Y Z hY hZ]
  exact he

include hw hInf in
theorem qplus_eq_zero (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y)
    (he : qplus w X Y = qzero w) : X = qzero w ∧ Y = qzero w := by
  obtain ⟨d, a, b, hd, hnd, ha, hb, hXa, hYb⟩ :=
    common_denominator_two w hw hInf X Y hX hY
  rw [hXa, hYb, qplus_common_denominator w hw hInf a b d ha hb hd hnd] at he
  have hz := (fractionCode_zero_iff w hw hInf _ d
    ⟨plus_numbers w hw hInf a b ha hb, hd, hnd⟩).1 he
  have hab := plus_eq_zero w hw hInf a b ha hb hz
  exact ⟨hXa.trans ((fractionCode_zero_iff w hw hInf a d ⟨ha, hd, hnd⟩).2 hab.1),
    hYb.trans ((fractionCode_zero_iff w hw hInf b d ⟨hb, hd, hnd⟩).2 hab.2)⟩

include hw hInf in
theorem qplus_right_comm (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) :
    qplus w (qplus w X Y) Z = qplus w (qplus w X Z) Y := by
  rw [qplus_assoc w hw hInf X Y Z hX hY hZ, qplus_comm w hw hInf Y Z hY hZ,
    ← qplus_assoc w hw hInf X Z Y hX hZ hY]

include hw hInf in
theorem qplus_left_comm (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) :
    qplus w X (qplus w Y Z) = qplus w Y (qplus w X Z) := by
  rw [← qplus_assoc w hw hInf X Y Z hX hY hZ, qplus_comm w hw hInf X Y hX hY,
    qplus_assoc w hw hInf Y X Z hY hX hZ]

include hw hInf in
theorem qplus_four (X Y Z T : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) (hT : FractionField w T) :
    qplus w (qplus w X Y) (qplus w Z T) = qplus w (qplus w X Z) (qplus w Y T) := by
  rw [qplus_assoc w hw hInf X Y _ hX hY (qplus_in_field w hw hInf Z T hZ hT),
    qplus_left_comm w hw hInf Y Z T hY hZ hT,
    ← qplus_assoc w hw hInf X Z _ hX hZ (qplus_in_field w hw hInf Y T hY hT)]

end Classicism.Research.ProbabilityFractions
