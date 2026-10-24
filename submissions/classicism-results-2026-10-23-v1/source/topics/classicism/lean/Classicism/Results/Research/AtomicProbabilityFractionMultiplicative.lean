import Classicism.Results.Research.AtomicProbabilityFractionAdditive

/-!
# Multiplication, distributivity and nonzero cancellation of fraction codes

All laws concern the concrete operations already realized by supported union.
Common denominators reduce distributivity and cancellation to the constructed
internal natural arithmetic. No external semiring assumptions are introduced.
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
theorem qtimes_comm (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    qtimes w X Y = qtimes w Y X := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  obtain ⟨c, d, hcd, hYc⟩ := hY.2
  rw [hXa, hYc, qtimes_codes w hw hInf a b c d hab hcd,
    qtimes_codes w hw hInf c d a b hcd hab]
  change fractionCode w (times w a c) (times w b d) =
    fractionCode w (times w c a) (times w d b)
  rw [times_comm w hw hInf a c hab.1 hcd.1,
    times_comm w hw hInf b d hab.2.1 hcd.2.1]

include hw hInf in
theorem qtimes_assoc (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) :
    qtimes w (qtimes w X Y) Z = qtimes w X (qtimes w Y Z) := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  obtain ⟨c, d, hcd, hYc⟩ := hY.2
  obtain ⟨e, f, hef, hZe⟩ := hZ.2
  rw [hXa, hYc, hZe, qtimes_codes w hw hInf a b c d hab hcd,
    qtimes_codes w hw hInf c d e f hcd hef,
    qtimes_codes w hw hInf _ _ e f (product_valid w hw hInf a b c d hab hcd) hef,
    qtimes_codes w hw hInf a b _ _ hab (product_valid w hw hInf c d e f hcd hef)]
  change fractionCode w (times w (times w a c) e) (times w (times w b d) f) =
    fractionCode w (times w a (times w c e)) (times w b (times w d f))
  rw [times_assoc w hw hInf a c e hab.1 hcd.1 hef.1,
    times_assoc w hw hInf b d f hab.2.1 hcd.2.1 hef.2.1]

include hw hInf in
theorem qtimes_one_right (X : φ) (hX : FractionField w X) : qtimes w X (qone w) = X := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  rw [hXa]
  change qtimes w (fractionCode w a b) (fractionCode w (one w) (one w)) = fractionCode w a b
  rw [qtimes_codes w hw hInf a b _ _ hab
    ⟨one_numbers w hw, one_numbers w hw, one_ne_zero w hw hInf⟩]
  change fractionCode w (times w a (one w)) (times w b (one w)) = fractionCode w a b
  rw [times_one_right w hw hInf a hab.1, times_one_right w hw hInf b hab.2.1]

include hw hInf in
theorem qtimes_one_left (X : φ) (hX : FractionField w X) : qtimes w (qone w) X = X := by
  rw [qtimes_comm w hw hInf _ X (qone_in_field w hw hInf) hX,
    qtimes_one_right w hw hInf X hX]

include hw hInf in
theorem qtimes_zero_right (X : φ) (hX : FractionField w X) : qtimes w X (qzero w) = qzero w := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  rw [hXa]
  change qtimes w (fractionCode w a b) (fractionCode w (coreZero w) (one w)) = qzero w
  rw [qtimes_codes w hw hInf a b _ _ hab
    ⟨numbers_zero w hw, one_numbers w hw, one_ne_zero w hw hInf⟩]
  apply (fractionCode_zero_iff w hw hInf _ _
    (product_valid w hw hInf a b _ _ hab
      ⟨numbers_zero w hw, one_numbers w hw, one_ne_zero w hw hInf⟩)).2
  exact times_zero_right w hw hInf a hab.1

include hw hInf in
theorem qtimes_zero_left (X : φ) (hX : FractionField w X) : qtimes w (qzero w) X = qzero w := by
  rw [qtimes_comm w hw hInf _ X (qzero_in_field w hw hInf) hX,
    qtimes_zero_right w hw hInf X hX]

include hw hInf in
theorem qtimes_add (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) :
    qtimes w X (qplus w Y Z) = qplus w (qtimes w X Y) (qtimes w X Z) := by
  obtain ⟨d, a, b, c, hd, hnd, ha, hb, hc, hXa, hYb, hZc⟩ :=
    common_denominator_three w hw hInf X Y Z hX hY hZ
  rw [hXa, hYb, hZc,
    qplus_common_denominator w hw hInf b c d hb hc hd hnd,
    qtimes_codes w hw hInf a d b d ⟨ha, hd, hnd⟩ ⟨hb, hd, hnd⟩,
    qtimes_codes w hw hInf a d c d ⟨ha, hd, hnd⟩ ⟨hc, hd, hnd⟩,
    qtimes_codes w hw hInf a d _ d ⟨ha, hd, hnd⟩ ⟨plus_numbers w hw hInf b c hb hc, hd, hnd⟩]
  change fractionCode w (times w a (plus w b c)) (times w d d) =
    qplus w (fractionCode w (times w a b) (times w d d))
      (fractionCode w (times w a c) (times w d d))
  rw [qplus_common_denominator w hw hInf _ _ _
    (times_numbers w hw hInf a b ha hb) (times_numbers w hw hInf a c ha hc)
    (times_numbers w hw hInf d d hd hd) (times_ne_zero w hw hInf d d hd hd hnd hnd),
    times_add w hw hInf a b c ha hb hc]

include hw hInf in
theorem qadd_times (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) :
    qtimes w (qplus w X Y) Z = qplus w (qtimes w X Z) (qtimes w Y Z) := by
  rw [qtimes_comm w hw hInf _ Z (qplus_in_field w hw hInf X Y hX hY) hZ,
    qtimes_add w hw hInf Z X Y hZ hX hY,
    qtimes_comm w hw hInf Z X hZ hX, qtimes_comm w hw hInf Z Y hZ hY]

include hw hInf in
theorem qtimes_eq_zero (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y)
    (he : qtimes w X Y = qzero w) : X = qzero w ∨ Y = qzero w := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  obtain ⟨c, d, hcd, hYc⟩ := hY.2
  rw [hXa, hYc, qtimes_codes w hw hInf a b c d hab hcd] at he
  have hz := (fractionCode_zero_iff w hw hInf _ _
    (product_valid w hw hInf a b c d hab hcd)).1 he
  rcases times_eq_zero w hw hInf a c hab.1 hcd.1 hz with ha | hc
  · exact Or.inl (hXa.trans ((fractionCode_zero_iff w hw hInf a b hab).2 ha))
  · exact Or.inr (hYc.trans ((fractionCode_zero_iff w hw hInf c d hcd).2 hc))

include hw hInf in
theorem qtimes_cancel_right (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) (hnZ : Z ≠ qzero w)
    (he : qtimes w X Z = qtimes w Y Z) : X = Y := by
  obtain ⟨d, a, b, c, hd, hnd, ha, hb, hc, hXa, hYb, hZc⟩ :=
    common_denominator_three w hw hInf X Y Z hX hY hZ
  have hnc : c ≠ coreZero w := fun hc0 => hnZ
    (hZc.trans ((fractionCode_zero_iff w hw hInf c d ⟨hc, hd, hnd⟩).2 hc0))
  rw [hXa, hYb, hZc,
    qtimes_codes w hw hInf a d c d ⟨ha, hd, hnd⟩ ⟨hc, hd, hnd⟩,
    qtimes_codes w hw hInf b d c d ⟨hb, hd, hnd⟩ ⟨hc, hd, hnd⟩] at he
  have he' := (fractionCode_same_denominator w hw hInf _ _ (times w d d)
    (times_numbers w hw hInf a c ha hc) (times_numbers w hw hInf b c hb hc)
    (times_numbers w hw hInf d d hd hd) (times_ne_zero w hw hInf d d hd hd hnd hnd)).1 he
  have hab := times_cancel_right w hw hInf a b c ha hb hc hnc he'
  exact hXa.trans ((congrArg (fun x => fractionCode w x d) hab).trans hYb.symm)

include hw hInf in
theorem qtimes_cancel_left (X Y Z : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hZ : FractionField w Z) (hnZ : Z ≠ qzero w)
    (he : qtimes w Z X = qtimes w Z Y) : X = Y := by
  apply qtimes_cancel_right w hw hInf X Y Z hX hY hZ hnZ
  rw [qtimes_comm w hw hInf X Z hX hZ, qtimes_comm w hw hInf Y Z hY hZ]
  exact he

end Classicism.Research.ProbabilityFractions
