import Classicism.Results.Research.AtomicProbabilityFractionMultiplicative

/-!
# A concrete reciprocal operation on nonzero nonnegative fractions

Existence is witnessed by exchanging numerator and denominator. Uniqueness
comes from the proved nonzero cancellation law. Supported union then realizes
the reciprocal as a term; no Choice or external inverse axiom is needed.
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

def FractionInv (w : Prop) (X Y : φ) : Prop :=
  w ∧ FractionField w X ∧ FractionField w Y ∧ qtimes w X Y = qone w

def qinverse (w : Prop) (X : φ) : φ :=
  fun a b => w ∧ ∃ Y, FractionInv w X Y ∧ Y a b

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem fraction_reciprocal_product (a b : ν) (hab : Valid w a b) (hna : a ≠ coreZero w) :
    qtimes w (fractionCode w a b) (fractionCode w b a) = qone w := by
  rw [qtimes_codes w hw hInf a b b a hab ⟨hab.2.1, hab.1, hna⟩]
  apply (fractionCode_identity_iff w hw hInf _ _ (one w) (one w)
    (product_valid w hw hInf a b b a hab ⟨hab.2.1, hab.1, hna⟩)
    ⟨one_numbers w hw, one_numbers w hw, one_ne_zero w hw hInf⟩).2
  change times w (times w a b) (one w) = times w (one w) (times w b a)
  rw [times_one_right w hw hInf _ (times_numbers w hw hInf a b hab.1 hab.2.1),
    times_one_left w hw hInf _ (times_numbers w hw hInf b a hab.2.1 hab.1),
    times_comm w hw hInf a b hab.1 hab.2.1]

include hw hInf in
theorem fractionInv_total (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    ∃ Y, FractionInv w X Y := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  have hna : a ≠ coreZero w := fun ha0 => hnX
    (hXa.trans ((fractionCode_zero_iff w hw hInf a b hab).2 ha0))
  refine ⟨fractionCode w b a, hw.1, hX,
    fractionCode_in_field w hw b a ⟨hab.2.1, hab.1, hna⟩, ?_⟩
  rw [hXa]
  exact fraction_reciprocal_product w hw hInf a b hab hna

include hw hInf in
theorem fractionInv_unique (X Y Z : φ) (hnX : X ≠ qzero w)
    (hY : FractionInv w X Y) (hZ : FractionInv w X Z) : Y = Z :=
  qtimes_cancel_left w hw hInf Y Z X hY.2.2.1 hZ.2.2.1 hY.2.1 hnX
    (hY.2.2.2.trans hZ.2.2.2.symm)

theorem qinverse_supported (X : φ) : Supported w (qinverse w X) :=
  le_of_box_incl (nec% (fun (a b : ν) (h : qinverse w X a b) => h.1))

include hw hInf in
theorem qinverse_selected (X Y : φ) (hnX : X ≠ qzero w) (hY : FractionInv w X Y) :
    qinverse w X = Y := by
  apply localized_eq w hw _ _ (qinverse_supported w X) (field_code_supported w Y hY.2.2.1)
  intro a b
  constructor
  · intro h
    obtain ⟨Z, hZ, hz⟩ := h.2
    exact (fractionInv_unique w hw hInf X Z Y hnX hZ hY) ▸ hz
  · intro hy
    exact ⟨hw.1, Y, hY, hy⟩

include hw hInf in
theorem qinverse_in_field (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    FractionField w (qinverse w X) := by
  obtain ⟨Y, hY⟩ := fractionInv_total w hw hInf X hX hnX
  exact (qinverse_selected w hw hInf X Y hnX hY).symm ▸ hY.2.2.1

include hw hInf in
theorem qtimes_inverse (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    qtimes w X (qinverse w X) = qone w := by
  obtain ⟨Y, hY⟩ := fractionInv_total w hw hInf X hX hnX
  rw [qinverse_selected w hw hInf X Y hnX hY]
  exact hY.2.2.2

include hw hInf in
theorem qinverse_ne_zero (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    qinverse w X ≠ qzero w := by
  intro hi0
  have hp := qtimes_inverse w hw hInf X hX hnX
  rw [hi0, qtimes_zero_right w hw hInf X hX] at hp
  exact qone_ne_zero w hw hInf hp.symm

include hw hInf in
theorem qinverse_involution (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    qinverse w (qinverse w X) = X := by
  apply qinverse_selected w hw hInf _ X (qinverse_ne_zero w hw hInf X hX hnX)
  refine ⟨hw.1, qinverse_in_field w hw hInf X hX hnX, hX, ?_⟩
  rw [qtimes_comm w hw hInf _ X (qinverse_in_field w hw hInf X hX hnX) hX]
  exact qtimes_inverse w hw hInf X hX hnX

end Classicism.Research.ProbabilityFractions
