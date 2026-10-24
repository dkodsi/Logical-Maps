import Classicism.Results.Research.AtomicProbabilityFractionArchimedean

/-!
# Explicit halving and density in the nonnegative fraction domain

The midpoint is X plus half of its positive additive difference from Y.
Halving uses the concrete reciprocal of one plus one. This discharges the
density resource for the nonnegative domain, with no assumed dense order.
Source: new internal-real bridge formalization, 22 October 2026.
-/

namespace Classicism.Research.ProbabilityFractions
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)

def qtwo (w : Prop) : φ := qplus w (qone w) (qone w)
def qhalf (w : Prop) (X : φ) : φ := qtimes w X (qinverse w (qtwo w))

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem qtwo_in_field : FractionField (σ := σ) w (qtwo w) :=
  qplus_in_field w hw hInf _ _ (qone_in_field w hw hInf) (qone_in_field w hw hInf)

include hw hInf in
theorem qtwo_ne_zero : qtwo (σ := σ) w ≠ qzero w := by
  intro he
  exact qone_ne_zero w hw hInf
    (qplus_eq_zero w hw hInf _ _ (qone_in_field w hw hInf) (qone_in_field w hw hInf) he).1

include hw hInf in
theorem qtimes_two (X : φ) (hX : FractionField w X) : qtimes w X (qtwo w) = qplus w X X := by
  change qtimes w X (qplus w (qone w) (qone w)) = qplus w X X
  rw [qtimes_add w hw hInf X _ _ hX (qone_in_field w hw hInf) (qone_in_field w hw hInf),
    qtimes_one_right w hw hInf X hX]

include hw hInf in
theorem qhalf_in_field (X : φ) (hX : FractionField w X) : FractionField w (qhalf w X) :=
  qtimes_in_field w hw hInf X _ hX
    (qinverse_in_field w hw hInf _ (qtwo_in_field w hw hInf) (qtwo_ne_zero w hw hInf))

include hw hInf in
theorem qhalf_ne_zero (X : φ) (hX : FractionField w X) (hnX : X ≠ qzero w) :
    qhalf w X ≠ qzero w := by
  intro he
  have hI := qinverse_in_field w hw hInf _ (qtwo_in_field w hw hInf) (qtwo_ne_zero w hw hInf)
  rcases qtimes_eq_zero w hw hInf X _ hX hI he with hx | hi
  · exact hnX hx
  · exact qinverse_ne_zero w hw hInf _ (qtwo_in_field w hw hInf) (qtwo_ne_zero w hw hInf) hi

include hw hInf in
theorem qhalf_add_half (X : φ) (hX : FractionField w X) :
    qplus w (qhalf w X) (qhalf w X) = X := by
  have h2 := qtwo_in_field (σ := σ) w hw hInf
  have hn2 := qtwo_ne_zero (σ := σ) w hw hInf
  have hI := qinverse_in_field w hw hInf _ h2 hn2
  calc
    qplus w (qhalf w X) (qhalf w X) = qtimes w (qhalf w X) (qtwo w) :=
      (qtimes_two w hw hInf _ (qhalf_in_field w hw hInf X hX)).symm
    _ = qtimes w X (qtimes w (qinverse w (qtwo w)) (qtwo w)) :=
      qtimes_assoc w hw hInf X _ _ hX hI h2
    _ = qtimes w X (qone w) := by
      rw [qtimes_comm w hw hInf _ _ hI h2, qtimes_inverse w hw hInf _ h2 hn2]
    _ = X := qtimes_one_right w hw hInf X hX

include hw hInf in
theorem qlt_add_nonzero (X Y : φ) (hX : FractionField w X)
    (hY : FractionField w Y) (hnY : Y ≠ qzero w) : QLt w X (qplus w X Y) := by
  refine ⟨⟨hX, qplus_in_field w hw hInf X Y hX hY, Y, hY, rfl⟩, ?_⟩
  intro he
  have he' : qplus w X (qzero w) = qplus w X Y := (qplus_zero_right w hw hInf X hX).trans he
  have h0Y := qplus_cancel_left w hw hInf _ Y X (qzero_in_field w hw hInf) hY hX he'
  exact hnY h0Y.symm

include hw hInf in
theorem fraction_order_dense (X Y : φ) (hXY : QLt w X Y) :
    ∃ M, FractionField w M ∧ QLt w X M ∧ QLt w M Y := by
  obtain ⟨Z, hZ, hXZ⟩ := hXY.1.2.2
  have hnZ : Z ≠ qzero w := by
    intro hz0
    rw [hz0, qplus_zero_right w hw hInf X hXY.1.1] at hXZ
    exact hXY.2 hXZ
  have hH := qhalf_in_field w hw hInf Z hZ
  have hnH := qhalf_ne_zero w hw hInf Z hZ hnZ
  have hM := qplus_in_field w hw hInf X _ hXY.1.1 hH
  refine ⟨qplus w X (qhalf w Z), hM,
    qlt_add_nonzero w hw hInf X _ hXY.1.1 hH hnH, ?_⟩
  have h := qlt_add_nonzero w hw hInf _ _ hM hH hnH
  rw [qplus_assoc w hw hInf X _ _ hXY.1.1 hH hH,
    qhalf_add_half w hw hInf Z hZ, hXZ] at h
  exact h

end Classicism.Research.ProbabilityFractions
