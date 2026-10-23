import Classicism.Results.Research.AtomicProbabilitySignedRationals

/-!
# The additive group on the represented signed rational domain

Addition is realized by the supported union of its proved single-valued graph;
negation is the explicit transpose of the difference-class predicate. These
are terms at admitted relational types, not selected external representatives.
Source: new internal-real bridge formalization, 22 October 2026.
-/

namespace Classicism.Research.ProbabilityRationals
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ProbabilityFractions

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)
local notation "ρ" => (φ → φ → Prop)

def RationalAdd (w : Prop) (R S U : ρ) : Prop :=
  w ∧ ∃ A B C D, FractionField w A ∧ FractionField w B ∧
    FractionField w C ∧ FractionField w D ∧ R = signedCode w A B ∧
    S = signedCode w C D ∧ U = signedCode w (qplus w A C) (qplus w B D)

def rplus (w : Prop) (R S : ρ) : ρ := fun A B => w ∧ ∃ U, RationalAdd w R S U ∧ U A B
def rneg (w : Prop) (R : ρ) : ρ := fun A B => w ∧ R B A

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem rationalAdd_total (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    ∃ U, RationalField w U ∧ RationalAdd w R S U := by
  obtain ⟨A, B, hA, hB, hRa⟩ := hR.2
  obtain ⟨C, D, hC, hD, hSc⟩ := hS.2
  refine ⟨signedCode w (qplus w A C) (qplus w B D),
    signedCode_in_field w hw _ _ (qplus_in_field w hw hInf A C hA hC)
      (qplus_in_field w hw hInf B D hB hD), ?_⟩
  exact ⟨hw.1, A, B, C, D, hA, hB, hC, hD, hRa, hSc, rfl⟩

include hw hInf in
theorem rationalAdd_unique (R S U V : ρ) (hU : RationalAdd w R S U)
    (hV : RationalAdd w R S V) : U = V := by
  obtain ⟨A, B, C, D, hA, hB, hC, hD, hRa, hSc, hUe⟩ := hU.2
  obtain ⟨E, F, G, H, hE, hF, hG, hH, hRe, hSg, hVe⟩ := hV.2
  have h₁ := (signedCode_identity_iff w hw hInf A B E F hA hB hE hF).1 (hRa.symm.trans hRe)
  have h₂ := (signedCode_identity_iff w hw hInf C D G H hC hD hG hH).1 (hSc.symm.trans hSg)
  have he := (signedCode_identity_iff w hw hInf _ _ _ _
    (qplus_in_field w hw hInf A C hA hC) (qplus_in_field w hw hInf B D hB hD)
    (qplus_in_field w hw hInf E G hE hG) (qplus_in_field w hw hInf F H hF hH)).2
    (difference_add w hw hInf A B C D E F G H hA hB hC hD hE hF hG hH h₁ h₂)
  exact hUe.trans (he.trans hVe.symm)

theorem rplus_supported (R S : ρ) : Supported w (rplus w R S) :=
  le_of_box_incl (nec% (fun (A B : φ) (h : rplus w R S A B) => h.1))

theorem rneg_supported (R : ρ) : Supported w (rneg w R) :=
  le_of_box_incl (nec% (fun (A B : φ) (h : rneg w R A B) => h.1))

include hw hInf in
theorem rplus_selected (R S U : ρ) (hU : RationalField w U) (hG : RationalAdd w R S U) :
    rplus w R S = U := by
  apply localized_eq w hw _ _ (rplus_supported w R S) (rational_code_supported w U hU)
  intro A B
  constructor
  · intro h
    obtain ⟨V, hV, hv⟩ := h.2
    exact (rationalAdd_unique w hw hInf R S V U hV hG) ▸ hv
  · intro hu
    exact ⟨hw.1, U, hG, hu⟩

include hw hInf in
theorem rplus_in_field (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    RationalField w (rplus w R S) := by
  obtain ⟨U, hU, hG⟩ := rationalAdd_total w hw hInf R S hR hS
  exact (rplus_selected w hw hInf R S U hU hG).symm ▸ hU

include hw hInf in
theorem rplus_codes (A B C D : φ) (hA : FractionField w A) (hB : FractionField w B)
    (hC : FractionField w C) (hD : FractionField w D) :
    rplus w (signedCode w A B) (signedCode w C D) =
      signedCode w (qplus w A C) (qplus w B D) :=
  rplus_selected w hw hInf _ _ _
    (signedCode_in_field w hw _ _ (qplus_in_field w hw hInf A C hA hC)
      (qplus_in_field w hw hInf B D hB hD))
    ⟨hw.1, A, B, C, D, hA, hB, hC, hD, rfl, rfl, rfl⟩

include hw hInf in
theorem rneg_codes (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    rneg w (signedCode w X Y) = signedCode w Y X := by
  apply localized_eq w hw _ _ (rneg_supported w _) (signedCode_supported w Y X)
  intro A B
  constructor
  · intro h
    exact ⟨h.1, h.2.2.2.1, h.2.2.1,
      difference_neg w hw hInf X Y B A hX hY h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩
  · intro h
    exact ⟨h.1, h.1, h.2.2.1, h.2.1,
      difference_neg w hw hInf Y X A B hY hX h.2.1 h.2.2.1 h.2.2.2⟩

include hw hInf in
theorem rneg_in_field (R : ρ) (hR : RationalField w R) : RationalField w (rneg w R) := by
  obtain ⟨X, Y, hX, hY, he⟩ := hR.2
  rw [he, rneg_codes w hw hInf X Y hX hY]
  exact signedCode_in_field w hw Y X hY hX

include hw hInf in
theorem rneg_involution (R : ρ) (hR : RationalField w R) : rneg w (rneg w R) = R := by
  obtain ⟨X, Y, hX, hY, he⟩ := hR.2
  rw [he, rneg_codes w hw hInf X Y hX hY, rneg_codes w hw hInf Y X hY hX]

include hw hInf in
theorem rplus_comm (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    rplus w R S = rplus w S R := by
  obtain ⟨A, B, hA, hB, hRa⟩ := hR.2
  obtain ⟨C, D, hC, hD, hSc⟩ := hS.2
  rw [hRa, hSc, rplus_codes w hw hInf A B C D hA hB hC hD,
    rplus_codes w hw hInf C D A B hC hD hA hB,
    qplus_comm w hw hInf A C hA hC, qplus_comm w hw hInf B D hB hD]

include hw hInf in
theorem rplus_assoc (R S U : ρ) (hR : RationalField w R)
    (hS : RationalField w S) (hU : RationalField w U) :
    rplus w (rplus w R S) U = rplus w R (rplus w S U) := by
  obtain ⟨A, B, hA, hB, hRa⟩ := hR.2
  obtain ⟨C, D, hC, hD, hSc⟩ := hS.2
  obtain ⟨E, F, hE, hF, hUe⟩ := hU.2
  rw [hRa, hSc, hUe, rplus_codes w hw hInf A B C D hA hB hC hD,
    rplus_codes w hw hInf C D E F hC hD hE hF,
    rplus_codes w hw hInf _ _ E F (qplus_in_field w hw hInf A C hA hC)
      (qplus_in_field w hw hInf B D hB hD) hE hF,
    rplus_codes w hw hInf A B _ _ hA hB
      (qplus_in_field w hw hInf C E hC hE) (qplus_in_field w hw hInf D F hD hF),
    qplus_assoc w hw hInf A C E hA hC hE, qplus_assoc w hw hInf B D F hB hD hF]

include hw hInf in
theorem rplus_zero_right (R : ρ) (hR : RationalField w R) : rplus w R (rzero w) = R := by
  obtain ⟨A, B, hA, hB, he⟩ := hR.2
  rw [he]
  change rplus w (signedCode w A B) (signedCode w (qzero w) (qzero w)) = signedCode w A B
  rw [rplus_codes w hw hInf A B _ _ hA hB (qzero_in_field w hw hInf) (qzero_in_field w hw hInf),
    qplus_zero_right w hw hInf A hA, qplus_zero_right w hw hInf B hB]

include hw hInf in
theorem rplus_zero_left (R : ρ) (hR : RationalField w R) : rplus w (rzero w) R = R := by
  rw [rplus_comm w hw hInf _ R (rzero_in_field w hw hInf) hR, rplus_zero_right w hw hInf R hR]

include hw hInf in
theorem rplus_neg (R : ρ) (hR : RationalField w R) : rplus w R (rneg w R) = rzero w := by
  obtain ⟨A, B, hA, hB, he⟩ := hR.2
  rw [he, rneg_codes w hw hInf A B hA hB, rplus_codes w hw hInf A B B A hA hB hB hA]
  exact (signedCode_zero_iff w hw hInf _ _
    (qplus_in_field w hw hInf A B hA hB) (qplus_in_field w hw hInf B A hB hA)).2
    (qplus_comm w hw hInf A B hA hB)

include hw hInf in
theorem rneg_add (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    rneg w (rplus w R S) = rplus w (rneg w R) (rneg w S) := by
  obtain ⟨A, B, hA, hB, hRa⟩ := hR.2
  obtain ⟨C, D, hC, hD, hSc⟩ := hS.2
  rw [hRa, hSc, rplus_codes w hw hInf A B C D hA hB hC hD,
    rneg_codes w hw hInf _ _ (qplus_in_field w hw hInf A C hA hC)
      (qplus_in_field w hw hInf B D hB hD),
    rneg_codes w hw hInf A B hA hB, rneg_codes w hw hInf C D hC hD,
    rplus_codes w hw hInf B A D C hB hA hD hC]

include hw hInf in
theorem rplus_cancel_right (R S U : ρ) (hR : RationalField w R)
    (hS : RationalField w S) (hU : RationalField w U)
    (he : rplus w R U = rplus w S U) : R = S := by
  have he' := congrArg (fun V => rplus w V (rneg w U)) he
  rw [rplus_assoc w hw hInf R U _ hR hU (rneg_in_field w hw hInf U hU),
    rplus_assoc w hw hInf S U _ hS hU (rneg_in_field w hw hInf U hU),
    rplus_neg w hw hInf U hU, rplus_zero_right w hw hInf R hR,
    rplus_zero_right w hw hInf S hS] at he'
  exact he'

include hw hInf in
theorem embed_add (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    rplus w (embed w X) (embed w Y) = embed w (qplus w X Y) := by
  change rplus w (signedCode w X (qzero w)) (signedCode w Y (qzero w)) =
    signedCode w (qplus w X Y) (qzero w)
  rw [rplus_codes w hw hInf X _ Y _ hX (qzero_in_field w hw hInf) hY (qzero_in_field w hw hInf),
    qplus_zero_right w hw hInf _ (qzero_in_field w hw hInf)]

end Classicism.Research.ProbabilityRationals
