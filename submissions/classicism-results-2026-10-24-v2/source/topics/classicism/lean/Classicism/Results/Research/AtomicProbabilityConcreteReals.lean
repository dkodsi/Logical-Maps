import Classicism.Results.Research.AtomicProbabilityRationalOrder
import Classicism.Results.Research.AtomicProbabilitySupportedReals

/-!
# A nontrivial complete cut order over the constructed rational domain

The base domain and strict order are now the explicit supported signed
rational codes, not arbitrary parameters required to satisfy field axioms.
Principal cuts embed that domain injectively and preserve/reflect order.
Represented nonempty bounded families have literally unique suprema in the
supported cut domain. This is a complete linear order construction; real
addition, multiplication and their field laws remain separate obligations.
All results are current under ActualWorld and quantified Infinity.
Source: new internal-real bridge formalization, 23 October 2026.
-/

namespace Classicism.Research.ProbabilityConcreteReals
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ProbabilityRationals
open Classicism.Research.ProbabilityCuts
open Classicism.Research.ProbabilitySupportedReals

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)
local notation "ρ" => (φ → φ → Prop)

def principal (w : Prop) (R : ρ) : ρ → Prop :=
  fun S => w ∧ RationalField w S ∧ RLt w S R

def RealField (w : Prop) : (ρ → Prop) → Prop := Reals w (RationalField w) (RLt w)
def RealBounded (w : Prop) (F : (ρ → Prop) → Prop) : Prop :=
  BoundedFamily w (RationalField w) (RLt w) F
def realSup (w : Prop) (F : (ρ → Prop) → Prop) : ρ → Prop :=
  supremum w (RationalField w) F

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

theorem principal_below (R : ρ) : principal w R ≤ BaseSupport w (RationalField w) :=
  le_of_box_incl (nec% (fun (S : ρ) (h : principal w R S) => ⟨h.1, h.2.1⟩))

include hw hInf in
theorem principal_real (R : ρ) (hR : RationalField w R) :
    RealCode w (RationalField w) (RLt w) (principal w R) := by
  refine ⟨principal_below w R, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    exact hS.2.1
  · obtain ⟨S, hS, hSR⟩ := rational_no_lower_endpoint w hw hInf R hR
    exact ⟨S, hw.1, hS, hSR⟩
  · exact ⟨R, hR, fun h => rlt_irrefl w R h.2.2⟩
  · intro A B hA hB hAB hBR
    exact ⟨hw.1, hA, rlt_trans w hw hInf A B R hAB hBR.2.2⟩
  · intro A hA
    obtain ⟨B, hB, hAB, hBR⟩ := rational_order_dense w hw hInf A R hA.2.2
    exact ⟨B, ⟨hw.1, hB, hBR⟩, hAB⟩

include hw hInf in
theorem principal_in_field (R : ρ) (hR : RationalField w R) : RealField w (principal w R) :=
  ⟨hw.1, principal_real w hw hInf R hR⟩

include hw hInf in
theorem principal_order_iff (R S : ρ) (hR : RationalField w R) (hS : RationalField w S) :
    principal w R ≤ principal w S ↔ RLe w R S := by
  constructor
  · intro h
    rcases rle_total w hw hInf R S hR hS with hRS | hSR
    · exact hRS
    · rcases Classicism.em (R = S) with he | hne
      · exact he ▸ rle_refl w hw hInf R hR
      · have hlt : RLt w S R := ⟨hSR, fun he => hne he.symm⟩
        have hp : principal w R S := ⟨hw.1, hS, hlt⟩
        have hs := incl_of_le h S hp
        exact False.elim (rlt_irrefl w S hs.2.2)
  · intro h
    apply localized_le w hw _ _
      (realCode_supported w _ _ _ (principal_real w hw hInf R hR))
    intro A hA
    exact ⟨hw.1, hA.2.1, rlt_of_lt_of_le w hw hInf A R S hA.2.2 h⟩

include hw hInf in
theorem principal_injective (R S : ρ) (hR : RationalField w R) (hS : RationalField w S)
    (he : principal w R = principal w S) : R = S := by
  have hRS : principal w R ≤ principal w S := he ▸ le_refl_rel (principal w R)
  have hSR : principal w S ≤ principal w R := he.symm ▸ le_refl_rel (principal w S)
  exact rle_antisymm w hw hInf R S
    ((principal_order_iff w hw hInf R S hR hS).1 hRS)
    ((principal_order_iff w hw hInf S R hS hR).1 hSR)

include hw hInf in
theorem real_field_inhabited : ∃ P : ρ → Prop, RealField w P :=
  ⟨principal w (rzero w), principal_in_field w hw hInf _ (rzero_in_field w hw hInf)⟩

include hw hInf in
theorem real_field_nontrivial :
    ∃ P Q : ρ → Prop, RealField w P ∧ RealField w Q ∧ P ≠ Q := by
  refine ⟨principal w (rzero w), principal w (rone w),
    principal_in_field w hw hInf _ (rzero_in_field w hw hInf),
    principal_in_field w hw hInf _ (rone_in_field w hw hInf), ?_⟩
  intro he
  exact rone_ne_zero w hw hInf
    (principal_injective w hw hInf _ _ (rzero_in_field w hw hInf) (rone_in_field w hw hInf) he).symm

include hw hInf in
theorem real_order_total (P Q : ρ → Prop) (hP : RealField w P) (hQ : RealField w Q) :
    P ≤ Q ∨ Q ≤ P := by
  rcases Classicism.em (∃ R, P R ∧ ¬ Q R) with h | h
  · obtain ⟨R, hPR, hnQR⟩ := h
    refine Or.inr (localized_le w hw Q P (realCode_supported w _ _ Q hQ.2) ?_)
    intro S hQS
    have hR := hP.2.2.1 R hPR
    have hS := hQ.2.2.1 S hQS
    rcases rle_total w hw hInf S R hS hR with hSR | hRS
    · rcases Classicism.em (S = R) with he | hne
      · exact he.symm ▸ hPR
      · exact hP.2.2.2.2.2.1 S R hS hR ⟨hSR, hne⟩ hPR
    · rcases Classicism.em (R = S) with he | hne
      · exact False.elim (hnQR (he.symm ▸ hQS))
      · exact False.elim (hnQR (hQ.2.2.2.2.2.1 R S hR hS ⟨hRS, hne⟩ hQS))
  · refine Or.inl (localized_le w hw P Q (realCode_supported w _ _ P hP.2) ?_)
    intro R hPR
    rcases Classicism.em (Q R) with hQR | hnQR
    · exact hQR
    · exact False.elim (h ⟨R, hPR, hnQR⟩)

include hw in
theorem concrete_real_supremum (F : (ρ → Prop) → Prop) (hF : RealBounded w F) :
    RealField w (realSup w F) ∧ CutLub F (realSup w F) ∧
      ∀ U, RealField w U → CutLub F U → realSup w F = U :=
  ⟨⟨hw.1, supremum_is_real w hw (RationalField w) (RLt w) F hF⟩,
    supremum_is_lub w hw (RationalField w) (RLt w) F hF,
    fun U hU hl => real_lub_unique w hw (RationalField w) (RLt w) F _ U
      (supremum_is_real w hw (RationalField w) (RLt w) F hF) hU.2
      (supremum_is_lub w hw (RationalField w) (RLt w) F hF) hl⟩

end Classicism.Research.ProbabilityConcreteReals
