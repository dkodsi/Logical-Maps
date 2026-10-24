import Classicism.Results.Research.AtomicProbabilityFractionInverse

/-!
# Represented signed rational codes

A signed rational is the supported class predicate of a difference of the
constructed nonnegative fractions. The equivalence relation, literal code
identity and injective nonnegative embedding are proved here, using the
previously proved additive cancellation rather than assuming a quotient.
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

def DifferenceEq (w : Prop) (X Y Z T : φ) : Prop := qplus w X T = qplus w Z Y

def signedCode (w : Prop) (X Y : φ) : ρ :=
  fun A B => w ∧ FractionField w A ∧ FractionField w B ∧ DifferenceEq w X Y A B

def RationalField (w : Prop) : ρ → Prop :=
  fun R => w ∧ ∃ X Y, FractionField w X ∧ FractionField w Y ∧ R = signedCode w X Y

def embed (w : Prop) (X : φ) : ρ := signedCode w X (qzero w)
def rzero (w : Prop) : ρ := embed w (qzero w)
def rone (w : Prop) : ρ := embed w (qone w)

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

theorem difference_refl (X Y : φ) : DifferenceEq w X Y X Y := rfl

theorem difference_symm (X Y Z T : φ) (h : DifferenceEq w X Y Z T) :
    DifferenceEq w Z T X Y := h.symm

include hw hInf in
theorem difference_trans (X Y Z T A B : φ)
    (hX : FractionField w X) (hY : FractionField w Y)
    (hZ : FractionField w Z) (hT : FractionField w T)
    (hA : FractionField w A) (hB : FractionField w B)
    (h₁ : DifferenceEq w X Y Z T) (h₂ : DifferenceEq w Z T A B) :
    DifferenceEq w X Y A B := by
  apply qplus_cancel_right w hw hInf (qplus w X B) (qplus w A Y) T
    (qplus_in_field w hw hInf X B hX hB) (qplus_in_field w hw hInf A Y hA hY) hT
  calc
    qplus w (qplus w X B) T = qplus w (qplus w X T) B :=
      qplus_right_comm w hw hInf X B T hX hB hT
    _ = qplus w (qplus w Z Y) B := congrArg (fun Q => qplus w Q B) h₁
    _ = qplus w (qplus w Z B) Y := qplus_right_comm w hw hInf Z Y B hZ hY hB
    _ = qplus w (qplus w A T) Y := congrArg (fun Q => qplus w Q Y) h₂
    _ = qplus w (qplus w A Y) T := qplus_right_comm w hw hInf A T Y hA hT hY

theorem signedCode_supported (X Y : φ) : Supported w (signedCode w X Y) :=
  le_of_box_incl (nec% (fun (A B : φ) (h : signedCode w X Y A B) => h.1))

theorem rationalField_supported : Supported w (RationalField (σ := σ) w) :=
  le_of_box_incl (nec% (fun (R : ρ) (h : RationalField w R) => h.1))

include hw in
theorem signedCode_self (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    signedCode w X Y X Y := ⟨hw.1, hX, hY, rfl⟩

include hw hInf in
theorem signedCode_identity_iff (X Y Z T : φ)
    (hX : FractionField w X) (hY : FractionField w Y)
    (hZ : FractionField w Z) (hT : FractionField w T) :
    signedCode w X Y = signedCode w Z T ↔ DifferenceEq w X Y Z T := by
  constructor
  · intro he
    have h := Eq.mpr (congrFun (congrFun he Z) T) (signedCode_self w hw Z T hZ hT)
    exact h.2.2.2
  · intro he
    apply localized_eq w hw _ _ (signedCode_supported w X Y) (signedCode_supported w Z T)
    intro A B
    constructor
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1,
        difference_trans w hw hInf Z T X Y A B hZ hT hX hY h.2.1 h.2.2.1 he.symm h.2.2.2⟩
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1,
        difference_trans w hw hInf X Y Z T A B hX hY hZ hT h.2.1 h.2.2.1 he h.2.2.2⟩

include hw in
theorem signedCode_in_field (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    RationalField w (signedCode w X Y) := ⟨hw.1, X, Y, hX, hY, rfl⟩

theorem rational_code_supported (R : ρ) (hR : RationalField w R) : Supported w R := by
  obtain ⟨X, Y, hX, hY, he⟩ := hR.2
  exact he.symm ▸ signedCode_supported w X Y

include hw hInf in
theorem embed_in_field (X : φ) (hX : FractionField w X) : RationalField w (embed w X) :=
  signedCode_in_field w hw X _ hX (qzero_in_field w hw hInf)

include hw hInf in
theorem embed_injective (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y)
    (he : embed w X = embed w Y) : X = Y := by
  have he' := (signedCode_identity_iff w hw hInf X (qzero w) Y (qzero w)
    hX (qzero_in_field w hw hInf) hY (qzero_in_field w hw hInf)).1 he
  change qplus w X (qzero w) = qplus w Y (qzero w) at he'
  rw [qplus_zero_right w hw hInf X hX, qplus_zero_right w hw hInf Y hY] at he'
  exact he'

include hw hInf in
theorem rzero_in_field : RationalField (σ := σ) w (rzero w) :=
  embed_in_field w hw hInf _ (qzero_in_field w hw hInf)

include hw hInf in
theorem rone_in_field : RationalField (σ := σ) w (rone w) :=
  embed_in_field w hw hInf _ (qone_in_field w hw hInf)

include hw hInf in
theorem rone_ne_zero : rone (σ := σ) w ≠ rzero w := by
  intro he
  exact qone_ne_zero w hw hInf
    (embed_injective w hw hInf _ _ (qone_in_field w hw hInf) (qzero_in_field w hw hInf) he)

include hw hInf in
theorem signedCode_zero_iff (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    signedCode w X Y = rzero w ↔ X = Y := by
  constructor
  · intro he
    have he' := (signedCode_identity_iff w hw hInf X Y (qzero w) (qzero w)
      hX hY (qzero_in_field w hw hInf) (qzero_in_field w hw hInf)).1 he
    change qplus w X (qzero w) = qplus w (qzero w) Y at he'
    rw [qplus_zero_right w hw hInf X hX, qplus_zero_left w hw hInf Y hY] at he'
    exact he'
  · intro he
    apply (signedCode_identity_iff w hw hInf X Y (qzero w) (qzero w)
      hX hY (qzero_in_field w hw hInf) (qzero_in_field w hw hInf)).2
    change qplus w X (qzero w) = qplus w (qzero w) Y
    rw [qplus_zero_right w hw hInf X hX, qplus_zero_left w hw hInf Y hY, he]

include hw hInf in
theorem difference_add (A B C D E F G H : φ)
    (hA : FractionField w A) (hB : FractionField w B)
    (hC : FractionField w C) (hD : FractionField w D)
    (hE : FractionField w E) (hF : FractionField w F)
    (hG : FractionField w G) (hH : FractionField w H)
    (h₁ : DifferenceEq w A B E F) (h₂ : DifferenceEq w C D G H) :
    DifferenceEq w (qplus w A C) (qplus w B D) (qplus w E G) (qplus w F H) := by
  change qplus w (qplus w A C) (qplus w F H) = qplus w (qplus w E G) (qplus w B D)
  rw [qplus_four w hw hInf A C F H hA hC hF hH,
    qplus_four w hw hInf E G B D hE hG hB hD, h₁, h₂]

include hw hInf in
theorem difference_neg (A B C D : φ) (hA : FractionField w A)
    (hB : FractionField w B) (hC : FractionField w C) (hD : FractionField w D)
    (he : DifferenceEq w A B C D) : DifferenceEq w B A D C := by
  change qplus w B C = qplus w D A
  rw [qplus_comm w hw hInf B C hB hC, qplus_comm w hw hInf D A hD hA]
  exact he.symm

end Classicism.Research.ProbabilityRationals
