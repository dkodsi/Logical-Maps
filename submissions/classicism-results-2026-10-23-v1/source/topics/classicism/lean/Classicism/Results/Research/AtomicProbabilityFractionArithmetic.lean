import Classicism.Results.Research.AtomicProbabilityFractions

/-!
# Well-defined fraction arithmetic and concrete operation realization

Cross-multiplication calculations prove representative independence. The
addition/multiplication graphs are therefore total and literally single-valued
on the constructed fraction field. Supported pointwise unions realize them as
admitted binary operations. No Choice, assumed quotient, assumed field, or
external algebra is used. Context: current ActualWorld + quantified Infinity.
-/

namespace Classicism.Research.ProbabilityFractions
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore
open Classicism.Research.ActualityCoreNumbers
open Classicism.Research.ProbabilityNumericOperations

variable {σ : Type} [Ty σ]
local notation "ν" => ((σ → Prop) → Prop)
local notation "φ" => (ν → ν → Prop)

def sumNumerator (w : Prop) (a b c d : ν) : ν := plus w (times w a d) (times w c b)
def productDenominator (w : Prop) (b d : ν) : ν := times w b d

variable (w : Prop) (hw : ActualWorld w) (hInf : AxiomOfInfinity σ)

include hw hInf in
theorem sum_valid (a b c d : ν) (hab : Valid w a b) (hcd : Valid w c d) :
    Valid w (sumNumerator w a b c d) (productDenominator w b d) :=
  ⟨plus_numbers w hw hInf _ _ (times_numbers w hw hInf a d hab.1 hcd.2.1)
      (times_numbers w hw hInf c b hcd.1 hab.2.1),
    times_numbers w hw hInf b d hab.2.1 hcd.2.1,
    times_ne_zero w hw hInf b d hab.2.1 hcd.2.1 hab.2.2 hcd.2.2⟩

include hw hInf in
theorem product_valid (a b c d : ν) (hab : Valid w a b) (hcd : Valid w c d) :
    Valid w (times w a c) (productDenominator w b d) :=
  ⟨times_numbers w hw hInf a c hab.1 hcd.1,
    times_numbers w hw hInf b d hab.2.1 hcd.2.1,
    times_ne_zero w hw hInf b d hab.2.1 hcd.2.1 hab.2.2 hcd.2.2⟩

include hw hInf in
theorem product_respects (a b c d e f g h : ν)
    (hab : Valid w a b) (hcd : Valid w c d) (hef : Valid w e f) (hgh : Valid w g h)
    (h₁ : CrossEq w a b e f) (h₂ : CrossEq w c d g h) :
    CrossEq w (times w a c) (productDenominator w b d)
      (times w e g) (productDenominator w f h) := by
  change times w (times w a c) (times w f h) = times w (times w e g) (times w b d)
  rw [times_four w hw hInf a c f h hab.1 hcd.1 hef.2.1 hgh.2.1,
    times_four w hw hInf e g b d hef.1 hgh.1 hab.2.1 hcd.2.1, h₁, h₂]

include hw hInf in
theorem sum_respects (a b c d e f g h : ν)
    (hab : Valid w a b) (hcd : Valid w c d) (hef : Valid w e f) (hgh : Valid w g h)
    (h₁ : CrossEq w a b e f) (h₂ : CrossEq w c d g h) :
    CrossEq w (sumNumerator w a b c d) (productDenominator w b d)
      (sumNumerator w e f g h) (productDenominator w f h) := by
  change times w (plus w (times w a d) (times w c b)) (times w f h) =
    times w (plus w (times w e h) (times w g f)) (times w b d)
  rw [add_times w hw hInf _ _ _ (times_numbers w hw hInf a d hab.1 hcd.2.1)
      (times_numbers w hw hInf c b hcd.1 hab.2.1) (times_numbers w hw hInf f h hef.2.1 hgh.2.1),
    add_times w hw hInf _ _ _ (times_numbers w hw hInf e h hef.1 hgh.2.1)
      (times_numbers w hw hInf g f hgh.1 hef.2.1) (times_numbers w hw hInf b d hab.2.1 hcd.2.1),
    times_four w hw hInf a d f h hab.1 hcd.2.1 hef.2.1 hgh.2.1,
    times_four_cross w hw hInf c b f h hcd.1 hab.2.1 hef.2.1 hgh.2.1,
    times_four w hw hInf e h b d hef.1 hgh.2.1 hab.2.1 hcd.2.1,
    times_four_cross w hw hInf g f b d hgh.1 hef.2.1 hab.2.1 hcd.2.1,
    h₁, h₂, times_comm w hw hInf h d hgh.2.1 hcd.2.1,
    times_comm w hw hInf f b hef.2.1 hab.2.1]

def FractionAdd (w : Prop) (X Y Z : φ) : Prop :=
  w ∧ ∃ a b c d, Valid w a b ∧ Valid w c d ∧
    X = fractionCode w a b ∧ Y = fractionCode w c d ∧
    Z = fractionCode w (sumNumerator w a b c d) (productDenominator w b d)

def FractionMul (w : Prop) (X Y Z : φ) : Prop :=
  w ∧ ∃ a b c d, Valid w a b ∧ Valid w c d ∧
    X = fractionCode w a b ∧ Y = fractionCode w c d ∧
    Z = fractionCode w (times w a c) (productDenominator w b d)

include hw hInf in
theorem fractionAdd_total (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    ∃ Z, FractionField w Z ∧ FractionAdd w X Y Z := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  obtain ⟨c, d, hcd, hYc⟩ := hY.2
  refine ⟨fractionCode w (sumNumerator w a b c d) (productDenominator w b d),
    fractionCode_in_field w hw _ _ (sum_valid w hw hInf a b c d hab hcd), ?_⟩
  exact ⟨hw.1, a, b, c, d, hab, hcd, hXa, hYc, rfl⟩

include hw hInf in
theorem fractionMul_total (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    ∃ Z, FractionField w Z ∧ FractionMul w X Y Z := by
  obtain ⟨a, b, hab, hXa⟩ := hX.2
  obtain ⟨c, d, hcd, hYc⟩ := hY.2
  refine ⟨fractionCode w (times w a c) (productDenominator w b d),
    fractionCode_in_field w hw _ _ (product_valid w hw hInf a b c d hab hcd), ?_⟩
  exact ⟨hw.1, a, b, c, d, hab, hcd, hXa, hYc, rfl⟩

include hw hInf in
theorem fractionAdd_unique (X Y Z T : φ) (hZ : FractionAdd w X Y Z)
    (hT : FractionAdd w X Y T) : Z = T := by
  obtain ⟨a, b, c, d, hab, hcd, hXa, hYc, hZe⟩ := hZ.2
  obtain ⟨e, f, g, h, hef, hgh, hXe, hYg, hTe⟩ := hT.2
  have h₁ := (fractionCode_identity_iff w hw hInf a b e f hab hef).1 (hXa.symm.trans hXe)
  have h₂ := (fractionCode_identity_iff w hw hInf c d g h hcd hgh).1 (hYc.symm.trans hYg)
  have he := (fractionCode_identity_iff w hw hInf _ _ _ _
    (sum_valid w hw hInf a b c d hab hcd) (sum_valid w hw hInf e f g h hef hgh)).2
    (sum_respects w hw hInf a b c d e f g h hab hcd hef hgh h₁ h₂)
  exact hZe.trans (he.trans hTe.symm)

include hw hInf in
theorem fractionMul_unique (X Y Z T : φ) (hZ : FractionMul w X Y Z)
    (hT : FractionMul w X Y T) : Z = T := by
  obtain ⟨a, b, c, d, hab, hcd, hXa, hYc, hZe⟩ := hZ.2
  obtain ⟨e, f, g, h, hef, hgh, hXe, hYg, hTe⟩ := hT.2
  have h₁ := (fractionCode_identity_iff w hw hInf a b e f hab hef).1 (hXa.symm.trans hXe)
  have h₂ := (fractionCode_identity_iff w hw hInf c d g h hcd hgh).1 (hYc.symm.trans hYg)
  have he := (fractionCode_identity_iff w hw hInf _ _ _ _
    (product_valid w hw hInf a b c d hab hcd) (product_valid w hw hInf e f g h hef hgh)).2
    (product_respects w hw hInf a b c d e f g h hab hcd hef hgh h₁ h₂)
  exact hZe.trans (he.trans hTe.symm)

def qplus (w : Prop) (X Y : φ) : φ := fun a b => w ∧ ∃ Z, FractionAdd w X Y Z ∧ Z a b
def qtimes (w : Prop) (X Y : φ) : φ := fun a b => w ∧ ∃ Z, FractionMul w X Y Z ∧ Z a b

theorem qplus_supported (X Y : φ) : Supported w (qplus w X Y) :=
  le_of_box_incl (nec% (fun (a b : ν) (h : qplus w X Y a b) => h.1))

theorem qtimes_supported (X Y : φ) : Supported w (qtimes w X Y) :=
  le_of_box_incl (nec% (fun (a b : ν) (h : qtimes w X Y a b) => h.1))

include hw hInf in
theorem qplus_selected (X Y Z : φ) (hZ : FractionField w Z) (hG : FractionAdd w X Y Z) :
    qplus w X Y = Z := by
  apply localized_eq w hw _ _ (qplus_supported w X Y) (field_code_supported w Z hZ)
  intro a b
  constructor
  · intro h
    obtain ⟨T, hT, hval⟩ := h.2
    exact (fractionAdd_unique w hw hInf X Y T Z hT hG) ▸ hval
  · intro hz
    exact ⟨hw.1, Z, hG, hz⟩

include hw hInf in
theorem qtimes_selected (X Y Z : φ) (hZ : FractionField w Z) (hG : FractionMul w X Y Z) :
    qtimes w X Y = Z := by
  apply localized_eq w hw _ _ (qtimes_supported w X Y) (field_code_supported w Z hZ)
  intro a b
  constructor
  · intro h
    obtain ⟨T, hT, hval⟩ := h.2
    exact (fractionMul_unique w hw hInf X Y T Z hT hG) ▸ hval
  · intro hz
    exact ⟨hw.1, Z, hG, hz⟩

include hw hInf in
theorem qplus_in_field (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    FractionField w (qplus w X Y) := by
  obtain ⟨Z, hZ, hG⟩ := fractionAdd_total w hw hInf X Y hX hY
  exact (qplus_selected w hw hInf X Y Z hZ hG).symm ▸ hZ

include hw hInf in
theorem qtimes_in_field (X Y : φ) (hX : FractionField w X) (hY : FractionField w Y) :
    FractionField w (qtimes w X Y) := by
  obtain ⟨Z, hZ, hG⟩ := fractionMul_total w hw hInf X Y hX hY
  exact (qtimes_selected w hw hInf X Y Z hZ hG).symm ▸ hZ

include hw hInf in
theorem qplus_codes (a b c d : ν) (hab : Valid w a b) (hcd : Valid w c d) :
    qplus w (fractionCode w a b) (fractionCode w c d) =
      fractionCode w (sumNumerator w a b c d) (productDenominator w b d) :=
  qplus_selected w hw hInf _ _ _
    (fractionCode_in_field w hw _ _ (sum_valid w hw hInf a b c d hab hcd))
    ⟨hw.1, a, b, c, d, hab, hcd, rfl, rfl, rfl⟩

include hw hInf in
theorem qtimes_codes (a b c d : ν) (hab : Valid w a b) (hcd : Valid w c d) :
    qtimes w (fractionCode w a b) (fractionCode w c d) =
      fractionCode w (times w a c) (productDenominator w b d) :=
  qtimes_selected w hw hInf _ _ _
    (fractionCode_in_field w hw _ _ (product_valid w hw hInf a b c d hab hcd))
    ⟨hw.1, a, b, c, d, hab, hcd, rfl, rfl, rfl⟩

end Classicism.Research.ProbabilityFractions
