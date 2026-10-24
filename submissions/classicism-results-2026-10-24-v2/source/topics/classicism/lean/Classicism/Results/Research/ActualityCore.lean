import Classicism.Results.Research.Evaluator
import Classicism.Results.Research.AtomCoordinates

/-!
# The current supported core of an actual world

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
§§1–3, 7–8 (original research, `misc`, 22 October 2026, unpaginated).

All conclusions are current. `ActualWorld w` is not boxed and `w` may vanish.
The all-relational localization and section lemmas cover arbitrary trailing
argument types through the existing `Rel`/`Pointwise` interpretation. Explicit
represented joins and atom coordinates below are unary; their tuple certificates
are requested separately. No external subsets or individual-output operations
are introduced. This file does not claim a completed syntax interpretation.
-/

namespace Classicism.Research.ActualityCore
open Classicism.Paper Classicism.P

section relational
variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

def Supported (w : Prop) (X : τ) : Prop := X ≤ constP w
def Cut (A X : τ) : τ := Rel.and A X
def Domain (w : Prop) (A : τ) : τ → Prop := fun X => w ∧ X ≤ A

theorem cut_le (A X : τ) : Cut A X ≤ A :=
  le_of_box_incl (nec% (incl_and_left A X))

theorem cut_le_right (A X : τ) : Cut A X ≤ X :=
  le_of_box_incl (nec% (incl_and_right A X))

theorem le_cut (A X Y : τ) (hA : Y ≤ A) (hX : Y ≤ X) : Y ≤ Cut A X :=
  le_of_box_incl (modal_K _ _ (modal_K _ _
    (nec% (incl_and A X Y)) ((le_iff _ _).1 hA)) ((le_iff _ _).1 hX))

theorem cut_fixed (A X : τ) (hX : X ≤ A) : Cut A X = X :=
  le_antisymm_rel _ _ (cut_le_right A X) (le_cut A X X hX (le_refl_rel X))

theorem cut_idempotent (A X : τ) : Cut A (Cut A X) = Cut A X :=
  cut_fixed A (Cut A X) (cut_le A X)

theorem cut_supported (w : Prop) (A X : τ) (hA : Supported w A) :
    Supported w (Cut A X) := le_trans_rel _ _ _ (cut_le A X) hA

/-- A closed pointwise argument, valid at every relational type. -/
theorem local_order_step (w : Prop) (X Y : τ) :
    (X ⊆ constP w) → (w → X ⊆ Y) → X ⊆ Y := fun hs hi =>
  (em w).elim hi (fun hn => incl_trans X (constP w) Y hs (incl_of_constP Y w hn))

/-- Only the source relation needs support. Actuality absorbs the entire current
universally quantified inclusion before any modal reasoning is performed. -/
theorem localized_le (w : Prop) (hw : ActualWorld w) (X Y : τ)
    (hX : Supported w X) (hXY : X ⊆ Y) : X ≤ Y :=
  le_of_box_incl (modal_K _ _ (modal_K _ _
    (nec% (local_order_step w X Y)) ((le_iff _ _).1 hX))
    ((le_iff_prop _ _).1 (hw.2 (X ⊆ Y) hXY)))

theorem localized_le_iff (w : Prop) (hw : ActualWorld w) (X Y : τ)
    (hX : Supported w X) : X ≤ Y ↔ X ⊆ Y :=
  ⟨incl_of_le, localized_le w hw X Y hX⟩

theorem localized_eq (w : Prop) (hw : ActualWorld w) (X Y : τ)
    (hX : Supported w X) (hY : Supported w Y) (hXY : X ≡ Y) : X = Y :=
  le_antisymm_rel X Y
    (localized_le w hw X Y hX (incl_of_coext X Y hXY))
    (localized_le w hw Y X hY (incl_of_coext' X Y hXY))

theorem domain_supported (w : Prop) (A : τ) : Supported w (Domain w A) :=
  le_of_box_incl (nec% (fun (X : τ) (h : Domain w A X) => h.1))

theorem cut_in_domain (w : Prop) (hw : ActualWorld w) (A X : τ) :
    Domain w A (Cut A X) := ⟨hw.1, cut_le A X⟩

theorem domain_contains_bottom (w : Prop) (hw : ActualWorld w) (A : τ) :
    Domain w A (Rel.bot τ) := ⟨hw.1, bot_le_rel A⟩

theorem domain_contains_top (w : Prop) (hw : ActualWorld w) (A : τ) :
    Domain w A A := ⟨hw.1, le_refl_rel A⟩

theorem domain_cut_fixed (w : Prop) (A X : τ) (hX : Domain w A X) :
    Cut A X = X := cut_fixed A X hX.2

/-- Rectangular support for one additional input and an arbitrary relational tail. -/
def ProductSupport {σ : Type} [Ty σ] (D : σ → Prop) (A : τ) : σ → τ :=
  fun x => Cut (constP (D x)) A

theorem section_below {σ : Type} [Ty σ] (D : σ → Prop) (A : τ)
    (F : σ → τ) (hF : F ≤ ProductSupport D A) (a : σ) : F a ≤ A :=
  le_trans_rel _ _ _ (show F a ≤ ProductSupport D A a from congrFun hF a)
    (cut_le_right (constP (D a)) A)

theorem section_in_domain {σ : Type} [Ty σ] (w : Prop) (D : σ → Prop)
    (A : τ) (F : σ → τ) (hF : Domain w (ProductSupport D A) F) (a : σ) :
    Domain w A (F a) := ⟨hF.1, section_below D A F hF.2 a⟩

/-- At a current domain input, supported lambda abstraction has the required
literal section. No hypothesis-dependent `funext` is used. -/
theorem supported_beta {σ : Type} [Ty σ] (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (A : τ) (hA : Supported w A) (T : σ → τ)
    (a : σ) (ha : D a) (hTa : T a ≤ A) :
    Cut (ProductSupport D A) T a = T a := by
  apply localized_eq w hw
  · exact le_trans_rel _ _ _
      (le_trans_rel _ _ _ (cut_le (ProductSupport D A a) (T a))
        (cut_le_right (constP (D a)) A)) hA
  · exact le_trans_rel _ _ _ hTa hA
  · exact coext_of_incl _ _ (incl_and_right _ _) (incl_and _ _ _
      (incl_and _ _ _ (incl_constP (T a) (D a) ha) (incl_of_le hTa))
      (incl_refl (T a)))

end relational

/-! ## Truth objects and supported logical operations -/

def Truth (w p : Prop) : Prop := w ∧ p

theorem truth_supported (w p : Prop) : Supported w (Truth w p) := and_le_left_prop w p

theorem truth_current (w : Prop) (hw : ActualWorld w) (p : Prop) :
    Truth w p ↔ p := ⟨And.right, fun hp => ⟨hw.1, hp⟩⟩

theorem truth_eq_iff (w : Prop) (hw : ActualWorld w) (p q : Prop) :
    Truth w p = Truth w q ↔ (p ↔ q) := by
  constructor
  · intro h
    exact ⟨fun hp => (Eq.mp h ⟨hw.1, hp⟩).2,
      fun hq => (Eq.mpr h ⟨hw.1, hq⟩).2⟩
  · intro h
    exact localized_eq w hw _ _ (truth_supported w p) (truth_supported w q)
      ⟨fun hp => ⟨hp.1, h.1 hp.2⟩, fun hq => ⟨hq.1, h.2 hq.2⟩⟩

theorem truth_false (w : Prop) : Truth w False = False := and_false_eq w
theorem truth_true (w : Prop) : Truth w True = w := and_true_eq w

theorem truth_values (w : Prop) (hw : ActualWorld w) (p : Prop) :
    Truth w p = w ∨ Truth w p = False :=
  (em p).elim
    (fun hp => Or.inl (((truth_eq_iff w hw p True).2
      ⟨fun _ => trivial, fun _ => hp⟩).trans (truth_true w)))
    (fun hn => Or.inr (((truth_eq_iff w hw p False).2
      ⟨hn, False.elim⟩).trans (truth_false w)))

theorem truth_meet (w p q : Prop) : Truth w (p ∧ q) = (Truth w p ∧ Truth w q) :=
  propext ⟨fun h => ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.2⟩⟩,
    fun h => ⟨h.1.1, h.1.2, h.2.2⟩⟩

theorem truth_join (w p q : Prop) : Truth w (p ∨ q) = (Truth w p ∨ Truth w q) :=
  propext ⟨fun h => h.2.elim (fun hp => Or.inl ⟨h.1, hp⟩)
    (fun hq => Or.inr ⟨h.1, hq⟩),
    fun h => h.elim (fun hp => ⟨hp.1, Or.inl hp.2⟩)
      (fun hq => ⟨hq.1, Or.inr hq.2⟩)⟩

theorem truth_neg (w p : Prop) : Truth w (¬ p) = (w ∧ ¬ Truth w p) :=
  propext ⟨fun h => ⟨h.1, fun hp => h.2 hp.2⟩,
    fun h => ⟨h.1, fun hp => h.2 ⟨h.1, hp⟩⟩⟩

def Equality {σ : Type} [Ty σ] (w : Prop) (D : σ → Prop) : σ → σ → Prop :=
  fun x y => w ∧ D x ∧ D y ∧ x = y

theorem equality_current {σ : Type} [Ty σ] (w : Prop) (hw : ActualWorld w)
    (D : σ → Prop) (x y : σ) (hx : D x) (hy : D y) :
    Equality w D x y ↔ x = y :=
  ⟨fun h => h.2.2.2, fun h => ⟨hw.1, hx, hy, h⟩⟩

def Universal {σ : Type} [Ty σ] (w : Prop) (D A : σ → Prop) :
    (σ → Prop) → Prop := fun P => w ∧ Domain w A P ∧ ∀ x, D x → P x

theorem universal_supported {σ : Type} [Ty σ] (w : Prop) (D A : σ → Prop) :
    Universal w D A ≤ Domain w A :=
  le_of_box_incl (nec% (fun (P : σ → Prop) (h : Universal w D A P) => h.2.1))

theorem universal_current {σ : Type} [Ty σ] (w : Prop) (hw : ActualWorld w)
    (D A P : σ → Prop) (hP : Domain w A P) :
    Universal w D A P ↔ ∀ x, D x → P x :=
  ⟨fun h => h.2.2, fun h => ⟨hw.1, hP, h⟩⟩

/-! ## Represented families in a unary supported interval -/

section unary
variable {σ : Type} [Ty σ]

def IntervalJoin (A : σ → Prop) (P : (σ → Prop) → Prop) : σ → Prop :=
  fun x => A x ∧ ∃ F : σ → Prop, P F ∧ F ≤ A ∧ F x

theorem intervalJoin_below (A : σ → Prop) (P : (σ → Prop) → Prop) :
    IntervalJoin A P ≤ A :=
  le_of_box_incl (nec% (fun (x : σ) (h : IntervalJoin A P x) => h.1))

theorem member_le_intervalJoin (w : Prop) (hw : ActualWorld w)
    (A : σ → Prop) (hA : Supported w A) (P : (σ → Prop) → Prop)
    (F : σ → Prop) (hPF : P F) (hFA : F ≤ A) : F ≤ IntervalJoin A P :=
  localized_le w hw F _ (le_trans_rel _ _ _ hFA hA)
    (fun x hx => ⟨incl_of_le hFA x hx, F, hPF, hFA, hx⟩)

/-- The join is an ambient LUB of the represented, support-restricted family.
An arbitrary ambient upper bound is permitted; it need not be supported. -/
theorem intervalJoin_lub (w : Prop) (hw : ActualWorld w)
    (A : σ → Prop) (hA : Supported w A) (P : (σ → Prop) → Prop) :
    LUB (IntervalJoin A P) (fun F => P F ∧ F ≤ A) := by
  intro Y
  constructor
  · intro hY
    exact localized_le w hw _ Y
      (le_trans_rel _ _ _ (intervalJoin_below A P) hA)
      (fun x hx => hx.2.elim fun F hF => incl_of_le (hY F ⟨hF.1, hF.2.1⟩) x hF.2.2)
  · intro hJ F hF
    exact le_trans_rel _ _ _ (member_le_intervalJoin w hw A hA P F hF.1 hF.2) hJ

theorem cut_kernel (w : Prop) (hw : ActualWorld w) (A X Y : σ → Prop)
    (hA : Supported w A) : Cut A X = Cut A Y ↔ ∀ x, A x → (X x ↔ Y x) := by
  constructor
  · intro h x ha
    exact ⟨fun hx => (Eq.mp (congrFun h x) ⟨ha, hx⟩).2,
      fun hy => (Eq.mpr (congrFun h x) ⟨ha, hy⟩).2⟩
  · intro h
    exact localized_eq w hw _ _ (cut_supported w A X hA) (cut_supported w A Y hA)
      (fun x => ⟨fun hx => ⟨hx.1, (h x hx.1).1 hx.2⟩,
        fun hy => ⟨hy.1, (h x hy.1).2 hy.2⟩⟩)

theorem supported_nonzero_has_value (w : Prop) (hw : ActualWorld w)
    (F : σ → Prop) (hF : Supported w F) (hn : F ≠ Rel.bot (σ → Prop)) :
    ∃ x, F x :=
  (em (∃ x, F x)).elim (fun h => h) (fun h => (hn
    (localized_eq w hw F _ hF (bot_le_rel _)
      (fun x => ⟨fun hx => h ⟨x, hx⟩, False.elim⟩))).elim)

theorem actualWorld_atom (w : Prop) (hw : ActualWorld w) : Atom w :=
  atom_of_decides w ⟨dia_intro w hw.1, fun p =>
    (em p).elim (fun hp => Or.inl (hw.2 p hp)) (fun hn => Or.inr (hw.2 (¬ p) hn))⟩

theorem pin_supported (w : Prop) (a : σ) : Supported w (AtomCoordinates.Pin w a) :=
  le_of_box_incl (nec% (fun (x : σ) (h : AtomCoordinates.Pin w a x) => h.1))

theorem pin_le_of_value (w : Prop) (hw : ActualWorld w) (F : σ → Prop)
    (a : σ) (ha : F a) : AtomCoordinates.Pin w a ≤ F :=
  localized_le w hw _ F (pin_supported w a)
    (fun x hx => hx.2.symm ▸ ha)

/-- This reuses the checked pin theorem; it does not repeat atom classification. -/
theorem supported_atom_coordinates (w : Prop) (hw : ActualWorld w)
    (F : σ → Prop) (hF : Supported w F) (ha : Atom F) :
    ∃ a : σ, F = AtomCoordinates.Pin w a := by
  obtain ⟨a, hFa⟩ := supported_nonzero_has_value w hw F hF (AtomCoordinates.atom_ne_bot F ha)
  exact ⟨a, (AtomCoordinates.atom_eq_of_nonzero_below F _ ha
    (fun hz => (AtomCoordinates.pin_eq_bot_iff w a).1 hz ▸ hw.1)
    (pin_le_of_value w hw F a hFa)).symm⟩

theorem supported_atom_below (w : Prop) (hw : ActualWorld w)
    (F : σ → Prop) (hF : Supported w F) (hn : F ≠ Rel.bot (σ → Prop)) :
    ∃ a : σ, Atom (AtomCoordinates.Pin w a) ∧ AtomCoordinates.Pin w a ≤ F :=
  (supported_nonzero_has_value w hw F hF hn).elim fun a ha =>
    ⟨a, AtomCoordinates.pin_atom w a (actualWorld_atom w hw), pin_le_of_value w hw F a ha⟩

theorem current_pin_injective (w : Prop) (hw : ActualWorld w) (a b : σ)
    (h : AtomCoordinates.Pin w a = AtomCoordinates.Pin w b) : a = b :=
  (Eq.mp (congrFun h a) ⟨hw.1, rfl⟩).2

end unary

/-! Closed wrappers for genuine object-language and tuple-schema certificates. -/

def Localization (τ : Type) [Rel τ] : Prop :=
  ∀ (w : Prop) (X Y : τ), ActualWorld w → Supported w X → Supported w Y →
    X ≡ Y → X = Y

theorem localization_law {τ : Type} [Rel τ] [Order τ] [Pointwise τ] :
    Localization τ := fun w X Y hw hX hY h => localized_eq w hw X Y hX hY h

def IntervalCompleteness (σ : Type) [Ty σ] : Prop :=
  ∀ (w : Prop) (A : σ → Prop), ActualWorld w → Supported w A →
    ∀ P : (σ → Prop) → Prop, ∃ J : σ → Prop,
      J ≤ A ∧ LUB J (fun F => P F ∧ F ≤ A)

theorem interval_completeness_law {σ : Type} [Ty σ] : IntervalCompleteness σ :=
  fun w A hw hA P => ⟨IntervalJoin A P, intervalJoin_below A P,
    intervalJoin_lub w hw A hA P⟩

def LocalAtomCoverage (σ : Type) [Ty σ] : Prop :=
  ∀ (w : Prop) (F : σ → Prop), ActualWorld w → Supported w F →
    F ≠ Rel.bot (σ → Prop) →
      ∃ a : σ, Atom (AtomCoordinates.Pin w a) ∧ AtomCoordinates.Pin w a ≤ F

theorem local_atom_coverage_law {σ : Type} [Ty σ] : LocalAtomCoverage σ :=
  fun w F hw hF hn => supported_atom_below w hw F hF hn

end Classicism.Research.ActualityCore
