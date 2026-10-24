import Classicism.Principles.Coarse

/-!
# Quantifier-observer separation characterizes Barcan

Direct source: `research/2026-10-23/operator-characterizations/operator-separation-new-results.txt`,
section 2, Theorem 2 (misc, original research, 23 October 2026, unpaginated).

All quantifiers and qualifications are local. Quantifier commutation in the
exact equivalence is a material biconditional. Literal meet and top preservation
are retained. A separate theorem records the weaker known bounds for literal
quantifier commutation; an optional Barcan assumption is never necessitated.
-/

namespace Classicism.Research.QuantifierObservers
open Classicism.P Classicism.Paper

def PreservesMeet (O : Prop → Prop) : Prop :=
  ∀ p q : Prop, O (p ∧ q) = (O p ∧ O q)

def CommutesForall (σ : Type) [Ty σ] (O : Prop → Prop) : Prop :=
  ∀ F : σ → Prop, O (∀ x, F x) ↔ ∀ x, O (F x)

def Qualified (σ : Type) [Ty σ] (O : Prop → Prop) : Prop :=
  O True = True ∧ PreservesMeet O ∧ CommutesForall σ O

def Separation (σ : Type) [Ty σ] : Prop :=
  ∀ p q : Prop, p = q ↔ ∀ O : Prop → Prop, Qualified σ O → (O p ↔ O q)

/-- Even truth of the top output, without a meet law, suffices for the forward argument. -/
def WeakQualified (σ : Type) [Ty σ] (O : Prop → Prop) : Prop :=
  O True ∧ CommutesForall σ O

def WeakSeparation (σ : Type) [Ty σ] : Prop :=
  ∀ p q : Prop, p = q ↔ ∀ O : Prop → Prop, WeakQualified σ O → (O p ↔ O q)

def Principal (a : Prop) : Prop → Prop := fun p => □ (a → p)

theorem principal_self (a : Prop) : Principal a a :=
  nec% (fun ha : a => ha)

theorem principal_top (a : Prop) : Principal a True = True :=
  propext ⟨fun _ => trivial, fun _ => nec% (fun _ : a => True.intro)⟩

theorem principal_meet (a : Prop) : PreservesMeet (Principal a) := by
  intro p q
  have h : (a → p ∧ q) = ((a → p) ∧ (a → q)) :=
    propext ⟨fun h => ⟨fun ha => (h ha).1, fun ha => (h ha).2⟩,
      fun h ha => ⟨h.1 ha, h.2 ha⟩⟩
  exact (congrArg (fun r : Prop => □ r) h).trans (box_and_eq _ _)

theorem principal_separates (p q : Prop)
    (h : ∀ a : Prop, Principal a p ↔ Principal a q) : p = q := by
  apply modalized_fregean p q
  rw [iff_eq_and_imp, box_and_eq]
  exact ⟨(h p).1 (principal_self p), (h q).2 (principal_self q)⟩

theorem principal_forall_forward {σ : Type} [Ty σ] (a : Prop) (F : σ → Prop) :
    Principal a (∀ x, F x) → ∀ x, Principal a (F x) := fun h x =>
  modal_K _ _ (nec% (fun (h : a → ∀ x, F x) (ha : a) => h ha x)) h

theorem principal_forall_backward {σ : Type} [Ty σ] (a : Prop) (F : σ → Prop) :
    Barcan σ → (∀ x, Principal a (F x)) → Principal a (∀ x, F x) := fun bf h =>
  modal_K _ _ (nec% (fun (h : ∀ x, a → F x) (ha : a) (x : σ) => h x ha))
    (bf (fun x => a → F x) h)

theorem principal_forall {σ : Type} [Ty σ] (a : Prop) (F : σ → Prop) :
    Barcan σ → (Principal a (∀ x, F x) ↔ ∀ x, Principal a (F x)) := fun bf =>
  ⟨principal_forall_forward a F, principal_forall_backward a F bf⟩

theorem principal_qualified {σ : Type} [Ty σ] (bf : Barcan σ) (a : Prop) :
    Qualified σ (Principal a) :=
  ⟨principal_top a, principal_meet a, fun F => principal_forall a F bf⟩

theorem barcan_separation {σ : Type} [Ty σ] : Barcan σ → Separation σ :=
  fun bf p q => ⟨fun he O _ => he ▸ Iff.rfl,
    fun h => principal_separates p q (fun a => h (Principal a) (principal_qualified bf a))⟩

theorem separation_barcan {σ : Type} [Ty σ] : Separation σ → Barcan σ := by
  intro sep F hF
  apply (sep (∀ x, F x) True).2
  intro O hO
  have ht : O True := Eq.mpr hO.1 trivial
  exact ⟨fun _ => ht, fun _ => (hO.2.2 F).2
    (fun x => Eq.mpr (congrArg O (hF x)) ht)⟩

/-- Exact local characterization at each admitted type, without ND or Atomicity. -/
theorem separation_iff_barcan {σ : Type} [Ty σ] : Separation σ ↔ Barcan σ :=
  ⟨separation_barcan, barcan_separation⟩

theorem barcan_weak_separation {σ : Type} [Ty σ] : Barcan σ → WeakSeparation σ :=
  fun bf p q => ⟨fun he O _ => he ▸ Iff.rfl, fun h => principal_separates p q
    (fun a => h (Principal a) ⟨Eq.mpr (principal_top a) trivial,
      fun F => principal_forall a F bf⟩)⟩

theorem weak_separation_barcan {σ : Type} [Ty σ] : WeakSeparation σ → Barcan σ := by
  intro sep F hF
  apply (sep (∀ x, F x) True).2
  intro O hO
  exact ⟨fun _ => hO.1, fun _ => (hO.2 F).2
    (fun x => Eq.mpr (congrArg O (hF x)) hO.1)⟩

theorem weak_separation_iff_barcan {σ : Type} [Ty σ] : WeakSeparation σ ↔ Barcan σ :=
  ⟨weak_separation_barcan, barcan_weak_separation⟩

def LiteralCommutesForall (σ : Type) [Ty σ] (O : Prop → Prop) : Prop :=
  ∀ F : σ → Prop, O (∀ x, F x) = (∀ x, O (F x))

def LiteralQualified (σ : Type) [Ty σ] (O : Prop → Prop) : Prop :=
  O True = True ∧ PreservesMeet O ∧ LiteralCommutesForall σ O

def LiteralSeparation (σ : Type) [Ty σ] : Prop :=
  ∀ p q : Prop, p = q ↔ ∀ O : Prop → Prop, LiteralQualified σ O → (O p ↔ O q)

theorem literal_separation_barcan {σ : Type} [Ty σ] :
    LiteralSeparation σ → Barcan σ := by
  intro sep F hF
  apply (sep (∀ x, F x) True).2
  intro O hO
  have ht : O True := Eq.mpr hO.1 trivial
  exact ⟨fun _ => ht, fun _ => Eq.mpr (hO.2.2 F)
    (fun x => Eq.mpr (congrArg O (hF x)) ht)⟩

theorem boxed_barcan_principal_literal {σ : Type} [Ty σ]
    (bf : □ (Barcan σ)) (a : Prop) : LiteralQualified σ (Principal a) :=
  ⟨principal_top a, principal_meet a, fun F => modalized_fregean _ _
    (modal_K _ _ (nec% (principal_forall a F)) bf)⟩

/-- The sufficient premise for the literal version is boxed Barcan; no converse is asserted. -/
theorem boxed_barcan_literal_separation {σ : Type} [Ty σ] :
    □ (Barcan σ) → LiteralSeparation σ := fun bf p q =>
  ⟨fun he O _ => he ▸ Iff.rfl, fun h => principal_separates p q
    (fun a => h (Principal a) (boxed_barcan_principal_literal bf a))⟩

end Classicism.Research.QuantifierObservers
