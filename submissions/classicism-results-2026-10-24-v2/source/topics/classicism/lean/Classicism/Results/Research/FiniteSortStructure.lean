import Classicism.Principles.Lattice
import Classicism.Principles.Choice

/-!
# Finitary steps for finite-sort certificates

Source: research/2026-10-22/notes/positive-effective.md §§23.1–23.3,
original research, misc, 22 October 2026 (unpaginated).

These are shallow C proofs. The separate certificate driver must check the
gate, relational types and translation. There is no Lean Fintype hypothesis,
choice operator, or internal induction on natural numbers. The finite-bound
generator composes these steps a fixed external number of times.
-/

namespace Classicism.Research.FiniteSortStructure
open Classicism.Paper Classicism.P

section Relational
variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

theorem le_top (x : τ) : x ≤ (⊤ : τ) :=
  (le_iff _ _).2 (nec% (incl_constP x True True.intro))

theorem meet_left (x y : τ) : (x ∧ y) ≤ x :=
  (le_iff _ _).2 (nec% (incl_and_left x y))

theorem meet_right (x y : τ) : (x ∧ y) ≤ y :=
  (le_iff _ _).2 (nec% (incl_and_right x y))

theorem le_meet (z x y : τ) (hx : z ≤ x) (hy : z ≤ y) : z ≤ (x ∧ y) :=
  (le_iff _ _).2 (modal_K _ _ (modal_K _ _ (nec% (incl_and x y z))
    ((le_iff _ _).1 hx)) ((le_iff _ _).1 hy))

/-- Minimal among the nonzero objects is exactly what the atom proof needs. -/
theorem atom_of_minimal (q : τ) (hne : ¬ q ≤ ¬ q)
    (hmin : ∀ z, ¬ z ≤ ¬ z → z ≤ q → q ≤ z) : Atom q := by
  intro z
  constructor
  · intro hz
    exact (em (z ≤ ¬ z)).elim id (fun hn =>
      (hz.2 (le_antisymm_rel z q hz.1 (hmin z hn hz.1))).elim)
  · intro hz
    refine ⟨?_, ?_⟩
    · have e := eq_bot_of_le_neg_rel z hz
      rw [e]
      exact bot_le_rel q
    · intro e
      exact hne (e ▸ hz)

/-- Add one named candidate to the finite minimality invariant. -/
theorem minimum_step (C : τ → Prop) (q a : τ)
    (hn : ¬ q ≤ ¬ q)
    (hm : ∀ z, C z → ¬ z ≤ ¬ z → z ≤ q → q ≤ z) :
    ∃ r : τ, (¬ r ≤ ¬ r) ∧ r ≤ q ∧
      ∀ z, (z = a ∨ C z) → ¬ z ≤ ¬ z → z ≤ r → r ≤ z := by
  rcases em ((¬ a ≤ ¬ a) ∧ a ≤ q) with ha | ha
  · refine ⟨a, ha.1, ha.2, ?_⟩
    intro z hz hzn hza
    rcases hz with e | hc
    · rw [e]
      exact le_refl_rel a
    · exact le_trans_rel a q z ha.2 (hm z hc hzn (le_trans_rel z a q hza ha.2))
  · refine ⟨q, hn, le_refl_rel q, ?_⟩
    intro z hz hzn hzq
    rcases hz with e | hc
    · exact (ha ⟨e ▸ hzn, e ▸ hzq⟩).elim
    · exact hm z hc hzn hzq

theorem glb_empty (X : τ → Prop) : GLB (⊤ : τ) (fun z => X z ∧ False) := by
  intro z
  exact ⟨fun _ => le_top z, fun _ w hw => hw.2.elim⟩

/-- One finite truth case, keeping the exact represented-property GLB. -/
theorem glb_step (X C : τ → Prop) (a y : τ)
    (hy : GLB y (fun z => X z ∧ C z)) :
    ∃ r : τ, GLB r (fun z => X z ∧ (z = a ∨ C z)) := by
  rcases em (X a) with ha | ha
  · refine ⟨y ∧ a, ?_⟩
    intro z
    constructor
    · intro hz
      exact le_meet z y a
        ((hy z).1 (fun w hw => hz w ⟨hw.1, Or.inr hw.2⟩))
        (hz a ⟨ha, Or.inl rfl⟩)
    · intro hz w hw
      rcases hw.2 with e | hc
      · rw [e]
        exact le_trans_rel z (y ∧ a) a hz (meet_right y a)
      · exact ((hy z).2 (le_trans_rel z (y ∧ a) y hz (meet_left y a))) w ⟨hw.1, hc⟩
  · refine ⟨y, ?_⟩
    intro z
    constructor
    · intro hz
      exact (hy z).1 (fun w hw => hz w ⟨hw.1, Or.inr hw.2⟩)
    · intro hz w hw
      rcases hw.2 with e | hc
      · exact (ha (e ▸ hw.1)).elim
      · exact (hy z).2 hz w ⟨hw.1, hc⟩

theorem glb_cover (X C : τ → Prop) (y : τ)
    (hc : ∀ z, C z) (hy : GLB y (fun z => X z ∧ C z)) : GLB y X := by
  intro z
  exact ⟨fun hz => (hy z).1 (fun w hw => hz w hw.1),
    fun hz w hw => (hy z).2 hz w ⟨hw, hc w⟩⟩

end Relational

/-- Adding one proposition to a finite list of actual truths. -/
theorem truth_step (C : Prop → Prop) (w a : Prop)
    (hw : w) (hc : ∀ p, C p → p → w ≤ p) :
    ∃ v : Prop, v ∧ ∀ p, (p = a ∨ C p) → p → v ≤ p := by
  rcases em a with ha | ha
  · refine ⟨w ∧ a, ⟨hw, ha⟩, ?_⟩
    intro p hp hpt
    rcases hp with e | hcp
    · rw [e]
      exact and_le_right_prop w a
    · exact le_trans_prop _ _ _ (and_le_left_prop w a) (hc p hcp hpt)
  · refine ⟨w, hw, ?_⟩
    intro p hp hpt
    rcases hp with e | hcp
    · exact (ha (e ▸ hpt)).elim
    · exact hc p hcp hpt

section Choice
variable {σ τ : Type} [Ty σ] [Ty τ]

def PartialChoice (C : σ → Prop) (U S : σ → τ → Prop) : Prop :=
  (∀ x, C x → ∃ y, S x y ∧ ∀ z, S x z → y = z) ∧
  ∀ x y, S x y → U x y

theorem partial_empty (U : σ → τ → Prop) :
    PartialChoice (fun _ => False) U (fun _ _ => False) :=
  ⟨fun _ h => h.elim, fun _ _ h => h.elim⟩

/-- Priority at the new input handles repeated entries in a finite cover.
The constructed object is a relation even when the output type is e. -/
theorem partial_step (C : σ → Prop) (U S : σ → τ → Prop)
    (a : σ) (hu : Serial U) (hs : PartialChoice C U S) :
    ∃ R : σ → τ → Prop, PartialChoice (fun x => x = a ∨ C x) U R := by
  obtain ⟨b, hab⟩ := hu a
  let R : σ → τ → Prop := fun x y => (x = a ∧ y = b) ∨ (x ≠ a ∧ S x y)
  refine ⟨R, ?_, ?_⟩
  · intro x hx
    rcases em (x = a) with hxa | hxa
    · refine ⟨b, Or.inl ⟨hxa, rfl⟩, ?_⟩
      intro z hz
      rcases hz with hz | hz
      · exact hz.2.symm
      · exact (hz.1 hxa).elim
    · have hcx : C x := hx.elim (fun e => (hxa e).elim) id
      obtain ⟨y, hy, hun⟩ := hs.1 x hcx
      refine ⟨y, Or.inr ⟨hxa, hy⟩, ?_⟩
      intro z hz
      rcases hz with hz | hz
      · exact (hxa hz.1).elim
      · exact hun z hz.2
  · intro x y hxy
    rcases hxy with hxy | hxy
    · rw [hxy.1, hxy.2]
      exact hab
    · exact hs.2 x y hxy.2

theorem partial_cover (C : σ → Prop) (U S : σ → τ → Prop)
    (hc : ∀ x, C x) (hs : PartialChoice C U S) :
    Functional S ∧ ∀ x y, S x y → U x y :=
  ⟨fun x => hs.1 x (hc x), hs.2⟩

end Choice
end Classicism.Research.FiniteSortStructure
