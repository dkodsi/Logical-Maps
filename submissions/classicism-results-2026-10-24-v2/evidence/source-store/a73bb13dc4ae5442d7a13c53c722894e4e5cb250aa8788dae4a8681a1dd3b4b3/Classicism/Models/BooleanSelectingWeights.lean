import Classicism.Models.BooleanValuedEquality
import Mathlib.Order.Heyting.Hom
import Mathlib.SetTheory.Cardinal.Order

/-!
# Well-ordered Boolean selecting weights

Original supporting formalization (misc), 23 October 2026, of section 6
of `research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
The disjoint weights select the earliest available ground output at each
Boolean degree. Their supremum is the row value, without a cardinal bound
or any small-table distributivity premise. The default weight is the
complement of that row value, never the complement of global seriality.

The actual weighted Boolean profile has the selected output value under
each weight and commutes with Boolean automorphisms. Support/coherence of
the full typed selector and its row equation are subsequent obligations;
this module does not assume or certify a typed Choice verdict.
-/

namespace Classicism.Meta.ChoiceBoolean.SelectingWeights

universe u v

variable {B : Type u} [CompleteBooleanAlgebra B]
variable {I : Type v} [LinearOrder I]

def earlier (r : I → B) (i : I) : B := ⨆ j : I, ⨆ (_ : j < i), r j

def weight (r : I → B) (i : I) : B := r i ⊓ (earlier r i)ᶜ

def rowValue (r : I → B) : B := ⨆ i, r i

def defaultWeight (r : I → B) : B := (rowValue r)ᶜ

theorem weight_le (r : I → B) (i : I) : weight r i ≤ r i := inf_le_left

theorem le_earlier (r : I → B) {i j : I} (hij : i < j) : r i ≤ earlier r j :=
  le_iSup_of_le i (le_iSup_of_le hij le_rfl)

theorem weight_inf_eq_bot_of_lt (r : I → B) {i j : I} (hij : i < j) :
    weight r i ⊓ weight r j = ⊥ := by
  apply bot_unique
  exact (inf_le_inf ((weight_le r i).trans (le_earlier r hij))
    (show weight r j ≤ (earlier r j)ᶜ from inf_le_right)).trans_eq
      (inf_compl_self (earlier r j))

theorem weight_inf_eq_bot (r : I → B) {i j : I} (hij : i ≠ j) :
    weight r i ⊓ weight r j = ⊥ := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact weight_inf_eq_bot_of_lt r h
  · rw [inf_comm]
    exact weight_inf_eq_bot_of_lt r h

/-- Well-founded induction suffices: every earlier row is already below
the supremum of the weights, and the remaining part is this row's weight. -/
theorem iSup_weight [WellFoundedLT I] (r : I → B) :
    (⨆ i, weight r i) = rowValue r := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact (weight_le r i).trans (le_iSup r i)
  · apply iSup_le
    intro i
    refine wellFounded_lt.induction
      (C := fun j : I => r j ≤ ⨆ k, weight r k) i ?_
    intro i ih
    have he : earlier r i ≤ ⨆ j, weight r j := by
      apply iSup_le
      intro j
      apply iSup_le
      intro hji
      exact ih j hji
    rw [← sup_inf_inf_compl (x := r i) (y := earlier r i)]
    exact sup_le (inf_le_right.trans he) (le_iSup (weight r) i)

theorem weight_default_inf (r : I → B) (i : I) :
    weight r i ⊓ defaultWeight r = ⊥ := by
  apply bot_unique
  exact (inf_le_inf ((weight_le r i).trans (le_iSup r i)) le_rfl).trans_eq
    (inf_compl_self (rowValue r))

theorem partition [WellFoundedLT I] (r : I → B) :
    defaultWeight r ⊔ (⨆ i, weight r i) = ⊤ := by
  rw [iSup_weight]
  exact compl_sup_eq_top

/-- The literal weighted output formula. The default can be any chosen
ground output value; it is used only outside the row value. -/
def mix (r : I → B) (d : B) (f : I → B) : B :=
  defaultWeight r ⊓ d ⊔ ⨆ i, weight r i ⊓ f i

theorem weight_inf_mix (r : I → B) (d : B) (f : I → B) (i : I) :
    weight r i ⊓ mix r d f = weight r i ⊓ f i := by
  apply le_antisymm
  · rw [mix, inf_sup_left, inf_iSup_eq]
    apply sup_le
    · rw [← inf_assoc, weight_default_inf, bot_inf_eq]
      exact bot_le
    · apply iSup_le
      intro j
      by_cases hij : i = j
      · subst j
        simp only [← inf_assoc, inf_idem, le_refl]
      · rw [← inf_assoc, weight_inf_eq_bot r hij, bot_inf_eq]
        exact bot_le
  · apply le_inf inf_le_left
    exact le_sup_of_le_right (le_iSup (fun j => weight r j ⊓ f j) i)

/-- The selected table is equal to its output at every positive weight,
as a Boolean equality, not just as a truth-at-top assertion. -/
theorem weight_le_mix_iff (r : I → B) (d : B) (f : I → B) (i : I) :
    weight r i ≤ iffValue (mix r d f) (f i) :=
  le_iffValue_iff_inf_eq.mpr (weight_inf_mix r d f i)

theorem default_inf_mix (r : I → B) (d : B) (f : I → B) :
    defaultWeight r ⊓ mix r d f = defaultWeight r ⊓ d := by
  apply le_antisymm
  · rw [mix, inf_sup_left, inf_iSup_eq]
    apply sup_le
    · simp only [← inf_assoc, inf_idem, le_refl]
    · apply iSup_le
      intro i
      have hi : defaultWeight r ⊓ weight r i = ⊥ := by
        rw [inf_comm]
        exact weight_default_inf r i
      rw [← inf_assoc, hi, bot_inf_eq]
      exact bot_le
  · apply le_inf inf_le_left
    exact le_sup_left

theorem default_le_mix_iff (r : I → B) (d : B) (f : I → B) :
    defaultWeight r ≤ iffValue (mix r d f) d :=
  le_iffValue_iff_inf_eq.mpr (default_inf_mix r d f)

/-- All ground indices are fixed; only the Boolean values are mapped. -/
theorem map_earlier (e : B ≃o B) (r : I → B) (i : I) :
    e (earlier r i) = earlier (fun j => e (r j)) i := by
  simp only [earlier, e.map_iSup]

theorem map_weight (e : B ≃o B) (r : I → B) (i : I) :
    e (weight r i) = weight (fun j => e (r j)) i := by
  simp only [weight, e.map_inf, map_compl, map_earlier]

theorem map_defaultWeight (e : B ≃o B) (r : I → B) :
    e (defaultWeight r) = defaultWeight (fun j => e (r j)) := by
  simp only [defaultWeight, rowValue, map_compl, e.map_iSup]

theorem map_mix (e : B ≃o B) (r : I → B) (d : B) (f : I → B) :
    e (mix r d f) = mix (fun i => e (r i)) (e d) (fun i => e (f i)) := by
  simp only [mix, e.map_sup, e.map_inf, e.map_iSup, map_weight, map_defaultWeight]

end Classicism.Meta.ChoiceBoolean.SelectingWeights
