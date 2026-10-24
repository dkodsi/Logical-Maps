import Classicism.Models.BooleanColumnConditions
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Small compatible families of actual column conditions

Original formalization (misc), 23 October 2026. Source: section 2 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
For regular κ, the union of fewer than κ pairwise compatible conditions
is an actual condition extending every member. In particular the concrete
condition order has lower bounds for all descending chains of size less
than κ. This is the limit step of the small-table distributivity proof;
neither distributivity nor any model verdict is assumed here.
-/

namespace Classicism.Meta.ChoiceBoolean.ColumnConditions

universe u

noncomputable section

open scoped Classical

variable {κ : Cardinal.{u}} {I : Type u}

/-- Select the unique bit assigned by a compatible family, when it assigns
one. The definition exists for arbitrary families; compatibility supplies
its extension property. -/
def familyRaw (p : I → Condition κ) : Raw κ := fun a =>
  if h : ∃ b, ∃ i, p i a = some b then some (Classical.choose h) else none

theorem familyRaw_some (p : I → Condition κ)
    (hp : ∀ i j, Compatible (p i) (p j)) (i : I) (a : Point κ) (b : Bool)
    (hi : p i a = some b) : familyRaw p a = some b := by
  classical
  have h : ∃ c, ∃ j, p j a = some c := ⟨b, i, hi⟩
  unfold familyRaw
  rw [dif_pos h]
  obtain ⟨j, hj⟩ := Classical.choose_spec h
  exact congrArg some (hp j i a _ _ hj hi)

theorem familyRaw_domain (p : I → Condition κ) :
    domain (familyRaw p) = ⋃ i, domain (p i).toFun := by
  classical
  ext a
  simp only [domain, Set.mem_setOf_eq, Set.mem_iUnion]
  by_cases h : ∃ b, ∃ i, p i a = some b
  · constructor
    · intro _
      obtain ⟨b, i, hi⟩ := h
      exact ⟨i, b, hi⟩
    · intro _
      exact ⟨Classical.choose h, by simp only [familyRaw, dif_pos h]⟩
  · constructor
    · rintro ⟨b, hb⟩
      simp only [familyRaw, dif_neg h] at hb
      cases hb
    · rintro ⟨i, b, hi⟩
      exact False.elim (h ⟨b, i, hi⟩)

/-- The concrete small union. Regularity proves the domain bound. -/
def amalgam (hκ : κ.IsRegular) (hI : Cardinal.mk I < κ)
    (p : I → Condition κ) : Condition κ where
  toFun := familyRaw p
  small := by
    rw [familyRaw_domain]
    exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hκ hI).2
      (fun i => (p i).small)

theorem amalgam_le (hκ : κ.IsRegular) (hI : Cardinal.mk I < κ)
    (p : I → Condition κ) (hp : ∀ i j, Compatible (p i) (p j)) (i : I) :
    amalgam hκ hI p ≤ p i := by
  intro a b hi
  exact familyRaw_some p hp i a b hi

theorem compatible_of_comparable {p q : Condition κ}
    (h : p ≤ q ∨ q ≤ p) : Compatible p q := by
  rcases h with h | h
  · exact compatible_of_common_extension le_rfl h
  · exact compatible_of_common_extension h le_rfl

/-- Every small chain has a lower bound in the actual partial-function
order. Empty chains are included. -/
theorem small_chain_lower_bound (hκ : κ.IsRegular) (hI : Cardinal.mk I < κ)
    (p : I → Condition κ) (hp : ∀ i j, p i ≤ p j ∨ p j ≤ p i) :
    ∃ q : Condition κ, ∀ i, q ≤ p i :=
  ⟨amalgam hκ hI p,
    amalgam_le hκ hI p (fun i j => compatible_of_comparable (hp i j))⟩

end

end Classicism.Meta.ChoiceBoolean.ColumnConditions
