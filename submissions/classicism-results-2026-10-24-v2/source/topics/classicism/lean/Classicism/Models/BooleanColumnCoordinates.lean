import Classicism.Models.BooleanColumnAlgebra

/-!
# Concrete Boolean coordinate values

Original formalization (misc), 23 October 2026, of sections 2 and 7 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
Coordinate truth values are actual singleton-condition cones. They move
with column permutations. Below any condition, two distinct columns can
be assigned opposite bits on a fresh row. No independence or separating
model verdict is assumed.
-/

namespace Classicism.Meta.ChoiceBoolean.ColumnCoordinates

open ColumnConditions ColumnAlgebra

universe u

noncomputable section

variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)

abbrev cone (p : Condition κ) : Values κ := ConditionCompletion.cone (Condition κ) p

def coordinate (i r : κ.out) : Values κ := cone (singleton hκ (i, r) true)

theorem le_singleton {p : Condition κ} {a : Point κ} {b : Bool}
    (h : p a = some b) : p ≤ singleton hκ a b := by
  classical
  intro x c hx
  by_cases he : x = a
  · subst x
    have hc : b = c := Option.some.inj ((singleton_apply hκ a b).symm.trans hx)
    simpa only [hc] using h
  · simp [ColumnConditions.singleton, he] at hx

theorem false_cone_le_complement (i r : κ.out) :
    cone (singleton hκ (i, r) false) ≤ (coordinate hκ i r)ᶜ := by
  have hz : cone (singleton hκ (i, r) false) ⊓ coordinate hκ i r = ⊥ := by
    by_contra hn
    have hc := (ColumnAlgebra.cone_compatible hκ
      (singleton hκ (i, r) false) (singleton hκ (i, r) true)).mp hn
    have he := hc (i, r) false true (singleton_apply hκ (i, r) false)
      (singleton_apply hκ (i, r) true)
    cases he
  exact le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hz.le)

theorem permute_singleton (π : Equiv.Perm κ.out) (i r : κ.out) (b : Bool) :
    permute π (singleton hκ (i, r) b) = singleton hκ (π i, r) b := by
  classical
  apply Condition.ext
  rintro ⟨j, s⟩
  change (if (π.symm j, s) = (i, r) then some b else none) =
    if (j, s) = (π i, r) then some b else none
  have he : (π.symm j, s) = (i, r) ↔ (j, s) = (π i, r) := by
    constructor
    · intro h
      have hj := congrArg (fun z : Point κ => π z.1) h
      have hs := congrArg Prod.snd h
      exact Prod.ext (by simpa only [Equiv.apply_symm_apply] using hj) hs
    · intro h
      have hj := congrArg (fun z : Point κ => π.symm z.1) h
      have hs := congrArg Prod.snd h
      exact Prod.ext (by simpa only [Equiv.symm_apply_apply] using hj) hs
  by_cases h : (π.symm j, s) = (i, r)
  · simp only [if_pos h, if_pos (he.mp h)]
  · have h' : (j, s) ≠ (π i, r) := fun h' => h (he.mpr h')
    simp only [if_neg h, if_neg h']

theorem coordinate_equivariant (π : Equiv.Perm κ.out) (i r : κ.out) :
    (action κ).map π (coordinate hκ i r) = coordinate hκ (π i) r := by
  rw [coordinate, action_cone, permute_singleton]
  rfl

/-- Opposite bits can be imposed below every starting condition, at an
actual unused row. -/
theorem opposite_refinement (p : Condition κ) (i j : κ.out) (hij : i ≠ j) :
    ∃ r, ∃ q : Condition κ, q ≤ p ∧
      cone q ≤ coordinate hκ i r ∧ cone q ≤ (coordinate hκ j r)ᶜ := by
  classical
  obtain ⟨r, hr⟩ := exists_fresh_row p
  let s := put hκ p (i, r) true
  have hs : s ≤ p := put_le hκ p (i, r) true (hr i)
  have hs_j : s (j, r) = none := by
    change ChoiceFreshColumns.merge (singleton hκ (i, r) true).toFun p.toFun (j, r) = none
    simp [ChoiceFreshColumns.merge, ColumnConditions.singleton, Ne.symm hij, hr j]
  let q := put hκ s (j, r) false
  have hq : q ≤ s := put_le hκ s (j, r) false hs_j
  refine ⟨r, q, hq.trans hs, ?_, ?_⟩
  · apply ConditionCompletion.cone_mono (Condition κ)
    exact le_singleton hκ (hq (i, r) true (put_apply hκ p (i, r) true))
  · exact (ConditionCompletion.cone_mono (Condition κ)
      (le_singleton hκ (put_apply hκ s (j, r) false))).trans
      (false_cone_le_complement hκ j r)

end

end Classicism.Meta.ChoiceBoolean.ColumnCoordinates
