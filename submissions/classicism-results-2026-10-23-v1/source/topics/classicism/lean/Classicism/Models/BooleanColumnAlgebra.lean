import Classicism.Models.BooleanColumnConditions
import Classicism.Models.BooleanConditionAutomorphisms
import Classicism.Models.BooleanSupportedPredicates

/-!
# The concrete Boolean algebra and column-permutation action

Original formalization (misc), 23 October 2026, of section 2 of
`research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
This instantiates the general completion and action constructions with
the actual small partial column assignments. The algebra is nontrivial
for infinite κ. Small-table distributivity and the typed Choice verdicts
are separate obligations, not hypotheses of this construction.
-/

namespace Classicism.Meta.ChoiceBoolean.ColumnAlgebra

open ColumnConditions

universe u

abbrev Values (κ : Cardinal.{u}) := ConditionCompletion.Algebra (Condition κ)

theorem nontrivial {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ) :
    Nontrivial (Values κ) := by
  letI : Nonempty (Condition κ) := ⟨empty hκ⟩
  infer_instance

theorem permutationOrderIso_one (κ : Cardinal.{u}) :
    permutationOrderIso (1 : Equiv.Perm κ.out) = OrderIso.refl (Condition κ) := by
  apply DFunLike.ext
  intro p
  apply Condition.ext
  rintro ⟨c, r⟩
  rfl

theorem permutationOrderIso_mul {κ : Cardinal.{u}} (π σ : Equiv.Perm κ.out) :
    permutationOrderIso (π * σ) =
      (permutationOrderIso σ).trans (permutationOrderIso π) := by
  apply DFunLike.ext
  intro p
  apply Condition.ext
  rintro ⟨c, r⟩
  rfl

/-- The complete Boolean automorphism action on actual condition values. -/
def action (κ : Cardinal.{u}) : BooleanAction κ.out (Values κ) where
  map π := ConditionCompletion.map (permutationOrderIso π)
  map_one b := by
    rw [permutationOrderIso_one]
    exact ConditionCompletion.map_refl b
  map_mul π σ b := by
    rw [permutationOrderIso_mul]
    exact (ConditionCompletion.map_comp
      (permutationOrderIso σ) (permutationOrderIso π) b).symm

theorem action_cone {κ : Cardinal.{u}} (π : Equiv.Perm κ.out) (p : Condition κ) :
    (action κ).map π (ConditionCompletion.cone (Condition κ) p) =
      ConditionCompletion.cone (Condition κ) (permute π p) :=
  ConditionCompletion.map_cone (permutationOrderIso π) p

/-- Boolean compatibility retains the concrete partial-assignment relation. -/
theorem cone_compatible {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (p q : Condition κ) :
    ConditionCompletion.cone (Condition κ) p ⊓
      ConditionCompletion.cone (Condition κ) q ≠ ⊥ ↔ Compatible p q :=
  (ConditionCompletion.cone_compatible_iff (Condition κ) p q).trans
    (compatible_iff_common_extension hκ p q).symm

end Classicism.Meta.ChoiceBoolean.ColumnAlgebra
