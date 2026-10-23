import Classicism.Models.ColourCollapsePowerCore
import Classicism.Models.ColourCollapseFormula

/-!
# Full TR and boxed BF with boxed RP_et do not entail WRP_et

Original assembly (misc), 23 October 2026. Direct source:
research/2026-10-22/notes/colour-collapse-entrance.md, sections 3–7
(unpaginated). Every profile premise is discharged for the value of an
actual object-language term. The only positive Rigid Power instance here
is et; this does not refute the full-schema TR + RP conjecture.

Source submission pending the sole integrator's Lean checks. No record's
verification status is changed by this file.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory AxiomSet
noncomputable section

theorem rigid_power_at {W : cat.Ob} (h : A ⟶ W) :
    model.Holds h (P.RigidPower.quoted et) .nil := by
  apply (holds_rigidPower_iff h et).2
  intro F hF
  apply exact_rigid
  exact rigid_power_exact_of_profile F hF (rigidPowerEntity h F)
    (fun k X => prof_rigidPowerEntity h F k X)

theorem boxed_rigid_power_et : model.HoldsSentence (P.NecRigidPower.quoted et) := by
  change model.Holds (𝟙 A) (Term.box (P.RigidPower.quoted et)) .nil
  rw [model.holds_box isModel]
  intro W h
  simpa only [Category.id_comp, IEnv.nil_eq] using rigid_power_at h

theorem not_weakly_rigid_power_et :
    ¬ model.HoldsSentence (P.WeaklyRigidPower.quoted et) := by
  intro hp
  have hweak : WeakData (weakPowerEntity (𝟙 A) (topEntity A)) :=
    ((holds_weaklyRigidPower_iff (𝟙 A) et).1 hp) (topEntity A)
      (rigid_weak (top_rigid A))
  exact weak_power_not_weak_of_profile
    (weakPowerEntity (𝟙 A) (topEntity A)) (rigidTestEntity (𝟙 A) et)
    (fun h X => prof_weakPowerEntity (𝟙 A) (topEntity A) h X)
    (fun h X => prof_rigidTestEntity (𝟙 A) h X) hweak

theorem holds_tame_schema : model.HoldsAx P.TameRigidity.schema := by
  rintro _ ⟨ρ, _, rfl⟩
  exact tame_at_root ρ

theorem holds_boxed_barcan_schema : model.HoldsAx P.NecBarcan.schema := by
  rintro _ ⟨σ, _, rfl⟩
  exact boxed_bf σ

/-- This background deliberately contains only one RP instance (boxed),
whereas Tame Rigidity and boxed Barcan are full schemas. -/
abbrev Background : AxiomSet Signature.pure :=
  (P.TameRigidity.schema ∪ P.NecBarcan.schema) ∪ {P.NecRigidPower.quoted et}

theorem holds_background : model.HoldsAx Background := by
  apply model.holdsAx_union
  · exact model.holdsAx_union holds_tame_schema holds_boxed_barcan_schema
  · intro p hp
    have he : p = P.NecRigidPower.quoted et := Set.mem_singleton_iff.1 hp
    subst p
    exact boxed_rigid_power_et

theorem background_consistent : Background.Consistent :=
  AxiomSet.Consistent.of_model model isModel holds_background

theorem not_theorem_weakly_rigid_power_et :
    ¬ Theorem (Classicism.Meta.C.axioms ∪ Background) (P.WeaklyRigidPower.quoted et) :=
  model.not_theorem_of_model isModel holds_background not_weakly_rigid_power_et

theorem not_entails_weakly_rigid_power :
    ¬ (Background ⟹ P.WeaklyRigidPower.schema) :=
  fun h => not_theorem_weakly_rigid_power_et (h _ ⟨et, ⟨trivial, trivial⟩, rfl⟩)

/-- The exact concrete countermodel target: all-type TR and boxed BF,
boxed RP at et, and failure of WRP at et. -/
theorem central_countermodel :
    model.IsModel ∧ model.HoldsAx P.TameRigidity.schema ∧
    model.HoldsAx P.NecBarcan.schema ∧
    model.HoldsSentence (P.NecRigidPower.quoted et) ∧
    ¬ model.HoldsSentence (P.WeaklyRigidPower.quoted et) :=
  ⟨isModel, holds_tame_schema, holds_boxed_barcan_schema,
    boxed_rigid_power_et, not_weakly_rigid_power_et⟩

end
end Classicism.Meta.Intensional.ColourCollapse
