import Classicism.Models.ColourCollapseNoLift
import Classicism.Models.ColourCollapseSeparation

/-!
# Rigid Power fails at the family type (et)t

Original proof (misc), 23 October 2026. Direct source:
research/2026-10-23/colour-collapse-higher-power.md, sections 5–6
(unpaginated). The universal family and its rigid-power property are actual
entities of the existing ColourCollapse model. The obstruction is the rigid
coloured label family at B, which has no weakly rigid lift at A.

This extends the established single-type separator with failure of the next
Rigid Power instance. It does not refute full-schema TR + RP => WRP.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory AxiomSet
noncomputable section

theorem topFamily_mem (W : cat.Ob) :
    (Set.univ : Intension model.inner ett W) ∈ Set.range (model.incl ett W) := by
  apply (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) ett W Set.univ).2
  exact ⟨⟨∅, Set.finite_empty, fun _ _ _ _ => rfl⟩,
    fun _ _ _ _ _ _ => trivial⟩

def topFamily (W : cat.Ob) : RD W ett := Classical.choose (topFamily_mem W)

theorem incl_topFamily (W : cat.Ob) :
    model.incl ett W (topFamily W) = Set.univ :=
  Classical.choose_spec (topFamily_mem W)

@[simp] theorem prof_topFamily {W V : cat.Ob} (h : W ⟶ V) (a : TA ett V) :
    prof (topFamily W) h a := by
  unfold prof
  rw [incl_topFamily]
  trivial

theorem topFamily_exact (W : cat.Ob) : ExactImage (topFamily W) := by
  intro V h a
  rcases a with ⟨X, xu⟩
  cases xu
  constructor
  · intro _
    obtain ⟨Y, hY⟩ := transport_surjective h (.rel et) X
    exact ⟨(Y, PUnit.unit), prof_topFamily _ _, Prod.ext hY rfl⟩
  · intro _
    exact prof_topFamily _ _

theorem topFamily_rigid (W : cat.Ob) : RigidData (topFamily W) :=
  exact_rigid _ (topFamily_exact W)

/-- The rigid-power property of the universal family is not even weakly
rigid at A: its future member `labels` has no weakly rigid root lift. -/
theorem higher_power_not_weak :
    ¬ WeakData (rigidPowerEntity (𝟙 A) (topFamily A)) := by
  intro hw
  have hle : model.incl ett B labels ⊆
      model.incl ett B ((model.inner (.rel ett)).map entrance (topFamily A)) := by
    rw [model.incl_map, incl_topFamily]
    intro p _
    trivial
  have hmember : prof (rigidPowerEntity (𝟙 A) (topFamily A)) entrance
      (labels, PUnit.unit) :=
    (prof_rigidPowerEntity (𝟙 A) (topFamily A) entrance labels).2
      ⟨labels_rigid, hle⟩
  obtain ⟨⟨Z, zu⟩, hZ, hZe⟩ :=
    (weak_exact (rigidPowerEntity (𝟙 A) (topFamily A)) hw entrance _).1 hmember
  cases zu
  have hZR : RigidData Z :=
    ((prof_rigidPowerEntity (𝟙 A) (topFamily A) (𝟙 A) Z).1 hZ).1
  have hmap : (model.inner (.rel ett)).map entrance Z = labels :=
    congrArg Prod.fst hZe
  exact no_weak_lift_labels Z (rigid_weak hZR) hmap

/-- Failure of the actual object-language Rigid Power instance at (et)t. -/
theorem not_rigid_power_ett :
    ¬ model.HoldsSentence (P.RigidPower.quoted ett) := by
  intro hp
  have hR : RigidData (rigidPowerEntity (𝟙 A) (topFamily A)) :=
    ((holds_rigidPower_iff (𝟙 A) ett).1 hp) (topFamily A) (topFamily_rigid A)
  exact higher_power_not_weak (rigid_weak hR)

theorem not_holds_rigid_power_schema : ¬ model.HoldsAx P.RigidPower.schema := by
  intro hp
  exact not_rigid_power_ett (hp _ ⟨ett, ⟨⟨trivial, trivial⟩, trivial⟩, rfl⟩)

/-- Exact combined certificate: preserve full root TR, full boxed BF, and
boxed RP at et, while WRP at et and RP at (et)t both fail at the root. -/
theorem higher_countermodel :
    model.IsModel ∧ model.HoldsAx P.TameRigidity.schema ∧
    model.HoldsAx P.NecBarcan.schema ∧
    model.HoldsSentence (P.NecRigidPower.quoted et) ∧
    ¬ model.HoldsSentence (P.WeaklyRigidPower.quoted et) ∧
    ¬ model.HoldsSentence (P.RigidPower.quoted ett) :=
  ⟨isModel, holds_tame_schema, holds_boxed_barcan_schema,
    boxed_rigid_power_et, not_weakly_rigid_power_et, not_rigid_power_ett⟩

end
end Classicism.Meta.Intensional.ColourCollapse
