import Classicism.Models.ColourCollapseSubobjects

/-!
# The concrete obstruction to weakly rigid power

Original proof (misc), 22 October 2026. Direct source:
research/2026-10-22/notes/colour-collapse-entrance.md, section 7
(unpaginated). The profile hypotheses below are discharged for denoted
object-language terms in the final assembly; no new domain element or
countermodel is postulated.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

theorem weak_power_not_weak_of_profile
    (Q Z : RD A (.arr (.rel et) .t))
    (hQ : ∀ {V : cat.Ob} (h : A ⟶ V) (X : RD V et),
      prof Q h (X, PUnit.unit) ↔ WeakData X ∧
        model.incl et V X ⊆ model.incl et V ((model.inner (.rel et)).map h (topEntity A)))
    (hZ : ∀ {V : cat.Ob} (h : A ⟶ V) (X : RD V et),
      prof Z h (X, PUnit.unit) ↔ RigidData X) : ¬ WeakData Q := by
  intro hwQ
  have ht : ∀ a : TA (.arr (.rel et) .t) A, prof Q (𝟙 A) a →
      ∀ {V : cat.Ob} (h : A ⟶ V),
        prof Z h (Args.map model.inner (.arr (.rel et) .t) h a) := by
    rintro ⟨X, xu⟩ hx V h
    cases xu
    have hwX : WeakData X := ((hQ (𝟙 A) X).1 hx).1
    have hrX : RigidData X := weak_rigid_at_root X hwX
    change prof Z h ((model.inner (.rel et)).map h X, PUnit.unit)
    exact (hZ h _).2 (rigid_map hrX h)
  have hle : model.incl et B (colour B) ⊆
      model.incl et B ((model.inner (.rel et)).map entrance (topEntity A)) := by
    rw [model.incl_map, incl_top]
    intro p _
    trivial
  have hmember : prof Q entrance (colour B, PUnit.unit) :=
    (hQ entrance (colour B)).2 ⟨colour_weak, hle⟩
  have hrigid : RigidData (colour B) :=
    (hZ entrance (colour B)).1 ((hwQ.2 Z ht) hmember)
  exact colour_not_rigid hrigid

end
end Classicism.Meta.Intensional.ColourCollapse
