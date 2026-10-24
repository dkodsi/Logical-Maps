import Classicism.Models.FixedPointEntranceModel
import Classicism.Semantics.IntensionalFacts

/-!
# Distinctness failure at the fixed-point entrance

Original proof (misc), 23 October 2026. Source:
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 6
(unpaginated). The actual root-only proposition and bottom are distinct
but have the same transport to the tail. Individual Barcan holds at every
accessible object because the interpreted individual domains are singleton.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Distinctness

open CategoryTheory
noncomputable section

def rootOnly : model.Dom (A tail) (.rel .t) :=
  ⟨{p | p.1 = false},
    ⟨∅, Set.finite_empty, root_pinned tail (intensionAction pointAction) _⟩,
    fun _ _ _ _ _ hx => hx⟩

def zero : model.Dom (A tail) (.rel .t) :=
  ⟨∅, ⟨∅, Set.finite_empty, root_pinned tail (intensionAction pointAction) _⟩,
    fun _ _ _ _ _ hx => False.elim hx⟩

theorem rootOnly_ne_zero : rootOnly ≠ zero := by
  intro he
  have h := congrArg (fun q : model.Dom (A tail) (.rel .t) =>
    (⟨A tail, PUnit.unit, 𝟙 (A tail)⟩ :
      Σ V : cone.Ob, (pointAction : cone.Ob ⥤ Type).obj V × (A tail ⟶ V)) ∈ q.val) he
  have ht : (⟨A tail, PUnit.unit, 𝟙 (A tail)⟩ :
      Σ V : cone.Ob, (pointAction : cone.Ob ⥤ Type).obj V × (A tail ⟶ V)) ∈ rootOnly.val := rfl
  exact (Eq.mp h ht : False)

theorem transported_equal :
    (model.inner (.rel .t)).map (entrance tail) rootOnly =
      (model.inner (.rel .t)).map (entrance tail) zero := by
  apply Subtype.ext
  ext ⟨V, x, h⟩
  cases V with
  | false => exact False.elim h.property
  | true =>
      change (true = false) ↔ False
      simp

theorem not_nd_t : ¬ model.HoldsSentence (Sentence.nd (.rel .t)) := by
  intro H
  exact rootOnly_ne_zero
    (((model.holds_nd_iff isModel (.rel .t) (𝟙 (A tail))).mp H)
      (entrance tail) transported_equal)

theorem bf_e_at {W : cone.Ob} (h : A tail ⟶ W) :
    model.Holds h (Sentence.bf .e) .nil := by
  apply model.holds_bf_of_surjective isModel .e h
  intro V k x
  exact ⟨PUnit.unit, @Subsingleton.elim _ (individual_singleton V) _ _⟩

theorem bf_e : model.HoldsSentence (Sentence.bf .e) := bf_e_at (𝟙 (A tail))

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Distinctness
