import Classicism.Models.FixedPointEntranceModel
import Classicism.Certified.Schemas

/-!
# Full Boolean Completeness at the concrete fixed-point entrance

Original formalization (misc), 23 October 2026, of
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 3
(unpaginated). Arbitrary intersections of admitted root intensions are
symmetric. Unique outgoing root arrows make each intersection pinned by
the empty set, so it is admitted in the actual recursively constructed
domain. This supplies the greatest lower bounds required by the quoted
Boolean Completeness schema at every relational type.

This is an unboxed root verdict; no completeness verdict at the tail is
claimed, and no admission or greatest-lower-bound premise is assumed.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Completeness

open CategoryTheory
noncomputable section

abbrev RD (ρ : RTy) := model.Dom (A tail) (.rel ρ)

/-- An arbitrary intersection of root-admitted intensions. -/
def intersectionRaw {ρ : RTy} (S : Set (RD ρ)) :
    Intension model.inner ρ (A tail) :=
  fun p => ∀ X : RD ρ, X ∈ S → p ∈ model.incl ρ (A tail) X

/-- Every such intersection is genuinely in the constructed domain. -/
theorem intersection_mem {ρ : RTy} (S : Set (RD ρ)) :
    intersectionRaw S ∈ Set.range (model.incl ρ (A tail)) := by
  apply (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
    (PinIdeal.fin cone.De) ρ (A tail) (intersectionRaw S)).2
  refine ⟨⟨∅, Set.finite_empty, ?_⟩, ?_⟩
  · intro V h i _
    have he : h = i := (root_hom_subsingleton tail V).elim h i
    subst i
    rfl
  · intro V a k g hg ha X hX
    have hs := ((SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
      (PinIdeal.fin cone.De) ρ (A tail) (model.incl ρ (A tail) X)).1 ⟨X, rfl⟩).2
    exact hs V a k g hg (ha X hX)

/-- An arbitrary union of root-admitted intensions. -/
def unionRaw {ρ : RTy} (S : Set (RD ρ)) :
    Intension model.inner ρ (A tail) :=
  fun p => ∃ X : RD ρ, X ∈ S ∧ p ∈ model.incl ρ (A tail) X

theorem union_mem {ρ : RTy} (S : Set (RD ρ)) :
    unionRaw S ∈ Set.range (model.incl ρ (A tail)) := by
  apply (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
    (PinIdeal.fin cone.De) ρ (A tail) (unionRaw S)).2
  refine ⟨⟨∅, Set.finite_empty, ?_⟩, ?_⟩
  · intro V h i _
    have he : h = i := (root_hom_subsingleton tail V).elim h i
    subst i
    rfl
  · intro V a k g hg
    rintro ⟨X, hX, ha⟩
    have hs := ((SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
      (PinIdeal.fin cone.De) ρ (A tail) (model.incl ρ (A tail) X)).1 ⟨X, rfl⟩).2
    exact ⟨X, hX, hs V a k g hg ha⟩

def family {ρ : RTy} (F : RD (.arr (.rel ρ) .t)) (X : RD ρ) : Prop :=
  (⟨A tail, (X, PUnit.unit), 𝟙 (A tail)⟩ :
    Tuple model.inner (.arr (.rel ρ) .t) (A tail)) ∈ model.incl _ (A tail) F

/-- The intersection of each represented family is its greatest lower
bound under inclusion of intensions. -/
theorem root_glbs (ρ : RTy) (F : RD (.arr (.rel ρ) .t)) :
    ∃ y : RD ρ, ∀ z : RD ρ,
      (∀ X : RD ρ, family F X → model.incl ρ (A tail) z ⊆ model.incl ρ (A tail) X) ↔
        model.incl ρ (A tail) z ⊆ model.incl ρ (A tail) y := by
  obtain ⟨y, hy⟩ := intersection_mem (family F)
  refine ⟨y, fun z => ⟨?_, ?_⟩⟩
  · intro hz p hp
    rw [hy]
    exact fun X hX => hz X hX hp
  · intro hz X hX p hp
    have hm := hz hp
    rw [hy] at hm
    exact hm X hX

/-- The actual quoted Boolean Completeness instance, for every relational
type, in the concrete entrance model. -/
theorem root_bc (ρ : RTy) : model.HoldsSentence (P.BooleanCompleteness.quoted ρ) := by
  exact (model.holds_bc_iff isModel ρ (𝟙 (A tail))).2 (root_glbs ρ)

theorem holds_bc_schema : model.HoldsAx P.BooleanCompleteness.schema := by
  rintro _ ⟨ρ, _, rfl⟩
  exact root_bc ρ

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Completeness
