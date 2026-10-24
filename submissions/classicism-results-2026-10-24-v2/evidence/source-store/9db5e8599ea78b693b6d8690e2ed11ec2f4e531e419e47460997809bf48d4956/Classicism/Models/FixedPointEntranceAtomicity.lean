import Classicism.Models.FixedPointEntranceCompleteness
import Classicism.Semantics.FullModels

/-!
# Root Atomicity in the fixed-point entrance model

Original formalization (misc), 23 October 2026, of
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 3
(unpaginated). The intersection of all admitted root intensions containing
a given tuple is admitted. Boolean complements show that this intersection
has no proper nonempty admitted part. Choosing a tuple in any nonempty
intension therefore supplies an atom below it, at every relational type.
The argument uses actual term closure and root intersections, with no
atomicity, fullness, or abstract atom-existence premise.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Atomicity

open CategoryTheory
noncomputable section

abbrev RD (ρ : RTy) := model.Dom (A tail) (.rel ρ)

/-- Boolean complementation is admitted by the constructed model's term closure. -/
theorem complement_mem {ρ : RTy} (X : RD ρ) :
    (model.incl ρ (A tail) X)ᶜ ∈ Set.range (model.incl ρ (A tail)) := by
  have h := isModel (𝟙 (A tail))
    (Term.app (Term.negR ρ) (Term.v0 : Term Signature.pure [.rel ρ] (.rel ρ)))
    (.cons X .nil)
  have he := model.sem_negR isModel (𝟙 (A tail)) (.cons X .nil) ρ
    (Term.v0 : Term Signature.pure [.rel ρ] (.rel ρ))
  rw [he] at h
  exact h

/-- Intersecting all admitted intensions containing p gives a minimal
nonempty admitted intension containing p. -/
theorem atom_through_tuple {ρ : RTy} (p : Tuple model.inner ρ (A tail)) :
    ∃ Y : RD ρ, p ∈ model.incl ρ (A tail) Y ∧
      (∀ X : RD ρ, p ∈ model.incl ρ (A tail) X →
        model.incl ρ (A tail) Y ⊆ model.incl ρ (A tail) X) ∧
      (∀ Z : RD ρ, model.incl ρ (A tail) Z ⊆ model.incl ρ (A tail) Y →
        (model.incl ρ (A tail) Z).Nonempty →
        model.incl ρ (A tail) Z = model.incl ρ (A tail) Y) := by
  classical
  obtain ⟨Y, hY⟩ := Completeness.intersection_mem
    (fun X : RD ρ => p ∈ model.incl ρ (A tail) X)
  have hpY : p ∈ model.incl ρ (A tail) Y := by
    rw [hY]
    exact fun _ hX => hX
  have hmin : ∀ X : RD ρ, p ∈ model.incl ρ (A tail) X →
      model.incl ρ (A tail) Y ⊆ model.incl ρ (A tail) X := by
    intro X hpX q hq
    rw [hY] at hq
    exact hq X hpX
  refine ⟨Y, hpY, hmin, ?_⟩
  intro Z hZY hZ
  have hpZ : p ∈ model.incl ρ (A tail) Z := by
    by_contra hn
    obtain ⟨C, hC⟩ := complement_mem Z
    have hpC : p ∈ model.incl ρ (A tail) C := by
      rw [hC]
      exact hn
    obtain ⟨q, hq⟩ := hZ
    have hqC := hmin C hpC (hZY hq)
    rw [hC] at hqC
    exact hqC hq
  exact Set.Subset.antisymm hZY (hmin Z hpZ)

/-- The atom condition in the official quotation, expressed by the actual
intension sets, has a witness below every nonempty admitted intension. -/
theorem atom_below {ρ : RTy} (X : RD ρ)
    (hX : model.incl ρ (A tail) X ≠ ∅) :
    ∃ Y : RD ρ,
      (∀ Z : RD ρ,
        (model.incl ρ (A tail) Y = model.incl ρ (A tail) Z ∪ model.incl ρ (A tail) Y ∧
          ¬ model.incl ρ (A tail) Z = model.incl ρ (A tail) Y) ↔
            model.incl ρ (A tail) Z = ∅) ∧
      model.incl ρ (A tail) Y ⊆ model.incl ρ (A tail) X := by
  classical
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hX
  obtain ⟨Y, hpY, hmin, hatom⟩ := atom_through_tuple p
  refine ⟨Y, fun Z => ⟨?_, ?_⟩, hmin X hp⟩
  · rintro ⟨hZY, hne⟩
    by_contra hz
    exact hne (hatom Z (Set.union_eq_right.1 hZY.symm)
      (Set.nonempty_iff_ne_empty.2 hz))
  · intro hz
    refine ⟨?_, ?_⟩
    · rw [hz, Set.empty_union]
    · intro he
      have : p ∈ model.incl ρ (A tail) Z := he.symm ▸ hpY
      rw [hz] at this
      exact this

/-- The actual quoted Atomicity sentence at the root, for every relational type. -/
theorem atomicity_at_root (ρ : RTy) : model.HoldsSentence (P.Atomicity.quoted ρ) := by
  classical
  simp only [Premodel.HoldsSentence, P.Atomicity.quoted, model.holds_forall isModel,
    model.holds_disj isModel, model.holds_exists isModel, model.holds_conj isModel,
    model.holds_neg isModel, model.holds_eq isModel, model.sem_orR isModel,
    Premodel.sem_negR isModel, Premodel.sem_var, IEnv.get]
  have e1 : ∀ S : Set (Tuple model.inner ρ (A tail)), Sᶜ = S ∪ Sᶜ ↔ S = ∅ :=
    fun S => by rw [Set.union_compl_self, Set.compl_univ_iff]
  intro X
  by_cases hx : model.incl ρ (A tail) X = ∅
  · exact Or.inl ((e1 _).2 hx)
  · obtain ⟨Y, hY, hYX⟩ := atom_below X hx
    refine Or.inr ⟨Y, fun Z => ?_, (Set.union_eq_right.2 hYX).symm⟩
    have he := (hY Z).trans (e1 (model.incl ρ (A tail) Z)).symm
    have himp {p q : Prop} (hpq : p → q) : ¬ p ∨ q := by
      by_cases hp : p
      · exact Or.inr (hpq hp)
      · exact Or.inl hp
    exact ⟨himp he.mp, himp he.mpr⟩

theorem holds_atomicity_schema : model.HoldsAx P.Atomicity.schema := by
  rintro _ ⟨ρ, _, rfl⟩
  exact atomicity_at_root ρ

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Atomicity
