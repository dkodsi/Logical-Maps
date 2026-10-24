import Classicism.Semantics.FullModels

/-!
# Atomicity from admitted singleton intensions

The singleton argument used for full action models only needs singletons to be
admitted.  This weaker hypothesis also applies to coalesced extensional Henkin
models, whose component domains need not contain all external relations.

The argument is the one in `Premodel.holds_atomicity` (the database's
`full-atomicity` argument), with fullness replaced by its exact local use.
This generalization was formalized on 23 October 2026 at Daniel Kodsi's request.
No existence of a Henkin component, or of a CH countermodel, is assumed here.
-/

namespace Classicism.Meta.Intensional.Premodel

open CategoryTheory

variable {C : Type} [SmallCategory C]

/-- At this object and type, every singleton intension is admitted. -/
def HasSingletons (B : Premodel Signature.pure C) (ρ : RTy) (W : C) : Prop :=
  ∀ p : Tuple B.inner ρ W, ∃ y : B.Dom W (.rel ρ), B.incl ρ W y = {p}

/-- Fullness is sufficient, but is not required by the atomicity proof. -/
theorem Full.hasSingletons {B : Premodel Signature.pure C} (hF : B.Full)
    (ρ : RTy) (W : C) : B.HasSingletons ρ W :=
  fun p => hF ρ W {p}

theorem holds_atomicity_of_singletons {B : Premodel Signature.pure C}
    (M : B.IsModel) {W : C} (h : B.W₀ ⟶ W) (ρ : RTy)
    (hS : B.HasSingletons ρ W) : B.Holds h (P.Atomicity.quoted ρ) .nil := by
  classical
  simp only [P.Atomicity.quoted, B.holds_forall M, B.holds_disj M,
    B.holds_exists M, B.holds_conj M, B.holds_neg M, B.holds_eq M,
    B.sem_orR M, sem_negR M, sem_var, IEnv.get]
  have e1 : ∀ S : Set (Tuple B.inner ρ W), Sᶜ = S ∪ Sᶜ ↔ S = ∅ := fun S => by
    rw [Set.union_compl_self, Set.compl_univ_iff]
  intro x
  by_cases hx : B.incl ρ W x = ∅
  · exact Or.inl ((e1 _).2 hx)
  · right
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hx
    obtain ⟨y, hy⟩ := hS p
    have e2 : ∀ S : Set (Tuple B.inner ρ W),
        ({p} = S ∪ {p} ∧ ¬ S = {p}) ↔ S = ∅ := fun S => by
      constructor
      · rintro ⟨h1, h2⟩
        have hs : S ⊆ {p} := Set.union_eq_right.1 h1.symm
        exact (Set.subset_singleton_iff_eq.1 hs).resolve_right h2
      · rintro rfl
        exact ⟨(Set.empty_union _).symm, fun e => Set.singleton_ne_empty p e.symm⟩
    refine ⟨y, fun z => ?_, ?_⟩
    · rw [hy, e1, e2]
      tauto
    · rw [hy]
      exact (Set.union_eq_right.2 (Set.singleton_subset_iff.2 hp)).symm

theorem holds_box_atomicity_of_singletons {B : Premodel Signature.pure C}
    (M : B.IsModel) {W : C} (h : B.W₀ ⟶ W) (ρ : RTy)
    (hS : ∀ {V : C}, (W ⟶ V) → B.HasSingletons ρ V) :
    B.Holds h (P.NecAtomicity.quoted ρ) .nil := by
  show B.Holds h (Term.box (P.Atomicity.quoted ρ)) .nil
  rw [B.holds_box M]
  intro V k
  exact holds_atomicity_of_singletons M (h ≫ k) ρ (hS k)

end Classicism.Meta.Intensional.Premodel

#print axioms Classicism.Meta.Intensional.Premodel.holds_atomicity_of_singletons
#print axioms Classicism.Meta.Intensional.Premodel.holds_box_atomicity_of_singletons
