import Classicism.Models.FixedPointEntranceBase

/-!
# Root relations in a fixed-point entrance category

Original formalization (misc), 23 October 2026, of sections 1--3 of
`research/2026-10-22/notes/fixed-point-entrance-cone.md` (unpaginated).
The root domain is exactly pairs of an arbitrary actual extension and a
symmetry-invariant future extension. In particular, the exact image of
any actual extension is admitted. These are domain-construction results,
not assumptions of rigidity or comprehension sentences.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance

open CategoryTheory
noncomputable section

variable (T : Tail) (F : (cat T).Ob ⥤ Type)

def pairRaw (E : Set (F.obj (A T))) (S : Set (F.obj (B T))) :
    (intensionAction F).obj (A T) :=
  fun p => match p with
  | ⟨false, x, _⟩ => x ∈ E
  | ⟨true, x, _⟩ => x ∈ S

theorem pairRaw_injective {E E' : Set (F.obj (A T))} {S S' : Set (F.obj (B T))}
    (h : pairRaw T F E S = pairRaw T F E' S') : E = E' ∧ S = S' := by
  constructor
  · ext x
    exact Set.ext_iff.mp h ⟨A T, x, 𝟙 (A T)⟩
  · ext x
    exact Set.ext_iff.mp h ⟨B T, x, entrance T⟩

/-- Every root intension is literally one such pair: there is only one
outgoing arrow to each object. -/
theorem exists_pairRaw (H : (intensionAction F).obj (A T)) :
    ∃ E S, H = pairRaw T F E S := by
  refine ⟨{x | (⟨A T, x, 𝟙 (A T)⟩ : Σ V, F.obj V × (A T ⟶ V)) ∈ H},
    {x | (⟨B T, x, entrance T⟩ : Σ V, F.obj V × (A T ⟶ V)) ∈ H}, ?_⟩
  ext ⟨V, x, h⟩
  cases V with
  | false =>
    have he := root_endo_unique T h
    subst h
    rfl
  | true =>
    have he := entrance_unique T h
    subst h
    rfl

def Invariant (S : Set (F.obj (B T))) : Prop :=
  ∀ (g : B T ⟶ B T), g ∈ syms T (B T) → ∀ x ∈ S, F.map g x ∈ S

theorem pairRaw_symmetric_iff (E : Set (F.obj (A T))) (S : Set (F.obj (B T))) :
    RawSym (syms T) F (pairRaw T F E S) ↔ Invariant T F S := by
  constructor
  · intro h g hg x hx
    exact h (B T) x (entrance T) g hg hx
  · intro h V x k g hg hx
    cases V with
    | false =>
      have he := root_endo_unique T g
      subst g
      change F.map (𝟙 (A T)) x ∈ E
      rw [Functor.map_id_apply F (A T) x]
      exact hx
    | true => exact h g hg x hx

/-- Finite support imposes no further restriction at the root. -/
theorem pairRaw_admitted_iff (E : Set (F.obj (A T))) (S : Set (F.obj (B T))) :
    (∃ q : (symPinnedAction (cat T).De (syms T) (PinIdeal.fin (cat T).De) F).obj (A T),
      q.val = pairRaw T F E S) ↔ Invariant T F S := by
  constructor
  · rintro ⟨q, he⟩
    apply (pairRaw_symmetric_iff T F E S).mp
    rw [← he]
    exact q.property.2
  · intro h
    exact ⟨⟨pairRaw T F E S,
      ⟨∅, Set.finite_empty, root_pinned T (intensionAction F) _⟩,
      (pairRaw_symmetric_iff T F E S).mpr h⟩, rfl⟩

/-- Every element in an exact image from the root is fixed by all tail
arrows, so its symmetry invariance requires no hypothesis on E. -/
theorem exactImage_invariant (E : Set (F.obj (A T))) :
    Invariant T F (F.map (entrance T) '' E) := by
  intro g _ x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [transport_fixed T F y g]
  exact ⟨y, hy, rfl⟩

theorem exactImage_admitted (E : Set (F.obj (A T))) :
    ∃ q : (symPinnedAction (cat T).De (syms T) (PinIdeal.fin (cat T).De) F).obj (A T),
      q.val = pairRaw T F E (F.map (entrance T) '' E) :=
  (pairRaw_admitted_iff T F E _).mpr (exactImage_invariant T F E)

end
end Classicism.Meta.Intensional.FixedPointEntrance
