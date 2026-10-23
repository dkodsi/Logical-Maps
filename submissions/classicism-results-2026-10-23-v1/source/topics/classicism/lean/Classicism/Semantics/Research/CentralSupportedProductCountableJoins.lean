import Classicism.Semantics.Research.CentralSupportedProduct

/-!
# Actual external countable joins in the supported product

Source: `followup/central-map.md`, §§1 and 10. This is the semantic join
construction, not yet the internal Countable Boolean Completeness schema.
That schema additionally needs the internal finite-cardinality successor-
orbit bridge; external countability is not silently substituted for it.
-/

namespace Classicism.Meta.Intensional.Central.Product

variable (I L : Type)

theorem union_supported {ι : Type} [Countable ι] {ρ : RTy} {W : World I L}
    (F : ι → (domain I L (.rel ρ)).obj W) :
    Supported (control I L) (intensionAction (arguments I L ρ)) (⋃ i, (F i).1) := by
  classical
  choose S hSc hS using fun i => profile_support I L (F i)
  apply supported_of_profile I L (Set.countable_iUnion hSc)
  intro V a h k hk
  simp only [Set.mem_iUnion]
  apply exists_congr
  intro i
  exact hS i V a h k (fun j hj => hk j (Set.mem_iUnion.2 ⟨i, hj⟩))

noncomputable def countableJoin {ι : Type} [Countable ι] {ρ : RTy} {W : World I L}
    (F : ι → (domain I L (.rel ρ)).obj W) : (domain I L (.rel ρ)).obj W :=
  ⟨⋃ i, (F i).1, union_supported I L F⟩

theorem countableJoin_upper {ι : Type} [Countable ι] {ρ : RTy} {W : World I L}
    (F : ι → (domain I L (.rel ρ)).obj W) (i : ι) :
    (F i).1 ⊆ (countableJoin I L F).1 :=
  fun _ h => Set.mem_iUnion.2 ⟨i, h⟩

theorem countableJoin_least {ι : Type} [Countable ι] {ρ : RTy} {W : World I L}
    (F : ι → (domain I L (.rel ρ)).obj W) (Z : (domain I L (.rel ρ)).obj W)
    (hZ : ∀ i, (F i).1 ⊆ Z.1) : (countableJoin I L F).1 ⊆ Z.1 := by
  intro a ha
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
  exact hZ i hi

/-- Countable collections of entire relations have their actual pointwise
union as an admitted least upper bound under full-intension inclusion. -/
theorem countable_set_has_lub {ρ : RTy} {W : World I L}
    (E : Set ((domain I L (.rel ρ)).obj W)) (hE : E.Countable) :
    ∃ J : (domain I L (.rel ρ)).obj W,
      (∀ F ∈ E, F.1 ⊆ J.1) ∧
      ∀ Z : (domain I L (.rel ρ)).obj W, (∀ F ∈ E, F.1 ⊆ Z.1) → J.1 ⊆ Z.1 := by
  letI : Countable E := hE
  let F : E → (domain I L (.rel ρ)).obj W := fun x => x.1
  refine ⟨countableJoin I L F, ?_, ?_⟩
  · intro x hx
    exact countableJoin_upper I L F ⟨x, hx⟩
  · intro Z hZ
    exact countableJoin_least I L F Z (fun x => hZ x.1 x.2)

end Classicism.Meta.Intensional.Central.Product
