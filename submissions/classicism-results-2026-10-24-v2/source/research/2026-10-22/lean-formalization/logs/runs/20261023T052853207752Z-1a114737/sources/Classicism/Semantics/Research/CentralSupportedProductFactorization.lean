import Classicism.Semantics.Research.CentralSupportedProduct

/-!
# Supported tuples and the coordinate factorization for Tame Rigidity

The concrete algebraic step of `followup/central-map.md`, §8. This module
does not claim the final Tame Rigidity schema: that requires the exact-image
argument and its object-language satisfaction bridge. All arrows belong to
the unrestricted product, a condition essential to this factorization.
-/

namespace Classicism.Meta.Intensional.Central.Product
open CategoryTheory

variable (I L : Type)

theorem domain_supported (σ : Ty) (W : World I L) (x : (domain I L σ).obj W) :
    Supported (control I L) (domain I L σ) x := by
  cases σ with
  | e => exact individuals_supported I L W x
  | var _ => exact individuals_supported I L W x
  | rel _ =>
    obtain ⟨S, hS⟩ := x.2
    exact ⟨S, fun V h k hk => Subtype.ext (hS V h k hk)⟩

theorem arguments_supported : ∀ (ρ : RTy) (W : World I L)
    (x : (arguments I L ρ).obj W), Supported (control I L) (arguments I L ρ) x
  | .t, _, _ => ⟨⟨∅, Set.countable_empty⟩, fun _ _ _ _ => rfl⟩
  | .arr σ ρ, W, x => by
    obtain ⟨S, hS⟩ := domain_supported I L σ W x.1
    obtain ⟨T, hT⟩ := arguments_supported ρ W x.2
    refine ⟨(control I L).join S T, fun V h k hk => ?_⟩
    apply Prod.ext
    · exact hS V h k ((control I L).join_left S T h k hk)
    · exact hT V h k ((control I L).join_right S T h k hk)

/-- Set an arrow to the identity on S; retain its full remaining coordinates. -/
noncomputable def cut (S : Set I) (m : Arrow I L) : Arrow I L := by
  classical
  exact fun i => if i ∈ S then 1 else m i

theorem cut_on {S : Set I} (m : Arrow I L) {i : I} (hi : i ∈ S) :
    cut I L S m i = 1 := by
  classical
  simp [cut, hi]

theorem cut_off {S : Set I} (m : Arrow I L) {i : I} (hi : i ∉ S) :
    cut I L S m i = m i := by
  classical
  simp [cut, hi]

/-- If m and n agree on S, `m * cut S n = cut S m * n`. -/
theorem cut_factorization {S : Set I} (m n : Arrow I L)
    (hmn : ∀ i ∈ S, m i = n i) :
    m * cut I L S n = cut I L S m * n := by
  classical
  funext i
  by_cases hi : i ∈ S
  · simp [cut, hi, hmn i hi]
  · simp [cut, hi]

theorem cut_fixes {F : World I L ⥤ Type} {W : World I L}
    {S : (control I L).Key W} {x : F.obj W}
    (hx : SupportedBy (control I L) F S x) (m : Arrow I L) :
    F.map (cut I L S.1 m : W ⟶ W) x = x := by
  have he := hx W (cut I L S.1 m) (𝟙 W) (fun i hi => cut_on I L m hi)
  simpa [Functor.map_id] using he

/-- A supported tuple b=n(a) can be lifted along m when m,n agree on a
support of b. The new preimage is obtained using the cut of n. -/
theorem factor_lifts_tuple {F : World I L ⥤ Type} {W : World I L}
    {S : (control I L).Key W} {b : F.obj W}
    (hb : SupportedBy (control I L) F S b) (m n : Arrow I L)
    (hmn : ∀ i ∈ S.1, m i = n i) (a : F.obj W) (ha : F.map n a = b) :
    F.map m (F.map (cut I L S.1 n) a) = b := by
  rw [← FunctorToTypes.map_comp_apply]
  change F.map (m * cut I L S.1 n : W ⟶ W) a = b
  rw [cut_factorization I L m n hmn]
  change F.map (n ≫ (cut I L S.1 m : W ⟶ W)) a = b
  rw [FunctorToTypes.map_comp_apply, ha]
  exact cut_fixes I L hb m

end Classicism.Meta.Intensional.Central.Product
