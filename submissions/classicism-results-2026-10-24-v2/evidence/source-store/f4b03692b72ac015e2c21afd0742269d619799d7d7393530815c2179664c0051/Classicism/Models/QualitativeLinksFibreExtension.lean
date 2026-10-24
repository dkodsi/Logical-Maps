import Classicism.Models.QualitativeLinksBase
import Mathlib.Data.Set.Finite.Lattice

/-!
# Covering a qualitative-link fibre while fixing finite support

Original formalization (misc), 23 October 2026. This supplies the finite
support step used for weak rigidity in the `tame-rigidity` argument of
`models/symmetric-qualitative-links.yaml` (11 October 2026, unpaginated).
The extension construction in Dorr's proof of Proposition 50, p. 26, is
the source antecedent, but this particular case is proved directly.

Three fresh links have images in a two-companion fibre, so two share an
image. Updating one to the requested target preserves surjectivity using
the other. The update preserves R and leaves every point fixed relative
to the original map. No general extension or semantic verdict is assumed.
-/

namespace Classicism.Meta.Intensional.QualitativeLinks.FibreExtension

open CategoryTheory
noncomputable section

def sourceLink (k : Nat) : Node := .link 0 1 k (by decide)

theorem sourceLink_rel (k : Nat) : R (.point 0) (.point 1) (sourceLink k) :=
  R.link 0 1 k (by decide)

def linkIndex : Node → Nat
  | .link _ _ k _ => k
  | _ => 0

theorem sourceLink_injective : Function.Injective sourceLink := by
  intro k l h
  exact congrArg linkIndex h

theorem diagonal_companion {n : Nat} {y : Node}
    (h : R (.point n) (.point n) y) : ∃ b : Bool, y = .companion n b := by
  cases h <;> first | exact ⟨_, rfl⟩ | contradiction

theorem bool_duplicate (a b c : Bool) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Among three fresh source links, two have the same image under a collapse. -/
theorem fresh_duplicate {f : Node → Node} (hf : Collapses f)
    {S : Set Node} (hS : S.Finite) :
    ∃ k l : Nat, k ≠ l ∧ sourceLink k ∉ S ∧ sourceLink l ∉ S ∧
      f (sourceLink k) = f (sourceLink l) := by
  obtain ⟨K, hK⟩ := (hS.image linkIndex).bddAbove
  have fresh : ∀ j : Nat, K < j → sourceLink j ∉ S := by
    intro j hj hz
    have hk : j ≤ K := hK ⟨sourceLink j, hz, rfl⟩
    omega
  obtain ⟨p, hp⟩ := preserves_points hf.2.1 0
  have comp : ∀ k : Nat, ∃ b : Bool, f (sourceLink k) = .companion p b := by
    intro k
    have hr := hf.2.1 (sourceLink_rel k)
    rw [← hf.2.2, hp] at hr
    exact diagonal_companion hr
  obtain ⟨b0, h0⟩ := comp (K + 1)
  obtain ⟨b1, h1⟩ := comp (K + 2)
  obtain ⟨b2, h2⟩ := comp (K + 3)
  rcases bool_duplicate b0 b1 b2 with h01 | h02 | h12
  · exact ⟨K + 1, K + 2, by omega, fresh _ (by omega), fresh _ (by omega),
      h0.trans ((congrArg (Node.companion p) h01).trans h1.symm)⟩
  · exact ⟨K + 1, K + 3, by omega, fresh _ (by omega), fresh _ (by omega),
      h0.trans ((congrArg (Node.companion p) h02).trans h2.symm)⟩
  · exact ⟨K + 2, K + 3, by omega, fresh _ (by omega), fresh _ (by omega),
      h1.trans ((congrArg (Node.companion p) h12).trans h2.symm)⟩

theorem update_surjective {f : Node → Node} (hf : Function.Surjective f)
    {a c : Node} (hac : a ≠ c) (he : f a = f c) (y : Node) :
    Function.Surjective (Function.update f a y) := by
  intro v
  obtain ⟨x, rfl⟩ := hf v
  by_cases hx : x = a
  · subst x
    exact ⟨c, (Function.update_of_ne hac.symm y f).trans he.symm⟩
  · exact ⟨x, Function.update_of_ne hx y f⟩

theorem update_point (f : Node → Node) (k : Nat) (y : Node) (n : Nat) :
    Function.update f (sourceLink k) y (.point n) = f (.point n) := by
  apply Function.update_of_ne
  simp [sourceLink]

theorem update_preserves {f : Node → Node} (hf : Preserves f) (k : Nat)
    {y : Node} (hy : R (f (.point 0)) (f (.point 1)) y) :
    Preserves (Function.update f (sourceLink k) y) := by
  intro x u z hr
  have hx : x ≠ sourceLink k := by
    obtain ⟨n, rfl⟩ := hr.left_point
    simp [sourceLink]
  have hu : u ≠ sourceLink k := by
    cases hr <;> simp [sourceLink]
  rw [Function.update_of_ne hx, Function.update_of_ne hu]
  by_cases hz : z = sourceLink k
  · subst z
    obtain ⟨hx0, hu1⟩ := hr.endpoints_unique (sourceLink_rel k)
    simpa only [Function.update_self, hx0, hu1] using hy
  · simpa only [Function.update_of_ne hz] using hf hr

/-- Change a fresh source link to any requested member of the target
fibre, preserving all finite support values and remaining a collapse. -/
theorem collapse_fibre_cover {f : Node → Node} (hf : Collapses f)
    {S : Set Node} (hS : S.Finite) {y : Node}
    (hy : R (f (.point 0)) (f (.point 1)) y) :
    ∃ g : Node → Node, Collapses g ∧ (∀ x ∈ S, g x = f x) ∧
      ∃ z : Node, R (.point 0) (.point 1) z ∧ g z = y := by
  obtain ⟨k, l, hkl, hk, _, he⟩ := fresh_duplicate hf hS
  have hne : sourceLink k ≠ sourceLink l := fun h => hkl (sourceLink_injective h)
  let g := Function.update f (sourceLink k) y
  have hg : Collapses g := by
    refine ⟨update_surjective hf.1 hne he y, update_preserves hf.2.1 k hy, ?_⟩
    simpa only [g, update_point] using hf.2.2
  refine ⟨g, hg, ?_, sourceLink k, sourceLink_rel k, ?_⟩
  · intro x hx
    have hne : x ≠ sourceLink k := by
      intro heq
      exact hk (heq ▸ hx)
    exact Function.update_of_ne hne y f
  · exact Function.update_self _ _ _

/-- The symmetry case needs no alteration, since injective preservation
reflects R. Together with the collapse case this covers every actual arrow. -/
theorem fibre_cover {f : Node → Node} (hf : Arrow f)
    {S : Set Node} (hS : S.Finite) {y : Node}
    (hy : R (f (.point 0)) (f (.point 1)) y) :
    ∃ g : Node → Node, Arrow g ∧ (∀ x ∈ S, g x = f x) ∧
      ∃ z : Node, R (.point 0) (.point 1) z ∧ g z = y := by
  rcases hf with hf | hf
  · obtain ⟨z, hz⟩ := hf.1.2 y
    refine ⟨f, Or.inl hf, fun _ _ => rfl, z, ?_, hz⟩
    apply reflects hf.2.1 hf.1.1
    simpa only [hz] using hy
  · obtain ⟨g, hg, hagree, z, hz, hgy⟩ := collapse_fibre_cover hf hS hy
    exact ⟨g, Or.inr hg, hagree, z, hz, hgy⟩

/-- The cover theorem stated directly with arrows of Base 3. -/
theorem fibre_cover_arrow (f : star ⟶ star) {S : Set Node} (hS : S.Finite)
    {y : Node} (hy : R (FunCat.fn f (.point 0)) (FunCat.fn f (.point 1)) y) :
    ∃ g : star ⟶ star, (∀ x ∈ S, FunCat.fn g x = FunCat.fn f x) ∧
      ∃ z : Node, R (.point 0) (.point 1) z ∧ FunCat.fn g z = y := by
  obtain ⟨g, hg, hagree, z, hz, hgy⟩ := fibre_cover f.property hS hy
  exact ⟨FunCat.arr g hg, hagree, z, hz, hgy⟩

end
end Classicism.Meta.Intensional.QualitativeLinks.FibreExtension
