import Classicism.Models.ColourCollapseHigherFamily
import Classicism.Models.ColourCollapseEvacuation

/-!
# No weakly rigid entrance lift of the coloured label family

Original proof (misc), 23 October 2026. Direct source:
research/2026-10-23/colour-collapse-higher-power.md, section 5
(unpaginated). Supports are finite sets of individuals; the family is infinite.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

theorem label_in_image_of_pin {S : Set Nat} (hS : S.Finite) (x : RD A et)
    (hp : ∀ (V : cat.Ob) (h i : A ⟶ V), AgreeOn cat.De S h i →
      (model.inner (.rel et)).map h x = (model.inner (.rel et)).map i x)
    (h : A ⟶ B) (c : Nat) (he : (model.inner (.rel et)).map h x = label c) :
    c ∈ FunCat.fn h '' S := by
  classical
  by_contra hc
  let d := 2 * (c + 1)
  have hd : colored B d := by dsimp [colored, d]; omega
  obtain ⟨g, hg, hgc⟩ := hit_avoiding (𝟙 B) (hS.image (FunCat.fn h)) hc (fun _ => hd)
  have hag : AgreeOn cat.De S (h ≫ g) h := by
    intro s hs
    change FunCat.fn g (FunCat.fn h s) = FunCat.fn h s
    exact hg (FunCat.fn h s) ⟨s, hs, rfl⟩
  have hh := hp B (h ≫ g) h hag
  rw [FunctorToTypes.map_comp_apply, he, label_map_B] at hh
  have hn := label_injective hh
  rw [hgc] at hn
  dsimp [d] at hn
  omega

/-- No weakly rigid family at A transports to the actual rigid family at B. -/
theorem no_weak_lift_labels (Z : RD A ett) (hw : WeakData Z) :
    (model.inner (.rel ett)).map entrance Z ≠ labels := by
  intro he
  obtain ⟨N, hN, hpZ⟩ := fin_pin (.rel ett) A Z
  obtain ⟨b, hb⟩ := hN.bddAbove
  let n := 2 * (b + 1)
  have hn : n ∉ N := fun hmem => by have := hb hmem; dsimp [n] at *; omega
  have hnc : colored B n := by dsimp [colored, n]; omega
  have hfuture : prof Z entrance (label n, PUnit.unit) := by
    have hh : prof ((model.inner (.rel ett)).map entrance Z) (𝟙 B)
        (label n, PUnit.unit) := by
      rw [he]
      exact (prof_labels (𝟙 B) _).2 ⟨n, hnc, rfl⟩
    simpa only [prof_map, Category.comp_id] using hh
  obtain ⟨⟨x, xu⟩, hx, hxe⟩ := (weak_exact Z hw entrance _).1 hfuture
  cases xu
  have hix : (model.inner (.rel et)).map entrance x = label n := congrArg Prod.fst hxe
  obtain ⟨M, hM, hpM⟩ := fin_pin (.rel et) A x
  let S := N ∪ M
  have hS : S.Finite := hN.union hM
  have hNS : N ⊆ S := Set.subset_union_left
  have hxp : ∀ (V : cat.Ob) (h i : A ⟶ V), AgreeOn cat.De S h i →
      (model.inner (.rel et)).map h x = (model.inner (.rel et)).map i x := by
    intro V h i ha
    exact (model.pinnedO_Incl_iff (.rel et) M x).1 hpM V h i
      (ha.mono cat.De Set.subset_union_right)
  obtain ⟨u, v, hufix, hcover, hreturn, hvfix⟩ := evacuate_return hS hNS
  have hau : AgreeOn cat.De N u (𝟙 A) := by
    intro s hs
    exact hufix s hs
  have hux : prof Z (𝟙 A) ((model.inner (.rel et)).map u x, PUnit.unit) :=
    (prof_agree hpZ hau _).1 (hw.1 (x, PUnit.unit) hx u)
  have himage : prof labels (𝟙 B)
      ((model.inner (.rel et)).map entrance ((model.inner (.rel et)).map u x), PUnit.unit) := by
    rw [← he, prof_map, Category.comp_id]
    exact hw.1 ((model.inner (.rel et)).map u x, PUnit.unit) hux entrance
  obtain ⟨c, hc, hce⟩ := (prof_labels (𝟙 B) _).1 himage
  have hcomp : (model.inner (.rel et)).map (u ≫ entrance) x = label c := by
    simpa only [FunctorToTypes.map_comp_apply] using hce
  obtain ⟨s, hs, hsc⟩ := label_in_image_of_pin hS x hxp (u ≫ entrance) c hcomp
  change FunCat.fn u s = c at hsc
  have hcN : c ∈ N := by
    have hm := hcover s hs (by rw [hsc]; exact hc)
    rwa [hsc] at hm
  have hag : AgreeOn cat.De S ((u ≫ entrance) ≫ v) entrance := by
    intro s hs
    exact hreturn s hs
  have hxx := hxp B ((u ≫ entrance) ≫ v) entrance hag
  rw [FunctorToTypes.map_comp_apply, hcomp, label_map_B, hvfix c hcN, hix] at hxx
  have hcn : c = n := label_injective hxx
  exact hn (hcn ▸ hcN)

end
end Classicism.Meta.Intensional.ColourCollapse
