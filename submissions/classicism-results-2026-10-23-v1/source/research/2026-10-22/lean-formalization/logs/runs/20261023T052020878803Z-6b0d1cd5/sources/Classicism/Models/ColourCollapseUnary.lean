import Classicism.Models.ColourCollapseWitness

/-!
# Canonical unary relations and the finite-or-universal classification

Original proofs (misc), 22 October 2026. Direct source:
research/2026-10-22/notes/colour-collapse-entrance.md, sections 5–6
(unpaginated). This is a source submission, pending the sole integrator's
compiler check. No classification is assumed as an interface field.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

theorem rigid_weak {ρ : RTy} {W : cat.Ob} {F : RD W ρ}
    (hF : RigidData F) : WeakData F := by
  simpa only [FunctorToTypes.map_id_apply] using hF (𝟙 W)

theorem rigid_map {ρ : RTy} {W V : cat.Ob} {F : RD W ρ}
    (hF : RigidData F) (h : W ⟶ V) : RigidData ((model.inner (.rel ρ)).map h F) := by
  intro U k
  simpa only [FunctorToTypes.map_comp_apply] using hF (h ≫ k)

theorem weak_eq_of_current {ρ : RTy} {W : cat.Ob} {F G : RD W ρ}
    (hF : WeakData F) (hG : WeakData G)
    (he : ∀ a, prof F (𝟙 W) a ↔ prof G (𝟙 W) a) : F = G := by
  apply model.Incl_injective (.rel ρ) W
  apply Set.Subset.antisymm
  · exact hF.2 G (fun a ha V h => hG.1 a ((he a).1 ha) h)
  · exact hG.2 F (fun a ha V h => hF.1 a ((he a).2 ha) h)

def extension {W : cat.Ob} (F : RD W et) : Set Nat :=
  {x | prof F (𝟙 W) (x, PUnit.unit)}

def finiteRaw (W : cat.Ob) (D : Set Nat) : Intension model.inner et W :=
  fun p => ∃ x ∈ D, FunCat.fn p.2.2 x = p.2.1.1

theorem finite_mem (W : cat.Ob) {D : Set Nat} (hD : D.Finite) :
    finiteRaw W D ∈ Set.range (model.incl et W) := by
  apply (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) et W (finiteRaw W D)).2
  refine ⟨⟨D, hD, ?_⟩, ?_⟩
  · intro V h i ha
    ext ⟨U, a, k⟩
    change (∃ x ∈ D, FunCat.fn k (FunCat.fn h x) = a.1) ↔
      (∃ x ∈ D, FunCat.fn k (FunCat.fn i x) = a.1)
    constructor <;> rintro ⟨x, hx, he⟩
    · exact ⟨x, hx, by rw [← ha x hx]; exact he⟩
    · exact ⟨x, hx, by rw [ha x hx]; exact he⟩
  · intro V a k g _
    rintro ⟨x, hx, he⟩
    exact ⟨x, hx, congrArg (FunCat.fn g) he⟩

def finiteEntity (W : cat.Ob) (D : Set Nat) (hD : D.Finite) : RD W et :=
  Classical.choose (finite_mem W hD)

theorem incl_finite (W : cat.Ob) (D : Set Nat) (hD : D.Finite) :
    model.incl et W (finiteEntity W D hD) = finiteRaw W D :=
  Classical.choose_spec (finite_mem W hD)

@[simp] theorem prof_finite {W V : cat.Ob} (D : Set Nat) (hD : D.Finite)
    (h : W ⟶ V) (a : TA et V) :
    prof (finiteEntity W D hD) h a ↔ ∃ x ∈ D, FunCat.fn h x = a.1 := by
  unfold prof
  rw [incl_finite]
  rfl

@[simp] theorem extension_finite (W : cat.Ob) (D : Set Nat) (hD : D.Finite) :
    extension (finiteEntity W D hD) = D := by
  ext x
  simp [extension, FunCat.fn]

theorem finite_exact (W : cat.Ob) (D : Set Nat) (hD : D.Finite) :
    ExactImage (finiteEntity W D hD) := by
  intro V h a
  rcases a with ⟨a, au⟩
  cases au
  constructor
  · intro ha
    obtain ⟨x, hx, he⟩ := (prof_finite D hD h _).1 ha
    refine ⟨(x, PUnit.unit), (prof_finite D hD (𝟙 W) _).2 ⟨x, hx, rfl⟩, ?_⟩
    exact Prod.ext he rfl
  · rintro ⟨⟨x, xu⟩, hx, he⟩
    obtain ⟨y, hy, hyx⟩ := (prof_finite D hD (𝟙 W) _).1 hx
    change y = x at hyx
    subst y
    exact (prof_finite D hD h _).2 ⟨x, hy, congrArg Prod.fst he⟩

theorem finite_rigid (W : cat.Ob) (D : Set Nat) (hD : D.Finite) :
    RigidData (finiteEntity W D hD) := exact_rigid _ (finite_exact W D hD)

theorem top_mem (W : cat.Ob) :
    (Set.univ : Intension model.inner et W) ∈ Set.range (model.incl et W) := by
  apply (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) et W Set.univ).2
  exact ⟨⟨∅, Set.finite_empty, fun _ _ _ _ => rfl⟩, fun _ _ _ _ _ _ => trivial⟩

def topEntity (W : cat.Ob) : RD W et := Classical.choose (top_mem W)

theorem incl_top (W : cat.Ob) : model.incl et W (topEntity W) = Set.univ :=
  Classical.choose_spec (top_mem W)

@[simp] theorem prof_top {W V : cat.Ob} (h : W ⟶ V) (a : TA et V) :
    prof (topEntity W) h a := by
  unfold prof
  rw [incl_top]
  trivial

theorem top_exact (W : cat.Ob) : ExactImage (topEntity W) := by
  intro V h a
  constructor
  · intro _
    obtain ⟨x, hx⟩ := h.2.2.1 a.1
    exact ⟨(x, PUnit.unit), prof_top _ _, Prod.ext hx (Subsingleton.elim _ _)⟩
  · intro _
    exact prof_top _ _

theorem top_rigid (W : cat.Ob) : RigidData (topEntity W) := exact_rigid _ (top_exact W)

/-- A finite prescription may additionally send one fresh point to a
colour-compatible target. The extension is an actual allowed surjection. -/
theorem hit_avoiding {W V : cat.Ob} (h : W ⟶ V) {S : Set Nat} (hS : S.Finite)
    {x y : Nat} (hx : x ∉ S) (hc : colored W x → colored V y) :
    ∃ j : W ⟶ V, AgreeOn cat.De S j h ∧ FunCat.fn j x = y := by
  classical
  let q := Function.update (FunCat.fn h) x y
  have hq : ∀ n ∈ S ∪ {x}, colored W n → colored V (q n) := by
    intro n _ hn
    by_cases he : n = x
    · subst n; simpa [q] using hc hn
    · simpa [q, he] using h.2.2.2 n hn
  obtain ⟨j, hj⟩ := extend_finite h.2.1 (hS.union (Set.finite_singleton x)) q hq
  refine ⟨j, ?_, ?_⟩
  · intro n hn
    rw [hj n (Or.inl hn)]
    have he : n ≠ x := fun he => hx (he ▸ hn)
    simp [q, he]
  · rw [hj x (Or.inr (Set.mem_singleton x))]
    simp [q]

theorem exists_outside {D S : Set Nat} (hD : ¬ D.Finite) (hS : S.Finite) :
    ∃ x ∈ D, x ∉ S := by
  classical
  by_contra hn
  push_neg at hn
  exact hD (hS.subset hn)

theorem fresh_uncoloured_forces_top {W : cat.Ob} (F : RD W et) (hw : WeakData F)
    {S : Set Nat} (hS : S.Finite) (hp : model.PinnedO (.rel et) (W := W) S (model.incl et W F))
    {x : Nat} (hx : x ∈ extension F) (hxs : x ∉ S) (hxc : ¬ colored W x) :
    extension F = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨j, hj, hxy⟩ := hit_avoiding (𝟙 W) hS hxs (fun hc => (hxc hc).elim) (y := y)
  have hm := hw.1 (x, PUnit.unit) hx j
  change prof F j (FunCat.fn j x, PUnit.unit) at hm
  rw [hxy] at hm
  exact (prof_agree hp hj _).1 hm

theorem coloured_lower_at {F : RD B et} (hw : WeakData F)
    (hD : ∀ x, colored B x → x ∈ extension F) {V : cat.Ob} (h : B ⟶ V)
    {a : Nat} (ha : colored V a) : prof F h (a, PUnit.unit) := by
  obtain ⟨S, hS, hp⟩ := fin_pin (.rel et) B F
  obtain ⟨b, hb⟩ := hS.bddAbove
  let x := 2 * (b + 1)
  have hx : x ∉ S := fun hs => by have := hb hs; dsimp [x] at *; omega
  have hxc : colored B x := by dsimp [colored, x]; omega
  obtain ⟨j, hj, hjx⟩ := hit_avoiding h hS hx (fun _ => ha)
  have hm := hw.1 (x, PUnit.unit) (hD x hxc) j
  change prof F j (FunCat.fn j x, PUnit.unit) at hm
  rw [hjx] at hm
  exact (prof_agree hp hj _).1 hm

/-- The only possible infinite proper extension at B is excluded using
the finite colour set at C and the concrete merging endomorphism. -/
theorem no_coloured_exception {F : RD B et} (hr : RigidData F)
    {K : Set Nat} (hK : K.Finite)
    (hl : ∀ x, colored B x → x ∈ extension F)
    (hu : ∀ x ∈ extension F, colored B x ∨ x ∈ K) : False := by
  have hw := rigid_weak hr
  obtain ⟨h, hh⟩ := extend_finite (W := B) (V := C) (by decide) hK (fun _ => 0)
    (fun _ _ _ => by decide)
  let E : Set Nat := {0, 1}
  have hE : E.Finite := (Set.finite_singleton 1).insert 0
  let G := finiteEntity C E hE
  have hc : (model.inner (.rel et)).map h F = G := by
    apply weak_eq_of_current (hr h) (rigid_weak (finite_rigid C E hE))
    rintro ⟨a, au⟩
    cases au
    rw [prof_map, Category.comp_id]
    change prof F h (a, PUnit.unit) ↔ prof (finiteEntity C E hE) (𝟙 C) (a, PUnit.unit)
    rw [prof_finite]
    change prof F h (a, PUnit.unit) ↔ ∃ x ∈ E, x = a
    constructor
    · intro ha
      obtain ⟨j, hj, ⟨x, xu⟩, hx, hxa⟩ := weak_below_hull F hw hK ha
      have hval : FunCat.fn j x = a := congrArg Prod.fst hxa
      have hcol : colored C a := by
        rcases hu x hx with hxc | hxK
        · rw [← hval]; exact j.2.2.2 x hxc
        · have hv : FunCat.fn j x = 0 := (hj x hxK).symm.trans (hh x hxK)
          rw [← hval, hv]; decide
      have hm : a ∈ E := by change a = 0 ∨ a = 1; change a < 2 at hcol; omega
      exact ⟨a, hm, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      apply coloured_lower_at hw hl h
      change x = 0 ∨ x = 1 at hx
      change x < 2
      omega
  have hone : prof F (h ≫ merge) (1, PUnit.unit) :=
    coloured_lower_at hw hl (h ≫ merge) (by decide)
  have hgone : prof G merge (1, PUnit.unit) := by
    rw [← hc, prof_map]
    exact hone
  obtain ⟨x, hx, hxe⟩ := (prof_finite E hE merge _).1 hgone
  change x = 0 ∨ x = 1 at hx
  rcases hx with rfl | rfl <;> cases hxe

/-- Every rigid unary relation at every object has finite or universal
current extension. This theorem uses the actual collapse, not a presumed
classification of the model's domain. -/
theorem rigid_extension {W : cat.Ob} (F : RD W et) (hr : RigidData F) :
    (extension F).Finite ∨ extension F = Set.univ := by
  classical
  by_cases hfin : (extension F).Finite
  · exact Or.inl hfin
  right
  by_contra htop
  obtain ⟨S, hS, hp⟩ := fin_pin (.rel et) W F
  have hw := rigid_weak hr
  have hcover : ∀ x ∈ extension F, x ∈ S ∨ colored W x := by
    intro x hx
    by_cases hs : x ∈ S
    · exact Or.inl hs
    right
    by_contra hc
    exact htop (fresh_uncoloured_forces_top F hw hS hp hx hs hc)
  cases W with
  | A =>
      exact hfin (hS.subset (fun x hx => (hcover x hx).elim id False.elim))
  | C =>
      have hsub : extension F ⊆ S ∪ ({0, 1} : Set Nat) := by
        intro x hx
        rcases hcover x hx with hs | hc
        · exact Or.inl hs
        · right; change x = 0 ∨ x = 1; change x < 2 at hc; omega
      exact hfin ((hS.union ((Set.finite_singleton 1).insert 0)).subset hsub)
  | B =>
      obtain ⟨x, hx, hxs⟩ := exists_outside hfin hS
      have hxc : colored B x := (hcover x hx).resolve_left hxs
      have hl : ∀ y, colored B y → y ∈ extension F := by
        intro y hy
        obtain ⟨j, hj, hjx⟩ := hit_avoiding (𝟙 B) hS hxs (fun _ => hy)
        have hm := hw.1 (x, PUnit.unit) hx j
        change prof F j (FunCat.fn j x, PUnit.unit) at hm
        rw [hjx] at hm
        exact (prof_agree hp hj _).1 hm
      exact no_coloured_exception hr hS hl (fun y hy => (hcover y hy).symm)

theorem rigid_unary_exact {W : cat.Ob} (F : RD W et) (hr : RigidData F) : ExactImage F := by
  rcases rigid_extension F hr with hfin | htop
  · have he : F = finiteEntity W (extension F) hfin := by
      apply weak_eq_of_current (rigid_weak hr) (rigid_weak (finite_rigid W _ hfin))
      rintro ⟨x, xu⟩
      cases xu
      change x ∈ extension F ↔ x ∈ extension (finiteEntity W (extension F) hfin)
      rw [extension_finite]
    rw [he]
    exact finite_exact _ _ _
  · have he : F = topEntity W := by
      apply weak_eq_of_current (rigid_weak hr) (rigid_weak (top_rigid W))
      rintro ⟨x, xu⟩
      cases xu
      constructor
      · intro _; exact prof_top _ _
      · intro _; change x ∈ extension F; rw [htop]; trivial
    rw [he]
    exact top_exact W

end
end Classicism.Meta.Intensional.ColourCollapse
