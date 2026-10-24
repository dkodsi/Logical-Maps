import Classicism.Models.ColourCollapseRigidity

/-!
# The coloured unary relation at B is weakly rigid and not rigid

Original formalization (misc), 22 October 2026. Source: colour-collapse-
entrance.md section 4 (unpaginated). Admission, finite interpolation, and
the explicit merge at C are proved for the concrete category.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

abbrev et : RTy := .arr .e .t

def colourRaw (W : cat.Ob) : Intension model.inner et W :=
  fun p => colored p.1 p.2.1.1

theorem colour_mem (W : cat.Ob) : colourRaw W ∈ Set.range (model.incl et W) := by
  apply (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) et W (colourRaw W)).2
  exact ⟨⟨∅, Set.finite_empty, fun _ _ _ _ => rfl⟩,
    fun V a k g hg ha => (hg.2 a.1).2 ha⟩

def colour (W : cat.Ob) : RD W et := Classical.choose (colour_mem W)

theorem incl_colour (W : cat.Ob) : model.incl et W (colour W) = colourRaw W :=
  Classical.choose_spec (colour_mem W)

@[simp] theorem prof_colour {W V : cat.Ob} (h : W ⟶ V) (a : TA et V) :
    prof (colour W) h a ↔ colored V a.1 := by
  unfold prof
  rw [incl_colour]
  rfl

theorem colour_weak : WeakData (colour B) := by
  classical
  constructor
  · intro a ha V h
    apply (prof_colour h _).2
    exact h.2.2.2 a.1 ((prof_colour (𝟙 B) a).1 ha)
  · intro Z hZ
    obtain ⟨N, hN, hpZ⟩ := fin_pin (.rel et) B Z
    rintro ⟨V, ⟨a, au⟩, h⟩ ha
    cases au
    have hac : colored V a := (prof_colour h _).1 ha
    obtain ⟨b, hb⟩ := hN.bddAbove
    let x := 2 * (b + 1)
    have hx : x ∉ N := fun hn => by have := hb hn; dsimp [x] at *; omega
    have hxc : colored B x := by dsimp [colored, x]; omega
    let q : Nat → Nat := fun n => if n = x then a else FunCat.fn h n
    have hqc : ∀ n ∈ N ∪ {x}, colored B n → colored V (q n) := by
      intro n _ hn
      by_cases he : n = x
      · subst n; simpa [q] using hac
      · simpa [q, he] using h.2.2.2 n hn
    obtain ⟨j, hj⟩ := extend_finite h.2.1 (hN.union (Set.finite_singleton x)) q hqc
    have hjx : FunCat.fn j x = a := by
      rw [hj x (Or.inr (Set.mem_singleton x))]
      simp [q] <;> rfl
    have hag : AgreeOn cat.De N j h := by
      intro n hn
      change FunCat.fn j n = FunCat.fn h n
      rw [hj n (Or.inl hn)]
      have he : n ≠ x := fun he => hx (he ▸ hn)
      simp [q, he]
    have hZj := hZ (x, PUnit.unit) ((prof_colour (𝟙 B) _).2 hxc) j
    change prof Z j (FunCat.fn j x, PUnit.unit) at hZj
    rw [hjx] at hZj
    exact (prof_agree hpZ hag (a, PUnit.unit)).1 hZj

def pairRaw : Intension model.inner et C :=
  fun p => p.2.1.1 = FunCat.fn p.2.2 0 ∨ p.2.1.1 = FunCat.fn p.2.2 1

theorem pair_mem : pairRaw ∈ Set.range (model.incl et C) := by
  apply (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) et C pairRaw).2
  refine ⟨⟨{0, 1}, (Set.finite_singleton 1).insert 0, ?_⟩, ?_⟩
  · intro V h i ha
    ext ⟨U, a, k⟩
    change (a.1 = FunCat.fn k (FunCat.fn h 0) ∨ a.1 = FunCat.fn k (FunCat.fn h 1)) ↔
      (a.1 = FunCat.fn k (FunCat.fn i 0) ∨ a.1 = FunCat.fn k (FunCat.fn i 1))
    have h0 : FunCat.fn h 0 = FunCat.fn i 0 := ha 0 (by simp)
    have h1 : FunCat.fn h 1 = FunCat.fn i 1 := ha 1 (by simp)
    constructor
    · exact fun hh => hh.imp (fun e => e.trans (congrArg (FunCat.fn k) h0))
        (fun e => e.trans (congrArg (FunCat.fn k) h1))
    · exact fun hh => hh.imp (fun e => e.trans (congrArg (FunCat.fn k) h0.symm))
        (fun e => e.trans (congrArg (FunCat.fn k) h1.symm))
  · intro V a k g _ ha
    exact ha.imp (congrArg (FunCat.fn g)) (congrArg (FunCat.fn g))

def pairEntity : RD C et := Classical.choose pair_mem

theorem incl_pair : model.incl et C pairEntity = pairRaw := Classical.choose_spec pair_mem

theorem prof_pair {V : cat.Ob} (h : C ⟶ V) (a : TA et V) :
    prof pairEntity h a ↔ a.1 = FunCat.fn h 0 ∨ a.1 = FunCat.fn h 1 := by
  unfold prof
  rw [incl_pair]
  rfl

theorem colour_not_rigid : ¬ RigidData (colour B) := by
  intro hr
  have hc := hr collapse
  have htest : ∀ a : TA et C,
      prof ((model.inner (.rel et)).map collapse (colour B)) (𝟙 C) a →
      ∀ {V : cat.Ob} (j : C ⟶ V), prof pairEntity j (Args.map model.inner et j a) := by
    intro a ha V j
    let n : Nat := a.1
    have hn : n < 2 := by
      have hcol : colored C a.1 := (prof_colour (collapse ≫ 𝟙 C) a).1 ((prof_map _ _ _ _).1 ha)
      exact hcol
    apply (prof_pair j _).2
    change FunCat.fn j n = FunCat.fn j 0 ∨ FunCat.fn j n = FunCat.fn j 1
    have he : n = 0 ∨ n = 1 := by omega
    exact he.imp (congrArg (FunCat.fn j)) (congrArg (FunCat.fn j))
  have hub := hc.2 pairEntity htest
  have hmem : prof ((model.inner (.rel et)).map collapse (colour B)) merge ((1 : Nat), PUnit.unit) := by
    rw [prof_map, prof_colour]
    change (1 : Nat) < 2
    decide
  have hbad : prof pairEntity merge ((1 : Nat), PUnit.unit) := hub hmem
  have he := (prof_pair merge _).1 hbad
  rcases he with he | he <;> cases he

end
end Classicism.Meta.Intensional.ColourCollapse
