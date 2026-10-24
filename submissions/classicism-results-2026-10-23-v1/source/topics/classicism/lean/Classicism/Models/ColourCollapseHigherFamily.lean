import Classicism.Models.ColourCollapseUnary

/-!
# A rigid family whose unary labels disappear at C

Original formalization (misc), 23 October 2026. Direct source:
research/2026-10-23/colour-collapse-higher-power.md, sections 3–4
(unpaginated). The new profiles are admitted in the existing concrete model.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

abbrev ett : RTy := .arr (.rel et) .t

theorem no_arrow_BA (h : B ⟶ A) : False := by
  have hh := h.2.1
  change 1 ≤ 0 at hh
  omega

theorem target_from_C {V : cat.Ob} (h : C ⟶ V) : V = C := by
  have hh := h.2.1
  cases V with
  | A => change 2 ≤ 0 at hh; omega
  | B => change 2 ≤ 1 at hh; omega
  | C => rfl

theorem top_transport {W V : cat.Ob} (h : W ⟶ V) :
    (model.inner (.rel et)).map h (topEntity W) = topEntity V := by
  apply model.Incl_injective (.rel et) V
  change model.incl et V ((model.inner (.rel et)).map h (topEntity W)) =
    model.incl et V (topEntity V)
  rw [model.incl_map, incl_top, incl_top]
  rfl

def labelRaw (n : Nat) : Intension model.inner et B :=
  fun p => p.1 = B → p.2.1.1 = FunCat.fn p.2.2 n

theorem label_mem (n : Nat) : labelRaw n ∈ Set.range (model.incl et B) := by
  apply (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) et B (labelRaw n)).2
  refine ⟨⟨{n}, Set.finite_singleton n, ?_⟩, ?_⟩
  · intro V h i ha
    ext ⟨U, a, k⟩
    change (U = B → a.1 = FunCat.fn k (FunCat.fn h n)) ↔
      (U = B → a.1 = FunCat.fn k (FunCat.fn i n))
    have he : FunCat.fn h n = FunCat.fn i n := ha n (Set.mem_singleton n)
    constructor
    · exact fun hp hu => (hp hu).trans (congrArg (FunCat.fn k) he)
    · exact fun hp hu => (hp hu).trans (congrArg (FunCat.fn k) he.symm)
  · intro V a k g _ ha
    change (V = B → a.1 = FunCat.fn k n) at ha
    change V = B → FunCat.fn g a.1 = FunCat.fn g (FunCat.fn k n)
    exact fun hv => congrArg (FunCat.fn g) (ha hv)

def label (n : Nat) : RD B et := Classical.choose (label_mem n)

theorem incl_label (n : Nat) : model.incl et B (label n) = labelRaw n :=
  Classical.choose_spec (label_mem n)

theorem prof_label {V : cat.Ob} (n : Nat) (h : B ⟶ V) (a : TA et V) :
    prof (label n) h a ↔ (V = B → a.1 = FunCat.fn h n) := by
  unfold prof
  rw [incl_label]
  rfl

theorem label_map_B (h : B ⟶ B) (n : Nat) :
    (model.inner (.rel et)).map h (label n) = label (FunCat.fn h n) := by
  apply model.Incl_injective (.rel et) B
  ext ⟨V, a, k⟩
  change prof ((model.inner (.rel et)).map h (label n)) k a ↔
    prof (label (FunCat.fn h n)) k a
  rw [prof_map, prof_label, prof_label]
  rfl

theorem label_map_C (h : B ⟶ C) (n : Nat) :
    (model.inner (.rel et)).map h (label n) = topEntity C := by
  apply model.Incl_injective (.rel et) C
  ext ⟨V, a, k⟩
  have hv := target_from_C k
  subst V
  change prof ((model.inner (.rel et)).map h (label n)) k a ↔
    prof (topEntity C) k a
  rw [prof_map, prof_label]
  constructor
  · intro _; exact prof_top _ _
  · intro _ hc; cases hc

theorem label_injective : Function.Injective label := by
  intro n m he
  have hn : prof (label n) (𝟙 B) ((n : Nat), PUnit.unit) :=
    (prof_label n (𝟙 B) _).2 (fun _ => rfl)
  rw [he] at hn
  exact (prof_label m (𝟙 B) _).1 hn rfl

def labelsExt : (V : cat.Ob) → Set (RD V et)
  | .A => ∅
  | .B => {X | ∃ n, colored B n ∧ X = label n}
  | .C => {X | X = topEntity C}

def labelsRaw : Intension model.inner ett B :=
  fun p => labelsExt p.1 p.2.1.1

theorem labels_mem : labelsRaw ∈ Set.range (model.incl ett B) := by
  apply (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) ett B labelsRaw).2
  refine ⟨⟨∅, Set.finite_empty, fun _ _ _ _ => rfl⟩, ?_⟩
  intro V a k g _ ha
  cases V with
  | A => exact ha.elim
  | B =>
      obtain ⟨n, hn, he⟩ := ha
      change ∃ m, colored B m ∧ (model.inner (.rel et)).map g a.1 = label m
      rw [he]
      exact ⟨FunCat.fn g n, g.2.2.2 n hn, label_map_B g n⟩
  | C =>
      change a.1 = topEntity C at ha
      change (model.inner (.rel et)).map g a.1 = topEntity C
      rw [ha]
      exact top_transport g

def labels : RD B ett := Classical.choose labels_mem

theorem incl_labels : model.incl ett B labels = labelsRaw :=
  Classical.choose_spec labels_mem

theorem prof_labels {V : cat.Ob} (h : B ⟶ V) (a : TA ett V) :
    prof labels h a ↔ labelsExt V a.1 := by
  unfold prof
  rw [incl_labels]
  rfl

theorem labels_map_B (h : B ⟶ B) :
    (model.inner (.rel ett)).map h labels = labels := by
  apply model.Incl_injective (.rel ett) B
  change model.incl ett B ((model.inner (.rel ett)).map h labels) =
    model.incl ett B labels
  rw [model.incl_map, incl_labels]
  rfl

theorem labels_C_exact (h : B ⟶ C) :
    ExactImage ((model.inner (.rel ett)).map h labels) := by
  intro V k a
  have hv := target_from_C k
  subst V
  obtain ⟨X, xu⟩ := a
  cases xu
  rw [prof_map, prof_labels]
  change X = topEntity C ↔ ∃ b : TA ett C,
    prof ((model.inner (.rel ett)).map h labels) (𝟙 C) b ∧
      Args.map model.inner ett k b = (X, PUnit.unit)
  constructor
  · intro hx
    subst X
    refine ⟨(topEntity C, PUnit.unit), ?_, Prod.ext (top_transport k) rfl⟩
    rw [prof_map, prof_labels]
    rfl
  · rintro ⟨⟨Y, yu⟩, hy, he⟩
    have hy' : Y = topEntity C := (prof_labels (h ≫ 𝟙 C) _).1
      ((prof_map labels h (𝟙 C) _).1 hy)
    have he' : (model.inner (.rel et)).map k Y = X := congrArg Prod.fst he
    rw [hy', top_transport] at he'
    exact he'.symm

theorem labels_weak : WeakData labels := by
  constructor
  · rintro ⟨X, xu⟩ hx V h
    cases xu
    obtain ⟨n, hn, rfl⟩ := (prof_labels (𝟙 B) _).1 hx
    apply (prof_labels h _).2
    cases V with
    | A => exact (no_arrow_BA h).elim
    | B => exact ⟨FunCat.fn h n, h.2.2.2 n hn, label_map_B h n⟩
    | C => exact label_map_C h n
  · intro Z hZ
    obtain ⟨N, hN, hpZ⟩ := fin_pin (.rel ett) B Z
    rintro ⟨V, ⟨X, xu⟩, h⟩ hx
    cases xu
    cases V with
    | A => exact (no_arrow_BA h).elim
    | B =>
        obtain ⟨n, hn, rfl⟩ := (prof_labels h _).1 hx
        obtain ⟨b, hb⟩ := hN.bddAbove
        let m := 2 * (b + 1)
        have hm : m ∉ N := fun hmem => by have := hb hmem; dsimp [m] at *; omega
        have hmc : colored B m := by dsimp [colored, m]; omega
        obtain ⟨j, hj, hjm⟩ := hit_avoiding h hN hm (fun _ => hn)
        have hZj := hZ (label m, PUnit.unit)
          ((prof_labels (𝟙 B) _).2 ⟨m, hmc, rfl⟩) j
        change prof Z j ((model.inner (.rel et)).map j (label m), PUnit.unit) at hZj
        rw [label_map_B, hjm] at hZj
        exact (prof_agree hpZ hj _).1 hZj
    | C =>
        have he : X = topEntity C := (prof_labels h _).1 hx
        subst X
        have hZ0 := hZ (label 0, PUnit.unit)
          ((prof_labels (𝟙 B) _).2 ⟨0, by change 0 % 2 = 0; decide, rfl⟩) h
        change prof Z h ((model.inner (.rel et)).map h (label 0), PUnit.unit) at hZ0
        rw [label_map_C] at hZ0
        exact hZ0

theorem labels_rigid : RigidData labels := by
  intro V h
  cases V with
  | A => exact (no_arrow_BA h).elim
  | B => rw [labels_map_B]; exact labels_weak
  | C => exact rigid_weak (exact_rigid _ (labels_C_exact h))

end
end Classicism.Meta.Intensional.ColourCollapse
