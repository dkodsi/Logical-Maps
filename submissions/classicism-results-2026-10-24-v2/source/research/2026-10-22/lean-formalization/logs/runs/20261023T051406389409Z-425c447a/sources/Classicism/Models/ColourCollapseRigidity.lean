import Classicism.Models.ColourCollapseBase

/-!
# Finite pinning, exact-image profiles, and entrance Tame Rigidity

Original proofs (misc), 22 October 2026. Source:
notes/colour-collapse-entrance.md section 3, and the finite-pinning criterion
in arguments/tame-rigidity-factorizable.yaml. The concrete root factorization
used here is proved in ColourCollapseBase, not assumed as a model interface.
-/

namespace Classicism.Meta.Intensional.ColourCollapse

open CategoryTheory
noncomputable section

abbrev RD (W : cat.Ob) (ρ : RTy) := model.Dom W (.rel ρ)
abbrev TA (ρ : RTy) (W : cat.Ob) := Args model.inner ρ W

def prof {ρ : RTy} {W V : cat.Ob} (F : RD W ρ) (h : W ⟶ V) (a : TA ρ V) : Prop :=
  (⟨V, a, h⟩ : Tuple model.inner ρ W) ∈ model.incl ρ W F

@[simp] theorem prof_map {ρ : RTy} {W V U : cat.Ob} (F : RD W ρ) (h : W ⟶ V)
    (k : V ⟶ U) (a : TA ρ U) :
    prof ((model.inner (.rel ρ)).map h F) k a ↔ prof F (h ≫ k) a := by
  unfold prof
  rw [model.incl_map]
  rfl

theorem fin_pin (σ : Ty) (W : cat.Ob) (x : model.Dom W σ) :
    ∃ S : Set Nat, S.Finite ∧ model.PinnedO σ (W := W) S (model.Incl σ W x) :=
  symIdeal_inner_finPinned (De := cat.De) (G := syms) (J := PinIdeal.fin cat.De)
    (W₀ := A) (nonempty_e := (base A).ne) (I := model.I) σ W x

theorem tuple_pin : ∀ (ρ : RTy) (W : cat.Ob) (a : TA ρ W),
    ∃ S : Set Nat, S.Finite ∧ ∀ V (h i : W ⟶ V), AgreeOn cat.De S h i →
      Args.map model.inner ρ h a = Args.map model.inner ρ i a
  | .t, W, a => ⟨∅, Set.finite_empty, fun _ _ _ _ => rfl⟩
  | .arr σ ρ, W, a => by
    obtain ⟨S, hS, hpS⟩ := fin_pin σ W a.1
    obtain ⟨T, hT, hpT⟩ := tuple_pin ρ W a.2
    refine ⟨S ∪ T, hS.union hT, fun V h i ha => ?_⟩
    change ((model.inner σ).map h a.1, Args.map model.inner ρ h a.2) =
      ((model.inner σ).map i a.1, Args.map model.inner ρ i a.2)
    exact Prod.ext ((model.pinnedO_Incl_iff σ (W := W) S a.1).1 hpS V h i (ha.mono cat.De Set.subset_union_left))
      (hpT V h i (ha.mono cat.De Set.subset_union_right))

theorem prof_agree {ρ : RTy} {W V : cat.Ob} {F : RD W ρ} {S : Set Nat}
    (hp : model.PinnedO (.rel ρ) (W := W) S (model.incl ρ W F))
    {h i : W ⟶ V} (ha : AgreeOn cat.De S h i) (a : TA ρ V) :
    prof F h a ↔ prof F i a := by
  have he := congrArg (fun R : Intension model.inner ρ V =>
    (⟨V, a, 𝟙 V⟩ : Tuple model.inner ρ V) ∈ R) (hp V h i ha)
  simpa only [Outer.map_rel, Intension.mem_map, Category.comp_id] using Iff.of_eq he

def WeakData {ρ : RTy} {W : cat.Ob} (F : RD W ρ) : Prop :=
  (∀ a : TA ρ W, prof F (𝟙 W) a → ∀ {V : cat.Ob} (h : W ⟶ V),
    prof F h (Args.map model.inner ρ h a)) ∧
  (∀ Z : RD W ρ, (∀ a : TA ρ W, prof F (𝟙 W) a → ∀ {V : cat.Ob} (h : W ⟶ V),
    prof Z h (Args.map model.inner ρ h a)) → model.incl ρ W F ⊆ model.incl ρ W Z)

def RigidData {ρ : RTy} {W : cat.Ob} (F : RD W ρ) : Prop :=
  ∀ {V : cat.Ob} (h : W ⟶ V), WeakData ((model.inner (.rel ρ)).map h F)

def ExactImage {ρ : RTy} {W : cat.Ob} (F : RD W ρ) : Prop :=
  ∀ {V : cat.Ob} (h : W ⟶ V) (a : TA ρ V),
    prof F h a ↔ ∃ b : TA ρ W, prof F (𝟙 W) b ∧ Args.map model.inner ρ h b = a

def hull {ρ : RTy} {W : cat.Ob} (N : Set Nat) (D : Set (TA ρ W)) : Intension model.inner ρ W :=
  fun p => ∃ j : W ⟶ p.1, AgreeOn cat.De N p.2.2 j ∧
    ∃ a, a ∈ D ∧ Args.map model.inner ρ j a = p.2.1

theorem hull_mem {ρ : RTy} {W : cat.Ob} {N : Set Nat} (hN : N.Finite) (D : Set (TA ρ W)) :
    hull N D ∈ Set.range (model.incl ρ W) := by
  apply (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) ρ W (hull N D)).2
  refine ⟨⟨N, hN, ?_⟩, ?_⟩
  · intro V h i ha
    ext ⟨U, a, k⟩
    constructor
    · rintro ⟨j, hj, b, hb, he⟩
      exact ⟨j, ((ha.comp_right cat.De k).symm cat.De).trans cat.De hj, b, hb, he⟩
    · rintro ⟨j, hj, b, hb, he⟩
      exact ⟨j, (ha.comp_right cat.De k).trans cat.De hj, b, hb, he⟩
  · intro V a k g _
    rintro ⟨j, hj, b, hb, he⟩
    exact ⟨j ≫ g, hj.comp_right cat.De g, b, hb,
      (Args.map_comp model.inner ρ j g b).trans (congrArg (Args.map model.inner ρ g) he)⟩

theorem weak_below_hull {ρ : RTy} {W : cat.Ob} (F : RD W ρ) (hw : WeakData F)
    {N : Set Nat} (hN : N.Finite) :
    model.incl ρ W F ⊆ hull N (fun a => prof F (𝟙 W) a) := by
  obtain ⟨Z, hZ⟩ := hull_mem hN (fun a => prof F (𝟙 W) a)
  have h := hw.2 Z (fun a ha V j => by
    unfold prof
    rw [hZ]
    exact ⟨j, AgreeOn.refl cat.De N j, a, ha, rfl⟩)
  rwa [hZ] at h

/-- Full weak rigidity at A implies an exact-image profile at every outgoing
arrow, through actual finite pinning and the explicit root factorization. -/
theorem weak_exact {ρ : RTy} (F : RD A ρ) (hw : WeakData F) : ExactImage F := by
  obtain ⟨S, hS, hp⟩ := fin_pin (.rel ρ) A F
  intro V h a
  constructor
  · intro ha
    obtain ⟨h', hag, b, hb, hba⟩ := weak_below_hull F hw hS ha
    obtain ⟨M, hM, hpM⟩ := tuple_pin ρ A b
    obtain ⟨u, hfix, hfactor⟩ := root_factor h h' hS hM hag
    have hcurrent : prof F (𝟙 A) (Args.map model.inner ρ u b) :=
      (prof_agree hp (h := u) (i := 𝟙 A) hfix _).1 (hw.1 b hb u)
    refine ⟨Args.map model.inner ρ u b, hcurrent, ?_⟩
    rw [← Args.map_comp, hpM V (u ≫ h) h' hfactor]
    exact hba
  · rintro ⟨b, hb, rfl⟩
    exact hw.1 b hb h

theorem exact_rigid {ρ : RTy} {W : cat.Ob} (F : RD W ρ) (he : ExactImage F) : RigidData F := by
  intro V k
  constructor
  · intro a ha U j
    have hFa : prof F k a := by simpa using ha
    obtain ⟨b, hb, hba⟩ := (he k a).1 hFa
    apply (prof_map F k j _).2
    apply (he (k ≫ j) _).2
    exact ⟨b, hb, by rw [Args.map_comp, hba]⟩
  · intro Z hZ
    rintro ⟨U, a, j⟩ ha
    have hFa : prof F (k ≫ j) a := (prof_map F k j a).1 ha
    obtain ⟨b, hb, hba⟩ := (he (k ≫ j) a).1 hFa
    have hbV : prof ((model.inner (.rel ρ)).map k F) (𝟙 V) (Args.map model.inner ρ k b) := by
      rw [prof_map, Category.comp_id]
      exact (he k _).2 ⟨b, hb, rfl⟩
    have hz := hZ (Args.map model.inner ρ k b) hbV j
    rw [← Args.map_comp, hba] at hz
    exact hz

theorem weak_rigid_at_root {ρ : RTy} (F : RD A ρ) : WeakData F → RigidData F :=
  fun hw => exact_rigid F (weak_exact F hw)

/-- The official full Tame Rigidity instance at A, at arbitrary relational
type. The semantic construction above is used to discharge both boxes. -/
theorem tame_at_root (ρ : RTy) : model.HoldsSentence (P.TameRigidity.quoted ρ) := by
  simp only [Premodel.HoldsSentence, P.TameRigidity.quoted,
    model.holds_forall isModel, model.holds_imp isModel, model.holds_conj isModel,
    model.holds_box isModel, Premodel.holds_inclR isModel, Premodel.sem_boxR isModel,
    Premodel.sem_var, IEnv.get, IEnv.get_map, model.incl_map, Intension.mem_map,
    Set.mem_ofPred_eq, Category.comp_id, Category.id_comp]
  intro F hF
  have hw : WeakData F := by
    constructor
    · simpa [prof] using hF.1
    · intro Z hZ
      rintro ⟨V, a, k⟩ ha
      exact hF.2 Z (by simpa [prof] using hZ) k a ha
  have hr := weak_rigid_at_root F hw
  constructor
  · intro V k a ha U j
    have hp := (hr k).1 a (by simpa [prof] using ha) j
    simpa [prof, Category.assoc] using hp
  · intro V k Z hZ U j a ha
    have hz := (hr k).2 Z (by simpa [prof, Category.assoc] using hZ)
      (show prof ((model.inner (.rel ρ)).map k F) j a from by simpa [prof] using ha)
    simpa [prof] using hz

end
end Classicism.Meta.Intensional.ColourCollapse
