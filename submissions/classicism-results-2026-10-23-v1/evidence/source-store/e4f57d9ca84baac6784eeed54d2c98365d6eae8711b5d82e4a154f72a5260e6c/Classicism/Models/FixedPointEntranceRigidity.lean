import Classicism.Models.FixedPointEntranceModel
import Classicism.Certified.Schemas

/-!
# Full Tame Rigidity at the concrete fixed-point entrance

Original formalization (misc), 23 October 2026, of
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 2
(unpaginated). Unique root hom-sets make every exact-image hull externally
pinned by the empty set. Its symmetry is proved directly from tuple transport.
Weak rigidity forces equality with this admitted hull. Exact-image profiles
are necessarily weakly rigid, yielding the official Tame Rigidity schema.
No modelhood, rigidity, or admission verdict is assumed.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Rigidity

open CategoryTheory
noncomputable section

abbrev RD (W : cone.Ob) (ρ : RTy) := model.Dom W (.rel ρ)
abbrev TA (ρ : RTy) (W : cone.Ob) := Args model.inner ρ W

def prof {ρ : RTy} {W V : cone.Ob} (F : RD W ρ) (h : W ⟶ V) (a : TA ρ V) : Prop :=
  (⟨V, a, h⟩ : Tuple model.inner ρ W) ∈ model.incl ρ W F

@[simp] theorem prof_map {ρ : RTy} {W V U : cone.Ob} (F : RD W ρ) (h : W ⟶ V)
    (k : V ⟶ U) (a : TA ρ U) :
    prof ((model.inner (.rel ρ)).map h F) k a ↔ prof F (h ≫ k) a := by
  unfold prof
  rw [model.incl_map]
  rfl

def WeakData {ρ : RTy} {W : cone.Ob} (F : RD W ρ) : Prop :=
  (∀ a : TA ρ W, prof F (𝟙 W) a → ∀ {V : cone.Ob} (h : W ⟶ V),
    prof F h (Args.map model.inner ρ h a)) ∧
  (∀ Z : RD W ρ, (∀ a : TA ρ W, prof F (𝟙 W) a → ∀ {V : cone.Ob} (h : W ⟶ V),
    prof Z h (Args.map model.inner ρ h a)) → model.incl ρ W F ⊆ model.incl ρ W Z)

def RigidData {ρ : RTy} {W : cone.Ob} (F : RD W ρ) : Prop :=
  ∀ {V : cone.Ob} (h : W ⟶ V), WeakData ((model.inner (.rel ρ)).map h F)

def ExactImage {ρ : RTy} {W : cone.Ob} (F : RD W ρ) : Prop :=
  ∀ {V : cone.Ob} (h : W ⟶ V) (a : TA ρ V),
    prof F h a ↔ ∃ b : TA ρ W, prof F (𝟙 W) b ∧ Args.map model.inner ρ h b = a

/-- The relation whose profile is exactly the transported image of D. -/
def rootHull {ρ : RTy} (D : Set (TA ρ (A tail))) :
    Intension model.inner ρ (A tail) :=
  fun p => ∃ b, b ∈ D ∧ Args.map model.inner ρ p.2.2 b = p.2.1

theorem rootHull_mem {ρ : RTy} (D : Set (TA ρ (A tail))) :
    rootHull D ∈ Set.range (model.incl ρ (A tail)) := by
  apply (SymmetricExternal.mem_range_symIncl cone.De pointAction (syms tail)
    (PinIdeal.fin cone.De) ρ (A tail) (rootHull D)).2
  refine ⟨⟨∅, Set.finite_empty, ?_⟩, ?_⟩
  · intro V h i _
    have he : h = i := (root_hom_subsingleton tail V).elim h i
    subst i
    rfl
  · intro V a k g _
    rintro ⟨b, hb, he⟩
    exact ⟨b, hb, (Args.map_comp model.inner ρ k g b).trans
      (congrArg (Args.map model.inner ρ g) he)⟩

/-- No finite-factorization assumption is needed: every root exact-image
hull is actually in the constructed domain. -/
theorem weak_exact {ρ : RTy} (F : RD (A tail) ρ) (hw : WeakData F) :
    ExactImage F := by
  obtain ⟨Z, hZ⟩ := rootHull_mem (fun b => prof F (𝟙 (A tail)) b)
  have hsub : model.incl ρ (A tail) F ⊆ rootHull (fun b => prof F (𝟙 (A tail)) b) := by
    have hs := hw.2 Z (fun b hb V h => by
      unfold prof
      rw [hZ]
      exact ⟨b, hb, rfl⟩)
    rwa [hZ] at hs
  intro V h a
  constructor
  · intro ha
    exact hsub ha
  · rintro ⟨b, hb, rfl⟩
    exact hw.1 b hb h

theorem exact_rigid {ρ : RTy} {W : cone.Ob} (F : RD W ρ) (he : ExactImage F) : RigidData F := by
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

theorem weak_rigid_at_root {ρ : RTy} (F : RD (A tail) ρ) : WeakData F → RigidData F :=
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
  have hr : RigidData F := weak_rigid_at_root F hw
  constructor
  · intro V k a ha U j
    have ha' : prof ((model.inner (.rel ρ)).map k F) (𝟙 V) a :=
      (prof_map F k (𝟙 V) a).2 (by simpa only [prof, Category.comp_id] using ha)
    exact (prof_map F k j _).1 ((hr k).1 a ha' j)
  · intro V k Z hZ U j a ha
    have hz := (hr k).2 Z (fun b hb T l =>
      hZ b (by simpa only [prof, Category.comp_id] using
        (prof_map F k (𝟙 V) b).1 hb) T l)
    exact hz ((prof_map F k j a).2 ha)

/-- Every closed relational type instance of the official schema holds. -/
theorem holds_tame_schema : model.HoldsAx P.TameRigidity.schema := by
  rintro _ ⟨ρ, _, rfl⟩
  exact tame_at_root ρ

end
end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Rigidity
