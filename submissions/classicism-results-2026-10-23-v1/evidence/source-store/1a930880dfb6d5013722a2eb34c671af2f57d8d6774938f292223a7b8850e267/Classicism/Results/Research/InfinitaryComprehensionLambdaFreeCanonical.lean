import Classicism.Results.Research.InfinitaryComprehensionRepresentation

/-!
# The canonical domain maps from the actual lambda-free axioms

Source: the Infinitary Comprehension note, sections 3--4 (misc, original
research, 23 October 2026). These proofs use the actual infinitary syntax,
its closure and Comprehension, and the single boxed ND_t sentence below.
They do not assume `Premodel.IsModel`, finite C soundness, Barcan, or an
already constant-domain presentation. Ordinary classical metatheory only;
compilation is deliberately paused.

`Closed` and `Comprehension` in this reusable module range over the auxiliary
full type datatype. The separate `GroundedModel` construction obtains these
premises from original closed-type formation and Comprehension, while retaining
arbitrary unused ambient parameter symbols.
-/

namespace Classicism.Research.InfinitaryComprehension.Canonical

open Classicism.Meta Classicism.Meta.Intensional CategoryTheory Grounding

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C)

/-- The actual lambda-free matrix x ≠ y. -/
def neqMatrix (σ : Classicism.Meta.Ty) : ITerm (A.Dom A.W₀) [σ, σ] Ty.t :=
  .neg (.eq (.var (.succ .zero)) (.var .zero))

/-- No finite-library modality or lambda is hidden in this sentence. -/
def ndFormula (σ : Classicism.Meta.Ty) : ITerm (A.Dom A.W₀) [] Ty.t :=
  .all (.all (.imp ((Canonical.neqMatrix A) σ) ((Canonical.neqMatrix A) σ).box))

def LambdaFreeC5 : Prop :=
  Holds A (Canonical.selfAssignment A) (𝟙 A.W₀) ((Canonical.ndFormula A) Ty.t).box .nil

theorem neqMatrix_profile {σ : Classicism.Meta.Ty} {W V : C} (h : A.W₀ ⟶ W)
    (a b : A.Dom W σ) (k : W ⟶ V) :
    (⟨V, PUnit.unit, k⟩ : Tuple A.inner .t W) ∈
      sem A (Canonical.selfAssignment A) h ((Canonical.neqMatrix A) σ) (.cons b (.cons a .nil)) ↔
      (A.inner σ).map k a ≠ (A.inner σ).map k b := by
  change (Outer.map A.inner σ k (A.Incl σ W a) ≠
    Outer.map A.inner σ k (A.Incl σ W b)) ↔ _
  rw [← A.Incl_map, ← A.Incl_map]
  exact not_congr (A.Incl_injective σ V).eq_iff

theorem ndFormula_injective (hc : Closed A) {σ : Classicism.Meta.Ty} {W V : C}
    (h : A.W₀ ⟶ W) (hnd : Holds A (Canonical.selfAssignment A) h ((Canonical.ndFormula A) σ) .nil)
    (k : W ⟶ V) : Function.Injective ((A.inner σ).map k) := by
  classical
  intro a b hab
  by_contra hne
  have h₁ := ((Canonical.holds_all A) (Canonical.selfAssignment A) h _ .nil).1 hnd a
  have h₂ := ((Canonical.holds_all A) (Canonical.selfAssignment A) h _ (.cons a .nil)).1 h₁ b
  have hnow : Holds A (Canonical.selfAssignment A) h ((Canonical.neqMatrix A) σ) (.cons b (.cons a .nil)) := by
    have hn := ((Canonical.neqMatrix_profile A) h a b (𝟙 W)).2
      (by simpa only [Functor.map_id, types_id_apply] using hne)
    exact hn
  change (¬ Holds A (Canonical.selfAssignment A) h ((Canonical.neqMatrix A) σ) (.cons b (.cons a .nil)) ∨
    Holds A (Canonical.selfAssignment A) h ((Canonical.neqMatrix A) σ).box (.cons b (.cons a .nil))) at h₂
  have hn := ((Canonical.holds_box A) (Canonical.selfAssignment A) hc h _ _).1
    (h₂.resolve_left (fun hn => hn hnow)) ⟨V, PUnit.unit, k⟩
  exact ((Canonical.neqMatrix_profile A) h a b k).1 hn hab

/-- The actual boxed ND_t sentence gives proposition injectivity at every
reachable object, independently of a finite C model condition. -/
theorem lambdaFree_prop_injective (hc : Closed A) (hC5 : LambdaFreeC5 A)
    {W V : C} (h : A.W₀ ⟶ W) (k : W ⟶ V) :
    Function.Injective ((A.inner Ty.t).map k) := by
  have hb := ((Canonical.holds_box A) (Canonical.selfAssignment A) hc (𝟙 A.W₀) _ .nil).1 hC5
  have hn := (mem_sem_iff A (Canonical.selfAssignment A) (𝟙 A.W₀)
    ((Canonical.ndFormula A) Ty.t) .nil h).1 (hb ⟨W, PUnit.unit, h⟩)
  simp only [Category.id_comp, Premodel.push, IEnv.map] at hn
  exact (Canonical.ndFormula_injective A) hc h hn k

/-- An equality proposition becomes top when the two objects merge. Reflecting
that top value through the injective proposition action prevents any merge. -/
theorem lambdaFree_map_injective (hc : Closed A) (hC5 : LambdaFreeC5 A)
    (σ : Classicism.Meta.Ty) {W V : C} (h : A.W₀ ⟶ W) (k : W ⟶ V) :
    Function.Injective ((A.inner σ).map k) := by
  intro a b hab
  let e : ITerm (A.Dom A.W₀) [σ, σ] Ty.t :=
    .eq (.var (.succ .zero)) (.var .zero)
  obtain ⟨q, hq⟩ := hc (Canonical.selfAssignment A) h e (.cons b (.cons a .nil))
  obtain ⟨top, ht⟩ := hc (Canonical.selfAssignment A) h
    (.top : ITerm (A.Dom A.W₀) [] Ty.t) .nil
  change A.incl .t W q = sem A (Canonical.selfAssignment A) h e
    (.cons b (.cons a .nil)) at hq
  change A.incl .t W top =
    sem A (Canonical.selfAssignment A) h (.top : ITerm (A.Dom A.W₀) [] Ty.t) .nil at ht
  have hqt : (A.inner Ty.t).map k q = (A.inner Ty.t).map k top := by
    apply A.incl_injective .t V
    rw [A.incl_map, A.incl_map, hq, ht]
    ext ⟨U, ⟨⟩, j⟩
    change (Outer.map A.inner σ (k ≫ j) (A.Incl σ W a) =
      Outer.map A.inner σ (k ≫ j) (A.Incl σ W b)) ↔ True
    apply iff_true_intro
    rw [← A.Incl_map, ← A.Incl_map]
    apply congrArg (A.Incl σ U)
    simpa only [Functor.map_comp, types_comp_apply] using
      congrArg ((A.inner σ).map j) hab
  have he := (Canonical.lambdaFree_prop_injective A) hc hC5 h k hqt
  have hnow : (⟨W, PUnit.unit, 𝟙 W⟩ : Tuple A.inner .t W) ∈ A.incl .t W q := by
    rw [he, ht]
    exact Set.mem_univ _
  rw [hq] at hnow
  change Outer.map A.inner σ (𝟙 W) (A.Incl σ W a) =
    Outer.map A.inner σ (𝟙 W) (A.Incl σ W b) at hnow
  rw [Outer.map_id, Outer.map_id] at hnow
  exact A.Incl_injective σ W hnow

/-- The universal proposition for an admitted root relation. -/
def rootRangeAll {σ : Classicism.Meta.Ty} (R : A.Dom A.W₀ (σ ⇒ RTy.t)) :
    ITerm (A.Dom A.W₀) [] Ty.t := .all (.app (.param R) (.var .zero))

theorem rootRangeAll_profile {σ : Classicism.Meta.Ty} (R : A.Dom A.W₀ (σ ⇒ RTy.t))
    (w : Tuple A.inner .t A.W₀) :
    w ∈ sem A (Canonical.selfAssignment A) (𝟙 A.W₀) ((Canonical.rootRangeAll A) R) .nil ↔
      ∀ x : A.Dom w.1 σ,
        (⟨w.1, (x, PUnit.unit), w.2.2⟩ : Tuple A.inner (σ ⇒ RTy.t) A.W₀) ∈
          A.incl _ A.W₀ R := by
  rcases w with ⟨V, ⟨⟩, k⟩
  change (∀ x : A.Dom V σ, Intension.True A.inner
    (A.apply (A.Incl _ V ((A.inner _).map ((𝟙 A.W₀) ≫ k) R))
      (A.Incl σ V x))) ↔ _
  simp only [Category.id_comp, A.apply_Incl, Intension.True,
    Intension.app, Set.mem_setOf_eq, Functor.map_id, types_id_apply]
  change (∀ x : A.Dom V σ,
    (⟨V, (x, PUnit.unit), 𝟙 V⟩ : Tuple A.inner (σ ⇒ RTy.t) V) ∈
      A.incl (σ ⇒ RTy.t) V ((A.inner (σ ⇒ RTy.t)).map k R)) ↔ _
  simp only [A.incl_map, Intension.map, Set.mem_setOf_eq, Category.comp_id]

/-- A permanently missing root-range object makes the universal range
proposition permanently false. Proposition injectivity reflects this bottom
value back to the root, contradicting its actual truth. No BF is invoked. -/
theorem lambdaFree_root_map_surjective (hc : Closed A) (hcomp : Comprehension A)
    (hC5 : LambdaFreeC5 A) (σ : Classicism.Meta.Ty) {V : C} (h : A.W₀ ⟶ V) :
    Function.Surjective ((A.inner σ).map h) := by
  classical
  intro x
  by_contra hx
  obtain ⟨R, hR⟩ := (Canonical.named_range_witness A) hc hcomp σ
  let q := (Canonical.rootTerm A) hc ((Canonical.rootRangeAll A) R)
  have hq : A.incl .t A.W₀ q =
      sem A (Canonical.selfAssignment A) (𝟙 A.W₀) ((Canonical.rootRangeAll A) R) .nil := by
    exact (Canonical.rootTerm_spec A) hc (σ := Ty.t) ((Canonical.rootRangeAll A) R)
  have htrue : (⟨A.W₀, PUnit.unit, 𝟙 A.W₀⟩ : Tuple A.inner .t A.W₀) ∈
      A.incl .t A.W₀ q := by
    rw [hq, (Canonical.rootRangeAll_profile A)]
    intro a
    apply (hR A.W₀ (𝟙 A.W₀) a).2
    exact ⟨a, by simp only [Functor.map_id, types_id_apply]⟩
  have hbottom : (A.inner Ty.t).map h q = (A.inner Ty.t).map h ((Canonical.rootBot A) hc) := by
    apply A.incl_injective .t V
    rw [A.incl_map, A.incl_map, (Canonical.incl_rootBot A)]
    ext ⟨U, ⟨⟩, k⟩
    change (⟨U, PUnit.unit, h ≫ k⟩ : Tuple A.inner .t A.W₀) ∈
      A.incl .t A.W₀ q ↔ False
    apply iff_false_intro
    intro hu
    rw [hq, (Canonical.rootRangeAll_profile A)] at hu
    obtain ⟨a, ha⟩ := (hR U (h ≫ k) ((A.inner σ).map k x)).1 (hu ((A.inner σ).map k x))
    apply hx
    refine ⟨a, (Canonical.lambdaFree_map_injective A) hc hC5 σ h k ?_⟩
    simpa only [Functor.map_comp, types_comp_apply] using ha
  have he := (Canonical.lambdaFree_prop_injective A) hc hC5 (𝟙 A.W₀) h hbottom
  rw [he, (Canonical.incl_rootBot A)] at htrue
  exact htrue

/-- Both domain-map directions follow from actual lambda-free axioms. -/
theorem lambdaFree_root_map_bijective (hc : Closed A) (hcomp : Comprehension A)
    (hC5 : LambdaFreeC5 A) (σ : Classicism.Meta.Ty) {V : C} (h : A.W₀ ⟶ V) :
    Function.Bijective ((A.inner σ).map h) :=
  ⟨(Canonical.lambdaFree_map_injective A) hc hC5 σ (𝟙 A.W₀) h,
    (Canonical.lambdaFree_root_map_surjective A) hc hcomp hC5 σ h⟩

/-- These are conclusions of the actual lambda-free axioms, not extra
constant-domain assumptions. -/
theorem lambdaFree_rootInjective (hc : Closed A) (hC5 : LambdaFreeC5 A) :
    RootInjective A :=
  fun σ {_} h => (Canonical.lambdaFree_map_injective A) hc hC5 (groundTy σ) (𝟙 A.W₀) h

theorem lambdaFree_rootSurjective (hc : Closed A) (hcomp : Comprehension A)
    (hC5 : LambdaFreeC5 A) : RootSurjective A :=
  fun σ {_} h => (Canonical.lambdaFree_root_map_surjective A) hc hcomp hC5 (groundTy σ) h

/-- The canonical model constructed directly from the infinitary axioms. -/
noncomputable def lambdaFreeModel (hc : Closed A) (hC5 : LambdaFreeC5 A) : Henkin.Model :=
  (Canonical.modelOfMaps A) hc ((Canonical.lambdaFree_rootInjective A) hc hC5)

noncomputable def lambdaFreeRootWorld (hc : Closed A) (hC5 : LambdaFreeC5 A) :
    ((Canonical.lambdaFreeModel A) hc hC5).World :=
  (Canonical.rootWorldOfMaps A) hc ((Canonical.lambdaFree_rootInjective A) hc hC5)

theorem lambdaFreeModel_faithful (hc : Closed A) (hcomp : Comprehension A)
    (hC5 : LambdaFreeC5 A) : Henkin.Faithful ((Canonical.lambdaFreeModel A) hc hC5) :=
  (Canonical.modelOfMaps_faithful A) hc ((Canonical.lambdaFree_rootInjective A) hc hC5)
    ((Canonical.lambdaFree_rootSurjective A) hc hcomp hC5)

theorem lambdaFreeModel_worldSeparated (hc : Closed A) (hC5 : LambdaFreeC5 A) :
    Henkin.WorldSeparated ((Canonical.lambdaFreeModel A) hc hC5) :=
  (Canonical.modelOfMaps_worldSeparated A) hc ((Canonical.lambdaFree_rootInjective A) hc hC5)

theorem lambdaFreeModel_comp (hc : Closed A) (hcomp : Comprehension A)
    (hC5 : LambdaFreeC5 A) :
    Henkin.Comp ((Canonical.lambdaFreeModel A) hc hC5) ((Canonical.lambdaFreeRootWorld A) hc hC5) :=
  (Canonical.modelOfMaps_comp A) hc hcomp ((Canonical.lambdaFree_rootInjective A) hc hC5)
    ((Canonical.lambdaFree_rootSurjective A) hc hcomp hC5)

theorem lambdaFreeModel_full_profiles (hc : Closed A) (hcomp : Comprehension A)
    (hC5 : LambdaFreeC5 A) : Henkin.FullProfiles ((Canonical.lambdaFreeModel A) hc hC5) :=
  (Canonical.modelOfMaps_full_profiles A) hc hcomp ((Canonical.lambdaFree_rootInjective A) hc hC5)
    ((Canonical.lambdaFree_rootSurjective A) hc hcomp hC5)

theorem lambdaFreeModel_full_functions (hc : Closed A) (hcomp : Comprehension A)
    (hC5 : LambdaFreeC5 A) (σ : Classicism.Meta.Ty) (ρ : RTy)
    (f : ((Canonical.lambdaFreeModel A) hc hC5).Dom σ → ((Canonical.lambdaFreeModel A) hc hC5).Dom ρ) :
    ∃! R : ((Canonical.lambdaFreeModel A) hc hC5).Dom (σ ⇒ ρ),
      ∀ x, ((Canonical.lambdaFreeModel A) hc hC5).app R x = f x :=
  (Canonical.modelOfMaps_full_functions A) hc hcomp ((Canonical.lambdaFree_rootInjective A) hc hC5)
    ((Canonical.lambdaFree_rootSurjective A) hc hcomp hC5) σ ρ f

theorem lambdaFreeModel_full_propositions (hc : Closed A) (hcomp : Comprehension A)
    (hC5 : LambdaFreeC5 A) (U : ((Canonical.lambdaFreeModel A) hc hC5).World → Prop) :
    ∃! p : ((Canonical.lambdaFreeModel A) hc hC5).Dom Ty.t,
      ∀ w, ((Canonical.lambdaFreeModel A) hc hC5).truth p w ↔ U w :=
  (Canonical.modelOfMaps_full_propositions A) hc hcomp ((Canonical.lambdaFree_rootInjective A) hc hC5)
    ((Canonical.lambdaFree_rootSurjective A) hc hcomp hC5) U

#print axioms lambdaFree_root_map_bijective
#print axioms lambdaFreeModel_comp
#print axioms lambdaFreeModel_full_profiles
#print axioms lambdaFreeModel_full_functions
#print axioms lambdaFreeModel_full_propositions

end Classicism.Research.InfinitaryComprehension.Canonical
