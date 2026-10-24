import Classicism.Results.Research.RigidityClosureResearchNullary
import Classicism.Results.Research.Evaluator

/-! Direct sources: notes/rigidity-by-joins-and-boolean-closure.md §6 and
notes/maximalism-modal.md §22, original research, misc, unpaginated,
22 October 2026. Converse uniformization uses the displayed higher comprehension
instance through Plenitude. It is not derived from only ND and one lower instance. -/
namespace Classicism.Research.RigidityClosure
open Classicism.P Classicism.Paper

variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

def WeakNormalizer (R : τ → τ) : Prop := ∀ X, WeaklyRigid (R X) ∧ X ≡ R X
def RigidNormalizer (R : τ → τ) : Prop := ∀ X, Rigid (R X) ∧ X ≡ R X

def UniformWeakRigidComprehension (τ : Type) [Rel τ] : Prop :=
  ∃ R : τ → τ, ∀ X, WeaklyRigid (R X) ∧ X ≡ R X
def UniformRigidComprehension (τ : Type) [Rel τ] : Prop :=
  ∃ R : τ → τ, ∀ X, Rigid (R X) ∧ X ≡ R X

theorem uniform_weak_implies_comprehension : UniformWeakRigidComprehension τ →
    WeakRigidComprehension τ := fun h => h.elim fun R hr X => ⟨R X, hr X⟩
theorem uniform_rigid_implies_comprehension : UniformRigidComprehension τ →
    RigidComprehension τ := fun h => h.elim fun R hr X => ⟨R X, hr X⟩
theorem uniform_rigid_implies_uniform_weak : UniformRigidComprehension τ →
    UniformWeakRigidComprehension τ := fun h => h.elim fun R hr =>
      ⟨R, fun X => ⟨weaklyRigid_of_rigid (hr X).1, (hr X).2⟩⟩

theorem coext_common_source (X Y Z : τ) (hy : X ≡ Y) (hz : X ≡ Z) : Y ≡ Z :=
  coext_of_incl Y Z
    (incl_trans Y X Z (incl_of_coext' X Y hy) (incl_of_coext X Z hz))
    (incl_trans Z X Y (incl_of_coext' X Z hz) (incl_of_coext X Y hy))

theorem weak_comprehension_plenitude_uniform : WeakRigidComprehension τ →
    Plenitude τ τ → UniformWeakRigidComprehension τ := by
  intro rc pl
  exact pl (fun X Y => WeaklyRigid Y ∧ X ≡ Y) (fun X => (rc X).elim fun Y hy =>
    ⟨Y, hy, fun Z hz => Proofs.eq_of_weaklyRigid_coext hy.1 hz.1
      (coext_common_source X Y Z hy.2 hz.2)⟩)

theorem rigid_comprehension_plenitude_uniform : RigidComprehension τ →
    Plenitude τ τ → UniformRigidComprehension τ := by
  intro rc pl
  exact pl (fun X Y => Rigid Y ∧ X ≡ Y) (fun X => (rc X).elim fun Y hy =>
    ⟨Y, hy, fun Z hz => Proofs.eq_of_weaklyRigid_coext
      (weaklyRigid_of_rigid hy.1) (weaklyRigid_of_rigid hz.1)
      (coext_common_source X Y Z hy.2 hz.2)⟩)

theorem nd_weak_comprehension_uniform {σ : Type} [Ty σ] :
    NecessityOfDistinctness Prop → WeakRigidComprehension (σ → Prop) →
    WeakRigidComprehension ((σ → Prop) → (σ → Prop) → Prop) →
    UniformWeakRigidComprehension (σ → Prop) := fun nd rc high =>
  weak_comprehension_plenitude_uniform rc
    (Proofs.weak_rigid_comprehension_and_nd_imply_plenitude high (Proofs.nd_of_nd_t nd))

theorem nd_rigid_comprehension_uniform {σ : Type} [Ty σ] :
    NecessityOfDistinctness Prop → RigidComprehension (σ → Prop) →
    RigidComprehension ((σ → Prop) → (σ → Prop) → Prop) →
    UniformRigidComprehension (σ → Prop) := fun nd rc high =>
  rigid_comprehension_plenitude_uniform rc
    (Proofs.weak_rigid_comprehension_and_nd_imply_plenitude
      (Proofs.rigid_comprehension_r_implies_weak_rigid_comprehension_r high)
      (Proofs.nd_of_nd_t nd))

/-- The direct Boolean-evaluation argument works for identity at every type. -/
theorem evaluator_identity_obstruction {σ : Type} [Ty σ]
    (E : Prop → Prop) (a b : σ) : E (a = b) = False → E True = True → a ≠ b :=
  fun hf ht he => Eq.mpr
    (hf.symm.trans ((congrArg E (necessity_of_identity a b he)).trans ht)) trivial

theorem actualEvaluator_implies_nd {σ : Type} [Ty σ]
    (E : Prop → Prop) (he : Classicism.Research.ActualEvaluator E) : NecessityOfDistinctness σ :=
  fun a b hn => modal_K _ _ (modal_K _ _ (nec% (evaluator_identity_obstruction E a b))
    (necessity_of_identity _ _ ((he (a = b)).2 hn)))
    (necessity_of_identity _ _ ((he True).1 trivial))

theorem uniform_weak_t_actual_evaluator : UniformWeakRigidComprehension Prop →
    ∃ E : Prop → Prop, Classicism.Research.ActualEvaluator E :=
  fun h => h.elim fun R hr => ⟨R, fun p =>
    ⟨fun hp => (hr p).1.1 ((hr p).2.mp hp),
     fun hn => ((weaklyRigid_prop_iff (R p)).1 (hr p).1).elim
       (fun ht => False.elim (hn ((hr p).2.mpr (box_elim ht)))) id⟩⟩

theorem uniform_weak_t_implies_nd {σ : Type} [Ty σ] :
    UniformWeakRigidComprehension Prop → NecessityOfDistinctness σ :=
  fun h => (uniform_weak_t_actual_evaluator h).elim fun E he => actualEvaluator_implies_nd E he

theorem uniform_rigid_t_implies_nd {σ : Type} [Ty σ] :
    UniformRigidComprehension Prop → NecessityOfDistinctness σ :=
  fun h => uniform_weak_t_implies_nd (uniform_rigid_implies_uniform_weak h)

/-- For a single nonnullary instance the exact current witness is explicit. -/
theorem uniform_weak_actual_evaluator_at {σ : Type} [Ty σ] (a : σ)
    (h : UniformWeakRigidComprehension (σ → Prop)) :
    ∃ E : Prop → Prop, Classicism.Research.ActualEvaluator E := by
  obtain ⟨R, hr⟩ := h
  refine ⟨fun p => R (fun _ => p) a, fun p => ⟨?_, ?_⟩⟩
  · intro hp
    exact (hr (fun _ => p)).1.1 a (((hr (fun _ => p)).2 a).mp hp)
  · intro hn
    have hb : R (fun _ => p) = (fun _ => False) :=
      Proofs.eq_of_weaklyRigid_coext (hr (fun _ => p)).1 weak_bottom
        (fun x => ⟨fun hx => hn (((hr (fun _ => p)).2 x).mpr hx), fun hx => False.elim hx⟩)
    exact congrFun hb a

theorem uniform_weak_implies_nd {σ : Type} [Ty σ] : Existence σ →
    UniformWeakRigidComprehension (σ → Prop) → NecessityOfDistinctness Prop :=
  fun he h => he.elim fun a _ => (uniform_weak_actual_evaluator_at a h).elim
    fun E hE => actualEvaluator_implies_nd E hE

theorem uniform_weak_implies_actuality {σ : Type} [Ty σ] : Existence σ →
    UniformWeakRigidComprehension (σ → Prop) → Actuality :=
  fun he h => he.elim fun a _ => (uniform_weak_actual_evaluator_at a h).elim fun E hE =>
    Classicism.Research.positiveEvaluator_actuality
      ⟨E, Classicism.Research.actualEvaluator_positive E hE⟩

end Classicism.Research.RigidityClosure
