import Classicism.Results.Research.Evaluator

/-!
# A single operation providing half-comprehension

Direct source: `research/2026-10-22/notes/uniform-half-comprehension-definitions.md`
(unpaginated, original research, `misc`, 22 October 2026).

The generic definitions range over one fixed relational type. Unary proofs are
vectorized in their argument type by the certificate module. In the converses the
explicit Existence premise records exactly the use of a current tuple; C proves
that premise at closed types. No converse for full uniform inextensibility is asserted.
-/

namespace Classicism.Research
open Classicism.Paper Classicism.P

def UniformPersistent (τ : Type) [Rel τ] : Prop :=
  ∃ R : τ → τ, ∀ X : τ, Persistent (R X) ∧ R X ≡ X

def UniformWeakPersistent (τ : Type) [Rel τ] : Prop :=
  ∃ R : τ → τ, ∀ X : τ, WeaklyPersistent (R X) ∧ R X ≡ X

def UniformWeakInextensible (τ : Type) [Rel τ] : Prop :=
  ∃ R : τ → τ, ∀ X : τ, WeaklyInextensible (R X) ∧ R X ≡ X

def UniformInextensible (τ : Type) [Rel τ] : Prop :=
  ∃ R : τ → τ, ∀ X : τ, Inextensible (R X) ∧ R X ≡ X

theorem uniformPersistent_weak {τ : Type} [Rel τ] :
    UniformPersistent τ → UniformWeakPersistent τ :=
  fun h => h.elim fun R hR =>
    ⟨R, fun X => ⟨weaklyPersistent_of_persistent (hR X).1, (hR X).2⟩⟩

theorem uniformInextensible_weak {τ : Type} [Rel τ] :
    UniformInextensible τ → UniformWeakInextensible τ :=
  fun h => h.elim fun R hR =>
    ⟨R, fun X => ⟨weaklyInextensible_of_inextensible (hR X).1, (hR X).2⟩⟩

theorem actuality_uniformPersistent {σ : Type} [Ty σ] :
    Actuality → UniformPersistent (σ → Prop) :=
  fun h => h.elim fun w hw =>
    ⟨fun X y => w ≤ X y, fun X =>
      ⟨(Proofs.persistent_coext_of_actual_world w hw X).1,
       fun y => ((Proofs.persistent_coext_of_actual_world w hw X).2 y).symm⟩⟩

theorem actuality_uniformWeakPersistent {σ : Type} [Ty σ] :
    Actuality → UniformWeakPersistent (σ → Prop) :=
  fun h => uniformPersistent_weak (actuality_uniformPersistent h)

theorem actuality_uniformWeakInextensible {σ : Type} [Ty σ] :
    Actuality → UniformWeakInextensible (σ → Prop) :=
  fun h => h.elim fun w hw =>
    ⟨fun X y => w ∧ X y, fun X =>
      ⟨Proofs.weaklyInextensible_of_actualWorld w hw X,
       fun y => ⟨fun hy => hy.2, fun hy => ⟨hw.1, hy⟩⟩⟩⟩

theorem uniformWeakPersistent_evaluator_at {σ : Type} [Ty σ] (a : σ)
    (h : UniformWeakPersistent (σ → Prop)) : HasPositiveEvaluator :=
  h.elim fun R hR =>
    ⟨fun p => R (fun _ => p) a,
     ⟨fun p => (hR (fun _ => p)).2 a,
      fun p hp => (hR (fun _ => p)).1 a (((hR (fun _ => p)).2 a).2 hp)⟩⟩

/-- A currently empty weakly inextensible property has necessarily false values. -/
theorem incl_self_neg {σ : Type} [Ty σ] (Y : σ → Prop) :
    Y ⊆ (fun a => ¬ Y a) → ∀ a : σ, ¬ Y a := fun h a ha => h a ha ha

theorem empty_weaklyInextensible {σ : Type} [Ty σ] (Y : σ → Prop)
    (hY : WeaklyInextensible Y) (hn : ∀ a : σ, ¬ Y a) :
    □ (∀ a : σ, ¬ Y a) :=
  modal_K _ _ (nec% (incl_self_neg Y))
    (hY (fun a => ¬ Y a) (fun a ha => False.elim (hn a ha)))

theorem uniformWeakInextensible_evaluator_at {σ : Type} [Ty σ] (a : σ)
    (h : UniformWeakInextensible (σ → Prop)) : HasPositiveEvaluator := by
  obtain ⟨R, hR⟩ := h
  refine ⟨fun p => ¬ R (fun _ => ¬ p) a, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    refine ⟨?_, ?_⟩
    · intro hn
      exact (em p).elim (fun hp => hp)
        (fun hp => False.elim (hn (((hR (fun _ => ¬ p)).2 a).2 hp)))
    · intro hp hRpa
      exact ((hR (fun _ => ¬ p)).2 a).1 hRpa hp
  · intro p hp
    exact converse_barcan _
      (empty_weaklyInextensible _ (hR (fun _ => ¬ p)).1
        (fun b hb => ((hR (fun _ => ¬ p)).2 b).1 hb hp)) a

theorem uniformWeakPersistent_actuality {σ : Type} [Ty σ] :
    Existence σ → UniformWeakPersistent (σ → Prop) → Actuality :=
  fun he h => he.elim fun a _ =>
    positiveEvaluator_actuality (uniformWeakPersistent_evaluator_at a h)

theorem uniformPersistent_actuality {σ : Type} [Ty σ] :
    Existence σ → UniformPersistent (σ → Prop) → Actuality :=
  fun he h => uniformWeakPersistent_actuality he (uniformPersistent_weak h)

theorem uniformWeakInextensible_actuality {σ : Type} [Ty σ] :
    Existence σ → UniformWeakInextensible (σ → Prop) → Actuality :=
  fun he h => he.elim fun a _ =>
    positiveEvaluator_actuality (uniformWeakInextensible_evaluator_at a h)

theorem uniformInextensible_actuality {σ : Type} [Ty σ] :
    Existence σ → UniformInextensible (σ → Prop) → Actuality :=
  fun he h => uniformWeakInextensible_actuality he (uniformInextensible_weak h)

/-! The nullary case has no tuple and needs no Existence premise. -/

theorem actuality_uniformPersistent_t : Actuality → UniformPersistent Prop :=
  fun h => h.elim fun w hw =>
    ⟨fun p => □ (w → p), fun p =>
      ⟨nec% (modal_four (w → p)), (actualWorld_positiveEvaluator w hw).1 p⟩⟩

theorem actuality_uniformWeakInextensible_t : Actuality → UniformWeakInextensible Prop :=
  fun h => h.elim fun w hw =>
    ⟨fun p => w ∧ p, fun p =>
      ⟨fun z hz => modal_K _ _
        (nec% (imp_of_w_imp_t w p z))
        ((le_iff_prop _ _).1 (hw.2 _ (fun hwp => box_elim (hz hwp)))),
       ⟨fun hp => hp.2, fun hp => ⟨hw.1, hp⟩⟩⟩⟩
where
  imp_of_w_imp_t (w p z : Prop) : (w → (w ∧ p → z)) → (w ∧ p → z) :=
    fun h hp => h hp.1 hp

theorem uniformWeakPersistent_actuality_t : UniformWeakPersistent Prop → Actuality :=
  fun h => h.elim fun R hR => positiveEvaluator_actuality
    ⟨R, ⟨fun p => (hR p).2, fun p hp => (hR p).1 (((hR p).2).2 hp)⟩⟩

theorem incl_self_neg_t (p : Prop) : incl p (¬ p) → ¬ p := fun h hp => h hp hp

theorem uniformWeakInextensible_actuality_t : UniformWeakInextensible Prop → Actuality := by
  intro h
  obtain ⟨R, hR⟩ := h
  apply positiveEvaluator_actuality
  refine ⟨fun p => ¬ R (¬ p), ?_, ?_⟩
  · intro p
    refine ⟨?_, fun hp hRnp => ((hR (¬ p)).2).1 hRnp hp⟩
    intro hn
    exact (em p).elim (fun hp => hp)
      (fun hp => False.elim (hn (((hR (¬ p)).2).2 hp)))
  · intro p hp
    exact modal_K _ _ (nec% (incl_self_neg_t (R (¬ p))))
      ((hR (¬ p)).1 (¬ R (¬ p)) (fun hRnp => False.elim (((hR (¬ p)).2).1 hRnp hp)))

end Classicism.Research
