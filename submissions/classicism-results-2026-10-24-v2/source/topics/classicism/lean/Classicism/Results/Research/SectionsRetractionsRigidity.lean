import Classicism.Results.Research.SectionsRetractionsStrong
import Classicism.Results.Research.ModalRigidityDescent

/-!
# Section closure of rigid relations

Direct source: `research/2026-10-22/notes/rigid-boolean-closure.md`, §7
(`misc`, original research, 22 October 2026; unpaginated).
This is the Choice-owned section component of rigidity.06. Fixing a parameter
of type σ needs unboxed ND_σ, independently of the remaining argument types.
The direct test below is the source's sealed cut/projection argument unfolded.
-/
namespace Classicism.Research.Splitting
open Classicism.Paper Classicism.P

def WeakSectionClosure (ν σ : Type) [Ty ν] [Ty σ] : Prop :=
  ∀ R : σ → ν → Prop, WeaklyRigid R → ∀ a, WeaklyRigid (R a)
def RigidSectionClosure (ν σ : Type) [Ty ν] [Ty σ] : Prop :=
  ∀ R : σ → ν → Prop, Rigid R → ∀ a, Rigid (R a)
def WeakPointSectionClosure (σ : Type) [Ty σ] : Prop :=
  ∀ R : σ → Prop, WeaklyRigid R → ∀ a, WeaklyRigid (R a)
def RigidPointSectionClosure (σ : Type) [Ty σ] : Prop :=
  ∀ R : σ → Prop, Rigid R → ∀ a, Rigid (R a)

theorem weak_section_decided {ν σ : Type} [Ty ν] [Ty σ]
    (R : σ → ν → Prop) (a : σ) (hr : WeaklyRigid R)
    (hd : ∀ x y, R x y → (□ (x = a) ∨ □ (x ≠ a))) : WeaklyRigid (R a) := by
  refine ⟨hr.1 a, ?_⟩
  intro Z hz
  have ht : □ (∀ x y, R x y → x = a → Z y) :=
    hr.2 (fun x y => x = a → Z y) fun x y hxy =>
      (hd x y hxy).elim
        (fun he => box_imp_of_box _ _ (hz y (box_elim he ▸ hxy)))
        (fun hn => box_imp_of_box_not _ _ hn)
  exact modal_K _ _
    (nec% (fun (h : ∀ x y, R x y → x = a → Z y) (y : ν) (hy : R a y) =>
      h a y hy rfl)) ht

theorem nd_equality_decision {σ : Type} [Ty σ] (nd : NecessityOfDistinctness σ)
    (x a : σ) : □ (x = a) ∨ □ (x ≠ a) :=
  (em (x = a)).elim (fun he => Or.inl (necessity_of_identity _ _ he))
    (fun hn => Or.inr (nd x a hn))

theorem decision_persistent (p : Prop) : (□ p ∨ □ (¬ p)) → □ (□ p ∨ □ (¬ p)) :=
  fun h => h.elim
    (fun hp => modal_K _ _ (nec% (fun (h : □ p) => (Or.inl h : □ p ∨ □ (¬ p))))
      (modal_four _ hp))
    (fun hn => modal_K _ _ (nec% (fun (h : □ (¬ p)) => (Or.inr h : □ p ∨ □ (¬ p))))
      (modal_four _ hn))

theorem nd_weak_sections {ν σ : Type} [Ty ν] [Ty σ] :
    NecessityOfDistinctness σ → WeakSectionClosure ν σ :=
  fun nd R hr a => weak_section_decided R a hr
    (fun x _ _ => nd_equality_decision nd x a)

theorem nd_rigid_sections {ν σ : Type} [Ty ν] [Ty σ] :
    NecessityOfDistinctness σ → RigidSectionClosure ν σ := by
  intro nd R hr a
  have hs : □ (∀ x y, R x y → (□ (x = a) ∨ □ (x ≠ a))) :=
    (weaklyRigid_of_rigid hr).2 (fun x _ => □ (x = a) ∨ □ (x ≠ a))
      (fun x _ _ => decision_persistent (x = a) (nd_equality_decision nd x a))
  exact (rigid_iff_box_weaklyRigid _).mpr
    (modal_K _ _ (modal_K _ _ (nec% (weak_section_decided R a))
      ((rigid_iff_box_weaklyRigid R).mp hr)) hs)

theorem decided_weaklyRigid (p : Prop) : (□ p ∨ □ (¬ p)) → WeaklyRigid p :=
  fun h => h.elim
    (fun hp => ⟨fun _ => hp, fun q hq => box_imp_of_box p q (hq (box_elim hp))⟩)
    (fun hn => ⟨fun hp => (box_elim hn hp).elim, fun q _ => box_imp_of_box_not p q hn⟩)

theorem decided_rigid (p : Prop) : (□ p ∨ □ (¬ p)) → Rigid p := fun h =>
  (rigid_iff_box_weaklyRigid p).mpr
    (modal_K _ _ (nec% (decided_weaklyRigid p)) (decision_persistent p h))

theorem nd_weak_membership {σ : Type} [Ty σ] (nd : NecessityOfDistinctness σ)
    (R : σ → Prop) (hr : WeaklyRigid R) (a : σ) : □ (R a) ∨ □ (¬ R a) :=
  (em (R a)).elim (fun ha => Or.inl (hr.1 a ha)) fun hn =>
    Or.inr (modal_K _ _
      (nec% (fun (h : ∀ x, R x → x ≠ a) (ha : R a) => h a ha rfl))
      (hr.2 (fun x => x ≠ a) (fun x hx => nd x a (fun he => hn (he ▸ hx)))))

theorem nd_weak_point_sections {σ : Type} [Ty σ] :
    NecessityOfDistinctness σ → WeakPointSectionClosure σ :=
  fun nd R hr a => decided_weaklyRigid _ (nd_weak_membership nd R hr a)

theorem nd_rigid_point_sections {σ : Type} [Ty σ] :
    NecessityOfDistinctness σ → RigidPointSectionClosure σ :=
  fun nd R hr a => decided_rigid _ (nd_weak_membership nd R (weaklyRigid_of_rigid hr) a)

theorem false_weaklyRigid_necessary_false (p : Prop) (hp : WeaklyRigid p)
    (hn : ¬ p) : □ (¬ p) :=
  (box_not_eq p).mpr
    (le_antisymm_prop p False
      ((le_iff_prop p False).mpr (hp.2 False (fun h => (hn h).elim)))
      (bot_le_prop p))

theorem weak_point_sections_nd {σ : Type} [Ty σ] :
    WeakPointSectionClosure σ → NecessityOfDistinctness σ :=
  fun sc a b hn => false_weaklyRigid_necessary_false (a = b)
    (sc (fun x => x = b)
      (weaklyRigid_of_rigid (ModalRigidityDescent.singleton_rigid b)) a) hn

theorem rigid_point_sections_nd {σ : Type} [Ty σ] :
    RigidPointSectionClosure σ → NecessityOfDistinctness σ :=
  fun sc a b hn => false_weaklyRigid_necessary_false (a = b)
    (weaklyRigid_of_rigid (sc (fun x => x = b) (ModalRigidityDescent.singleton_rigid b) a)) hn

theorem weak_point_sections_iff_nd {σ : Type} [Ty σ] :
    WeakPointSectionClosure σ ↔ NecessityOfDistinctness σ :=
  ⟨weak_point_sections_nd, nd_weak_point_sections⟩

theorem rigid_point_sections_iff_nd {σ : Type} [Ty σ] :
    RigidPointSectionClosure σ ↔ NecessityOfDistinctness σ :=
  ⟨rigid_point_sections_nd, nd_rigid_point_sections⟩

end Classicism.Research.Splitting
