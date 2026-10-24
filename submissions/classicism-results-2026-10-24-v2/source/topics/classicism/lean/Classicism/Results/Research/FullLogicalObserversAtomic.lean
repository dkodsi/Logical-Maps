import Classicism.Results.Research.FullLogicalObservers
import Classicism.Results.Research.QuantifierObservers
import Classicism.Results.Records.C5

/-!
# Atomicity supplies full composite logical observers

Direct source: `research/2026-10-23/operator-characterizations/positive-operator-representation.txt`,
sections 2--3; `boolean-observers-and-atoms.txt`, section 1
(misc, original ordinary proofs, 23 October 2026, unpaginated).
The Boolean identities use BF at t; the quantifier identities use boxed BF
at the quantified type. No local assumption is passed through Equivalence.
-/

namespace Classicism.Research.FullLogicalObservers
open Classicism.P Classicism.Paper

def PatchedPrincipal (a : Prop) : Prop → Prop :=
  fun p => (◇ a ∧ □ (¬ a ∨ p)) ∨ (¬ ◇ a ∧ p)

/-- The explicit Boolean form is the same entire observer as the ordinary
implication presentation. It also keeps substitution of False syntactically
uniform in the object-language derivation. -/
theorem patched_principal_imp (a : Prop) :
    PatchedPrincipal a = (fun p => (◇ a ∧ □ (a → p)) ∨ (¬ ◇ a ∧ p)) :=
  funext (fun p => congrArg (fun r : Prop => (◇ a ∧ □ r) ∨ (¬ ◇ a ∧ p))
    (imp_eq_not_or a p).symm)

theorem patch_top_eq (c : Prop) :
    ((c ∧ True) ∨ (¬ c ∧ True)) = True :=
  propext ⟨fun _ => trivial,
    fun _ => (em c).elim (fun hc => Or.inl ⟨hc, trivial⟩)
      (fun hc => Or.inr ⟨hc, trivial⟩)⟩

theorem patch_bot_eq (c : Prop) :
    ((c ∧ ¬ c) ∨ (¬ c ∧ False)) = False :=
  propext ⟨fun h => h.elim (fun h => h.2 h.1) (fun h => h.2), False.elim⟩

theorem patch_meet_eq (c u v p q : Prop) :
    ((c ∧ (u ∧ v)) ∨ (¬ c ∧ (p ∧ q))) =
    (((c ∧ u) ∨ (¬ c ∧ p)) ∧ ((c ∧ v) ∨ (¬ c ∧ q))) :=
  propext ⟨fun h => h.elim
    (fun h => ⟨Or.inl ⟨h.1, h.2.1⟩, Or.inl ⟨h.1, h.2.2⟩⟩)
    (fun h => ⟨Or.inr ⟨h.1, h.2.1⟩, Or.inr ⟨h.1, h.2.2⟩⟩),
    fun h => h.1.elim
      (fun hu => h.2.elim (fun hv => Or.inl ⟨hu.1, hu.2, hv.2⟩)
        (fun hq => (hq.1 hu.1).elim))
      (fun hp => h.2.elim (fun hv => (hp.1 hv.1).elim)
        (fun hq => Or.inr ⟨hp.1, hp.2, hq.2⟩))⟩

theorem patch_not_eq (c u p : Prop) :
    ((c ∧ ¬ u) ∨ (¬ c ∧ ¬ p)) = ¬ ((c ∧ u) ∨ (¬ c ∧ p)) :=
  propext ⟨fun h hn => h.elim
    (fun hu => hn.elim (fun h => hu.2 h.2) (fun h => h.1 hu.1))
    (fun hp => hn.elim (fun h => hp.1 h.1) (fun h => hp.2 h.2)),
    fun h => (em c).elim
      (fun hc => Or.inl ⟨hc, fun hu => h (Or.inl ⟨hc, hu⟩)⟩)
      (fun hc => Or.inr ⟨hc, fun hp => h (Or.inr ⟨hc, hp⟩)⟩)⟩

theorem patched_top (a : Prop) : PatchedPrincipal a True = True := by
  have ht : (□ True) = True := modal_four True box_true
  unfold PatchedPrincipal
  rw [or_true_eq, ht]
  exact patch_top_eq (◇ a)

theorem patched_bot (a : Prop) : PatchedPrincipal a False = False := by
  unfold PatchedPrincipal
  rw [or_false_eq, box_not_eq_not_dia]
  exact patch_bot_eq (◇ a)

theorem patched_and (a p q : Prop) :
    PatchedPrincipal a (p ∧ q) = (PatchedPrincipal a p ∧ PatchedPrincipal a q) := by
  unfold PatchedPrincipal
  rw [or_and_distrib_eq (¬ a) p q, box_and_eq (¬ a ∨ p) (¬ a ∨ q)]
  exact patch_meet_eq (◇ a) (□ (¬ a ∨ p)) (□ (¬ a ∨ q)) p q

theorem imp_neg_as_not_meet (a p : Prop) : (a → ¬ p) = ¬ (a ∧ p) :=
  propext ⟨fun h hap => h hap.1 hap.2, fun h ha hp => h ⟨ha, hp⟩⟩

theorem meet_eq_of_le (a p : Prop) (h : a ≤ p) : (a ∧ p) = a :=
  (congrArg (fun r : Prop => a ∧ r) h).trans (and_or_absorb_eq a p)

theorem principal_neg_of_le (a p : Prop) (h : a ≤ p) :
    □ (a → ¬ p) = ¬ ◇ a :=
  (congrArg (fun r : Prop => □ r)
    ((imp_neg_as_not_meet a p).trans
      (congrArg Not (meet_eq_of_le a p h)))).trans (box_not_eq_not_dia a)

theorem principal_neg_guard (a p : Prop) (ha : Atom a) :
    ((◇ a) ∧ □ (a → ¬ p)) = ((◇ a) ∧ ¬ □ (a → p)) := by
  apply (atom_le_or_le_neg a p ha).elim
  · intro hp
    have hpBox : □ (a → p) := (le_iff_prop a p).1 hp
    have hpEq : (□ (a → p)) = True := modal_four (a → p) hpBox
    rw [principal_neg_of_le a p hp, hpEq,
      not_true_eq, and_not_self_eq, and_false_eq]
  · intro hn
    have hnBox : □ (a → ¬ p) := (le_iff_prop a (¬ p)).1 hn
    have hnEq : (□ (a → ¬ p)) = True := modal_four (a → ¬ p) hnBox
    have he : □ (a → p) = ¬ ◇ a := by
      have h := principal_neg_of_le a (¬ p) hn
      rw [not_not_eq] at h
      exact h
    rw [hnEq, he, not_not_eq,
      and_true_eq, and_self_eq]

theorem patched_not (a p : Prop) (ha : Atom a) :
    PatchedPrincipal a (¬ p) = ¬ PatchedPrincipal a p := by
  have hg := principal_neg_guard a p ha
  rw [imp_eq_not_or a (¬ p), imp_eq_not_or a p] at hg
  exact (congrArg (fun r : Prop => r ∨ (¬ ◇ a ∧ ¬ p)) hg).trans
    (patch_not_eq (◇ a) (□ (¬ a ∨ p)) p)

theorem join_as_neg_meet (p q : Prop) : (p ∨ q) = ¬ (¬ p ∧ ¬ q) := by
  rw [not_and_eq, not_not_eq, not_not_eq]

theorem patched_or (a p q : Prop) (ha : Atom a) :
    PatchedPrincipal a (p ∨ q) = (PatchedPrincipal a p ∨ PatchedPrincipal a q) := by
  rw [join_as_neg_meet p q, patched_not a _ ha, patched_and,
    patched_not a p ha, patched_not a q ha, ← join_as_neg_meet]

theorem patched_boolFull (a : Prop) (bf : Barcan Prop) (ha : Atom a) :
    BoolFull (PatchedPrincipal a) := by
  have fn : Functionality Prop Prop := Proofs.barcan_r_implies_functionality_r bf
  have fn₂ : Functionality Prop (Prop → Prop) :=
    Proofs.barcan_r_implies_functionality_r bf
  exact ⟨patched_top a, patched_bot a,
    fn _ _ (fun p => patched_not a p ha),
    fn₂ _ _ (fun p => fn _ _ (fun q => patched_and a p q)),
    fn₂ _ _ (fun p => fn _ _ (fun q => patched_or a p q ha))⟩

theorem patched_truth (a p : Prop) (ha : ◇ a) :
    PatchedPrincipal a p ↔ □ (a → p) := by
  unfold PatchedPrincipal
  rw [← imp_eq_not_or a p]
  exact ⟨fun h => h.elim And.right (fun h => (h.1 ha).elim),
    fun hp => Or.inl ⟨ha, hp⟩⟩

theorem patched_identity_truth (a p : Prop) (ha : ¬ ◇ a) :
    PatchedPrincipal a p ↔ p :=
  ⟨fun h => h.elim (fun h => (ha h.1).elim) And.right,
   fun hp => Or.inr ⟨ha, hp⟩⟩

theorem patched_forall_material {σ : Type} [Ty σ] (a : Prop) :
    Barcan σ → ∀ F : σ → Prop,
      (PatchedPrincipal a (∀ x, F x) ↔ ∀ x, PatchedPrincipal a (F x)) := by
  intro bf F
  apply (em (◇ a)).elim
  · intro ha
    exact ⟨fun h x => (patched_truth a (F x) ha).2
      ((QuantifierObservers.principal_forall a F bf).1
        ((patched_truth a _ ha).1 h) x),
      fun h => (patched_truth a _ ha).2
        ((QuantifierObservers.principal_forall a F bf).2
          (fun x => (patched_truth a (F x) ha).1 (h x)))⟩
  · intro ha
    exact ⟨fun h x => (patched_identity_truth a (F x) ha).2
      ((patched_identity_truth a _ ha).1 h x),
      fun h => (patched_identity_truth a _ ha).2
        (fun x => (patched_identity_truth a (F x) ha).1 (h x))⟩

theorem patched_forall_full {σ : Type} [Ty σ] (a : Prop)
    (bf : □ (Barcan σ)) :
    (fun F : σ → Prop => PatchedPrincipal a (∀ x, F x)) =
      (fun F : σ → Prop => ∀ x, PatchedPrincipal a (F x)) :=
  intensionality _ _ (modal_K _ _ (nec% (patched_forall_material (σ := σ) a)) bf)

theorem exists_as_neg_forall {σ : Type} [Ty σ] (F : σ → Prop) :
    (∃ x, F x) = ¬ (∀ x, ¬ F x) :=
  propext ⟨fun h hn => h.elim (fun x hx => hn x hx),
    fun h => (em (∃ x, F x)).elim id
      (fun hn => (h (fun x hx => hn ⟨x, hx⟩)).elim)⟩

theorem forall_full_to_exists_full {σ : Type} [Ty σ] (O : Prop → Prop)
    (hn : (fun p : Prop => O (¬ p)) = (fun p : Prop => ¬ O p))
    (hf : (fun F : σ → Prop => O (∀ x, F x)) =
      (fun F : σ → Prop => ∀ x, O (F x))) :
    (fun F : σ → Prop => O (∃ x, F x)) =
      (fun F : σ → Prop => ∃ x, O (F x)) := by
  calc
    (fun F : σ → Prop => O (∃ x, F x)) =
        (fun F : σ → Prop => O (¬ ∀ x, ¬ F x)) :=
      funext (fun F => congrArg O (exists_as_neg_forall F))
    _ = (fun F : σ → Prop => ¬ O (∀ x, ¬ F x)) :=
      congrArg (fun N : Prop → Prop => fun F : σ → Prop => N (∀ x, ¬ F x)) hn
    _ = (fun F : σ → Prop => ¬ ∀ x, O (¬ F x)) :=
      congrArg (fun U : (σ → Prop) → Prop => fun F : σ → Prop => ¬ U (fun x => ¬ F x)) hf
    _ = (fun F : σ → Prop => ¬ ∀ x, ¬ O (F x)) :=
      congrArg (fun N : Prop → Prop => fun F : σ → Prop => ¬ ∀ x, N (F x)) hn
    _ = (fun F : σ → Prop => ∃ x, O (F x)) :=
      funext (fun F => (exists_as_neg_forall (fun x => O (F x))).symm)

theorem patched_quantifierFull {σ : Type} [Ty σ] (a : Prop)
    (hb : BoolFull (PatchedPrincipal a)) (bf : □ (Barcan σ)) :
    QuantifierFull σ (PatchedPrincipal a) :=
  ⟨patched_forall_full a bf,
    forall_full_to_exists_full _ hb.2.2.1 (patched_forall_full a bf)⟩

theorem atom_possible (a : Prop) (ha : Atom a) : ◇ a :=
  fun h => not_le_neg_of_atom ha (le_neg_of_eq_false a h)

theorem patched_atom_truth (a p : Prop) (ha : Atom a) :
    PatchedPrincipal a p ↔ a ≤ p :=
  (patched_truth a p (atom_possible a ha)).trans (le_iff_prop a p).symm

theorem self_iff_top (p : Prop) : (p ↔ p) = True :=
  propext ⟨fun _ => trivial, fun _ => Iff.rfl⟩

/-- The same witness `PatchedPrincipal a` is used for every extra qualification X. -/
theorem atomicity_separation_by (X : (Prop → Prop) → Prop)
    (hat : Atomicity Prop)
    (hq : ∀ a : Prop, Atom a → BoolFull (PatchedPrincipal a) ∧ X (PatchedPrincipal a)) :
    SeparationBy X := by
  intro p q
  constructor
  · intro he O hO
    rw [he, self_iff_top, hO.1.1]
    trivial
  · intro h
    apply modalized_fregean p q
    apply (neg_le_iff_box (p ↔ q)).1
    exact Atomicity.to_dual hat (p ↔ q) (fun a ha =>
      (patched_atom_truth a (p ↔ q) ha).1 (h (PatchedPrincipal a) (hq a ha)))

theorem atomicity_full_separation {σ : Type} [Ty σ]
    (hat : Atomicity Prop) (bft : Barcan Prop) (bfs : □ (Barcan σ)) :
    SeparationFull σ :=
  atomicity_separation_by (QuantifierFull σ) hat (fun a ha =>
    ⟨patched_boolFull a bft ha,
      patched_quantifierFull a (patched_boolFull a bft ha) bfs⟩)

theorem c5_atomicity_full_separation {σ : Type} [Ty σ]
    (hat : Atomicity Prop) (hc5 : NecNecessityOfDistinctness Prop) :
    SeparationFull σ :=
  atomicity_full_separation hat
    (box_elim (Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r hc5))
    (Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r hc5)

theorem c5_atomicity_necessary_atomicity (hat : Atomicity Prop)
    (hc5 : NecNecessityOfDistinctness Prop) : □ (Atomicity Prop) := by
  have hact : NecActuality :=
    Proofs.atomicity_t_and_necessary_distinctness_necessary_t_imply_necessary_actuality hat hc5
  exact modal_K _ _ (modal_K _ _
    (nec% Proofs.c5_and_necessary_actuality_imply_atomicity_at_t)
      (modal_four _ hact)) (modal_four _ hc5)

theorem c5_atomicity_necessary_full_separation {σ : Type} [Ty σ]
    (hat : Atomicity Prop) (hc5 : NecNecessityOfDistinctness Prop) :
    □ (SeparationFull σ) :=
  modal_K _ _ (modal_K _ _ (nec% (c5_atomicity_full_separation (σ := σ)))
    (c5_atomicity_necessary_atomicity hat hc5)) (modal_four _ hc5)

end Classicism.Research.FullLogicalObservers
