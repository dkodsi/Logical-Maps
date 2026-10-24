import Classicism.Results.Research.WorldRepresentation

/-!
# Diagonal characters and local propositional atomicity

Direct source: `research/2026-10-23/operator-characterizations/diagonal-characters-independent-audit.txt`,
sections 1–4 (original research, misc, unpaginated, 23 October 2026).
Every premise is local and type t. No BF, C5, Choice, or operation identity is assumed.
-/
namespace Classicism.Research.DiagonalCharacters
open Classicism.P Classicism.Paper

def Kernel (E : Prop → Prop) : Prop := ∀ p : Prop, E p → p
def Bivalent (E : Prop → Prop) : Prop := ∀ p : Prop, E p = True ∨ E p = False
def NegationPreserving (E : Prop → Prop) : Prop := ∀ p : Prop, E (¬ p) = ¬ E p
def Diagonal (E : Prop → Prop) : Prop :=
  E False = False ∧ Bivalent E ∧ NegationPreserving E ∧ E (Kernel E)
def FullCharacter (E : Prop → Prop) : Prop :=
  Diagonal E ∧ E True = True ∧ ∀ p q : Prop, E (p ∧ q) = (E p ∧ E q)
def Canonical (a : Prop) : Prop → Prop := fun p => a ≤ p
def Separation : Prop :=
  ∀ p q : Prop, p = q ↔ ∀ E : Prop → Prop, Diagonal E → (E p ↔ E q)

theorem bivalent_true (E : Prop → Prop) (hb : Bivalent E) (p : Prop)
    (hp : E p) : E p = True :=
  (hb p).elim id (fun hf => False.elim (Eq.mp hf hp))

theorem bivalent_false (E : Prop → Prop) (hb : Bivalent E) (p : Prop)
    (hp : ¬ E p) : E p = False :=
  (hb p).elim (fun ht => False.elim (hp (Eq.mpr ht trivial))) id

theorem endpoint_distinct (E : Prop → Prop) (p q : Prop) :
    E p = True → E q = False → p ≠ q := fun hp hq he =>
  Eq.mp (hp.symm.trans ((congrArg E he).trans hq)) trivial

theorem stable_endpoint_distinct (E : Prop → Prop) (p q : Prop)
    (hp : E p = True) (hq : E q = False) : □ (p ≠ q) :=
  modal_K _ _ (modal_K _ _ (nec% (endpoint_distinct E p q))
    (necessity_of_identity _ _ hp)) (necessity_of_identity _ _ hq)

theorem diagonal_stable (E : Prop → Prop) (h : Diagonal E) : □ ◇ (Kernel E) :=
  stable_endpoint_distinct E (Kernel E) False (bivalent_true E h.2.1 _ h.2.2.2) h.1

theorem kernel_instance (E : Prop → Prop) (p : Prop) : E p → Kernel E → p :=
  fun hp hw => hw p hp

theorem accepted_below (E : Prop → Prop) (p : Prop) (hp : E p = True) : Kernel E ≤ p :=
  le_of_box_incl (modal_K _ _ (nec% (kernel_instance E p)) hp)

theorem rejected_negation (E : Prop → Prop) (hn : NegationPreserving E)
    (p : Prop) (hp : E p = False) : E (¬ p) = True :=
  (hn p).trans ((congrArg Not hp).trans not_false_eq)

theorem diagonal_decides (E : Prop → Prop) (h : Diagonal E) (p : Prop) :
    Kernel E ≤ p ∨ Kernel E ≤ ¬ p :=
  (h.2.1 p).elim (fun hp => Or.inl (accepted_below E p hp))
    (fun hp => Or.inr (accepted_below E (¬ p) (rejected_negation E h.2.2.1 p hp)))

theorem diagonal_atom (E : Prop → Prop) (h : Diagonal E) : Atom (Kernel E) :=
  atom_of_decides _ ⟨box_elim (diagonal_stable E h), diagonal_decides E h⟩

theorem diagonal_stable_atom (E : Prop → Prop) : Diagonal E →
    Atom (Kernel E) ∧ □ ◇ (Kernel E) :=
  fun h => ⟨diagonal_atom E h, diagonal_stable E h⟩

theorem incompatible_orders (a p : Prop) : a ≤ ¬ p → a ≠ False → ¬ (a ≤ p) :=
  fun hn ha hp => ha (eq_false_of_le_neg a (le_neg_of_le_both_rel a p hp hn))

theorem stable_rejected_order (a p : Prop) (hs : □ ◇ a) (hn : a ≤ ¬ p) :
    (a ≤ p) = False :=
  (box_not_eq (a ≤ p)).mp
    (modal_K _ _ (modal_K _ _ (nec% (incompatible_orders a p))
      (box_le_prop a (¬ p) hn)) hs)

/-- Literal equality at each current argument; no identity of operations is inferred. -/
theorem diagonal_pointwise (E : Prop → Prop) (h : Diagonal E) (p : Prop) :
    E p = Canonical (Kernel E) p :=
  (h.2.1 p).elim
    (fun hp => hp.trans (box_le_prop _ _ (accepted_below E p hp)).symm)
    (fun hp => hp.trans (stable_rejected_order _ p (diagonal_stable E h)
      (accepted_below E (¬ p) (rejected_negation E h.2.2.1 p hp))).symm)

theorem diagonal_truth (E : Prop → Prop) (h : Diagonal E) (p : Prop) :
    E p ↔ Kernel E ≤ p :=
  ⟨fun hp => Eq.mp (diagonal_pointwise E h p) hp,
   fun hp => Eq.mpr (diagonal_pointwise E h p) hp⟩

/-- The defining universal cancels the canonical operator in bare C. -/
theorem canonical_kernel (a : Prop) : Kernel (Canonical a) = a :=
  propext ⟨fun h => h a (le_refl_prop a),
    fun ha p hp => imp_of_le_prop a p hp ha⟩

theorem canonical_meet (a p q : Prop) :
    Canonical a (p ∧ q) = (Canonical a p ∧ Canonical a q) :=
  propext (WorldRepresentation.at_and a p q)

theorem canonical_bivalent (a : Prop) (ha : Atom a) (hs : □ ◇ a) :
    Bivalent (Canonical a) := fun p =>
  (atom_le_or_le_neg a p ha).elim
    (fun hp => Or.inl (box_le_prop a p hp))
    (fun hn => Or.inr (stable_rejected_order a p hs hn))

theorem canonical_bottom (a : Prop) (hs : □ ◇ a) : Canonical a False = False :=
  stable_rejected_order a False hs (by rw [not_false_eq]; exact le_top_prop a)

theorem canonical_negation (a : Prop) (ha : Atom a) (hs : □ ◇ a) :
    NegationPreserving (Canonical a) := by
  intro p
  apply (atom_le_or_le_neg a p ha).elim
  · intro hp
    have hnp : a ≤ ¬ ¬ p := by rw [not_not_eq]; exact hp
    calc Canonical a (¬ p) = False := stable_rejected_order a (¬ p) hs hnp
      _ = ¬ True := not_true_eq.symm
      _ = ¬ Canonical a p := congrArg Not (box_le_prop a p hp).symm
  · intro hn
    calc Canonical a (¬ p) = True := box_le_prop a (¬ p) hn
      _ = ¬ False := not_false_eq.symm
      _ = ¬ Canonical a p := congrArg Not (stable_rejected_order a p hs hn).symm

theorem canonical_accepts_kernel (a : Prop) : Canonical a (Kernel (Canonical a)) := by
  rw [canonical_kernel]
  exact le_refl_prop a

theorem canonical_diagonal (a : Prop) : Atom a → □ ◇ a → Diagonal (Canonical a) :=
  fun ha hs => ⟨canonical_bottom a hs, canonical_bivalent a ha hs,
    canonical_negation a ha hs, canonical_accepts_kernel a⟩

theorem diagonal_top (E : Prop → Prop) (h : Diagonal E) : E True = True :=
  (diagonal_pointwise E h True).trans (box_le_prop _ True (le_top_prop _))

theorem diagonal_meet (E : Prop → Prop) (h : Diagonal E) (p q : Prop) :
    E (p ∧ q) = (E p ∧ E q) := by
  rw [diagonal_pointwise E h (p ∧ q), diagonal_pointwise E h p,
    diagonal_pointwise E h q]
  exact canonical_meet (Kernel E) p q

theorem full_character_iff_diagonal (E : Prop → Prop) : FullCharacter E ↔ Diagonal E :=
  ⟨And.left, fun h => ⟨h, diagonal_top E h, diagonal_meet E h⟩⟩

theorem separating_witness (h : Separation) (p q : Prop) (hne : p ≠ q) :
    ∃ E : Prop → Prop, Diagonal E ∧ ¬ (E p ↔ E q) := by
  apply (em (∃ E : Prop → Prop, Diagonal E ∧ ¬ (E p ↔ E q))).elim id
  intro hn
  apply False.elim
  apply hne
  apply (h p q).2
  intro E he
  exact (em (E p ↔ E q)).elim id (fun hneq => False.elim (hn ⟨E, he, hneq⟩))

theorem bivalent_difference_stable (E : Prop → Prop) (hb : Bivalent E)
    (p q : Prop) (hne : ¬ (E p ↔ E q)) : □ (p ≠ q) :=
  (em (E p)).elim
    (fun hp => stable_endpoint_distinct E p q (bivalent_true E hb p hp)
      (bivalent_false E hb q (fun hq => hne ⟨fun _ => hq, fun _ => hp⟩)))
    (fun hp => modal_K _ _ (nec% (fun (h : q ≠ p) (he : p = q) => h he.symm))
      (stable_endpoint_distinct E q p
        (bivalent_true E hb q ((em (E q)).elim id
          (fun hq => False.elim (hne ⟨fun he => False.elim (hp he),
            fun he => False.elim (hq he)⟩))))
        (bivalent_false E hb p hp)))

theorem separation_nd : Separation → NecessityOfDistinctness Prop :=
  fun h p q hn => (separating_witness h p q hn).elim fun E he =>
    bivalent_difference_stable E he.1.2.1 p q he.2

theorem separation_atomicity : Separation → Atomicity Prop := by
  intro h p
  apply (em (p = False)).elim
  · intro hp
    exact Or.inl (le_neg_of_eq_false p hp)
  · intro hp
    obtain ⟨E, he, hd⟩ := separating_witness h p False hp
    have hep : E p := (em (E p)).elim id (fun hn => False.elim
      (hd ⟨fun ht => False.elim (hn ht), fun hf => False.elim (Eq.mp he.1 hf)⟩))
    exact Or.inr ⟨Kernel E, diagonal_atom E he,
      accepted_below E p (bivalent_true E he.2.1 p hep)⟩

theorem atom_profile_iff (a p q : Prop) (ha : Atom a)
    (h : (a ≤ p) ↔ (a ≤ q)) : a ≤ (p ↔ q) :=
  (em (a ≤ p)).elim
    (fun hp => le_of_box_incl (modal_K _ _ (modal_K _ _
      (nec% (fun (hp : a → p) (hq : a → q) (ha : a) =>
        (show p ↔ q from ⟨fun _ => hq ha, fun _ => hp ha⟩)))
      ((le_iff_prop _ _).1 hp)) ((le_iff_prop _ _).1 (h.1 hp))))
    (fun hn => le_of_box_incl (modal_K _ _ (modal_K _ _
      (nec% (fun (hp : a → ¬ p) (hq : a → ¬ q) (ha : a) =>
        (show p ↔ q from ⟨fun hp' => False.elim (hp ha hp'),
          fun hq' => False.elim (hq ha hq')⟩)))
      ((le_iff_prop _ _).1 ((WorldRepresentation.at_neg a p ha).2 hn)))
      ((le_iff_prop _ _).1 ((WorldRepresentation.at_neg a q ha).2
        (fun hq => hn (h.2 hq))))))

theorem atomic_profiles_equal (hat : Atomicity Prop) (p q : Prop)
    (h : ∀ a : Prop, Atom a → ((a ≤ p) ↔ (a ≤ q))) : p = q :=
  intensionality p q ((WorldRepresentation.atomic_coverage hat (p ↔ q)).1
    (fun a ha => atom_profile_iff a p q ha (h a ha)))

theorem nd_atomicity_separation : NecessityOfDistinctness Prop → Atomicity Prop → Separation :=
  fun nd hat p q => ⟨fun he E _ => he ▸ Iff.rfl, fun h =>
    atomic_profiles_equal hat p q (fun a ha => h (Canonical a)
      (canonical_diagonal a ha (nd a False (WorldRepresentation.atom_possible a ha))))⟩

/-- Exact finite, unboxed, type-t characterization; no full-schema upgrade. -/
theorem separation_iff_nd_atomicity : Separation ↔
    (NecessityOfDistinctness Prop ∧ Atomicity Prop) :=
  ⟨fun h => ⟨separation_nd h, separation_atomicity h⟩,
    fun h => nd_atomicity_separation h.1 h.2⟩

end Classicism.Research.DiagonalCharacters
