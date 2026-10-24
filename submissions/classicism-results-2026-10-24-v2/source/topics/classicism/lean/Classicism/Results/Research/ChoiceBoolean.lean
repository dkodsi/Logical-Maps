import Classicism.Principles.Lattice

/-!
Order lemmas used by the represented disjoint-increment proof. Direct source:
the Boolean calculations in `research/2026-10-22/notes/relational-choice-countable-completeness-ccc.md`,
§§1,3 (`misc`, unpaginated). The derived join is written with negation and meet
so the existing `Pointwise` interface suffices at every admitted relational type.
-/
namespace Classicism.Research.Choice
open Classicism.Paper Classicism.P

section
variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

theorem meet_le_left (a b : τ) : (a ∧ b) ≤ a :=
  le_of_box_incl (nec% (incl_and_left a b))

theorem meet_le_right (a b : τ) : (a ∧ b) ≤ b :=
  le_of_box_incl (nec% (incl_and_right a b))

theorem le_meet (x a b : τ) (ha : x ≤ a) (hb : x ≤ b) : x ≤ (a ∧ b) :=
  le_of_box_incl (modal_K _ _ (modal_K _ _ (nec% (incl_and a b x))
    ((le_iff _ _).1 ha)) ((le_iff _ _).1 hb))

theorem neg_intro_le (x y z : τ) (h₁ : (x ∧ y) ≤ z) (h₂ : (x ∧ y) ≤ ¬ z) :
    x ≤ ¬ y :=
  le_of_box_incl (modal_K _ _ (modal_K _ _ (nec% (incl_neg_intro x y z))
    ((le_iff _ _).1 h₁)) ((le_iff _ _).1 h₂))

theorem neg_antitone_incl (a b : τ) : a ⊆ b → (¬ b) ⊆ (¬ a) := fun h =>
  incl_neg_intro (¬ b) a b
    (incl_trans _ a b (incl_and_right (¬ b) a) h) (incl_and_left (¬ b) a)

theorem neg_antitone_le (a b : τ) (h : a ≤ b) : (¬ b) ≤ (¬ a) :=
  le_of_box_incl (modal_K _ _ (nec% (neg_antitone_incl a b)) ((le_iff _ _).1 h))

def OrderJoin (a b : τ) : τ := ¬ ((¬ a) ∧ (¬ b))

theorem le_orderJoin_left (a b : τ) : a ≤ OrderJoin a b :=
  neg_intro_le a ((¬ a) ∧ (¬ b)) a (meet_le_left _ _)
    (le_trans_rel _ _ _ (meet_le_right _ _) (meet_le_left _ _))

theorem le_orderJoin_right (a b : τ) : b ≤ OrderJoin a b :=
  neg_intro_le b ((¬ a) ∧ (¬ b)) b (meet_le_left _ _)
    (le_trans_rel _ _ _ (meet_le_right _ _) (meet_le_right _ _))

theorem orderJoin_le (a b u : τ) (ha : a ≤ u) (hb : b ≤ u) : OrderJoin a b ≤ u :=
  le_trans_rel _ _ _
    (neg_antitone_le (¬ u) ((¬ a) ∧ (¬ b))
      (le_meet _ _ _ (neg_antitone_le a u ha) (neg_antitone_le b u hb)))
    (neg_neg_le_rel u)

theorem eq_bot_of_opposite (x a : τ) (h₁ : x ≤ a) (h₂ : x ≤ ¬ a) : x = (⊥ : τ) :=
  eq_bot_of_le_neg_rel x (le_neg_of_le_both_rel x a h₁ h₂)

theorem disjoint_of_bounds (x y a : τ) (h₁ : x ≤ a) (h₂ : y ≤ ¬ a) :
    (x ∧ y) = (⊥ : τ) :=
  eq_bot_of_opposite (x ∧ y) a
    (le_trans_rel _ _ _ (meet_le_left x y) h₁)
    (le_trans_rel _ _ _ (meet_le_right x y) h₂)

theorem self_meet_bot (x : τ) (h : (x ∧ x) = (⊥ : τ)) : x = (⊥ : τ) :=
  le_antisymm_rel x ⊥ (h ▸ le_meet x x x (le_refl_rel x) (le_refl_rel x))
    (bot_le_rel x)

theorem increment_nonzero (a c : τ) (hac : a ≤ c) (hne : a ≠ c) :
    (c ∧ ¬ a) ≠ (⊥ : τ) := by
  intro e
  have hself : (c ∧ ¬ a) ≤ ¬ (c ∧ ¬ a) := by
    rw [e]
    exact bot_le_rel _
  have hc : c ≤ ¬ ¬ a := le_of_box_incl (modal_K _ _
    (nec% (incl_neg_of_and_incl_neg c (¬ a))) ((le_iff _ _).1 hself))
  exact hne (le_antisymm_rel a c hac (le_trans_rel _ _ _ hc (neg_neg_le_rel a)))

end
end Classicism.Research.Choice
