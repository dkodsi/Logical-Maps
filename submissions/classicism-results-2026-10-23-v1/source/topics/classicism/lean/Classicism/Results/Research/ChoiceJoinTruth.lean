import Classicism.Results.Research.ChoiceActuality

/-!
# Actuality and truth reflection for represented joins

Direct source: `research/2026-10-22/followup/choice-completeness-actuality.md`,
§9, with the direct Actuality reduction below obtained during translation
(`misc`, original research, 22 October 2026; unpaginated).

No completeness is assumed when the particular join is already given. The
conclusion is actual coextension; it is not an identity of relation entities.
-/
namespace Classicism.Research.Choice
open Classicism.Paper Classicism.P

def JoinTruthReflection : Prop :=
  ∀ A : Prop → Prop, ∀ j : Prop, LUB j A → (j ↔ ∃ a, A a ∧ a)

theorem actuality_join_truth : Actuality → JoinTruthReflection := by
  intro act A j hj
  obtain ⟨w, hw, hwl⟩ := act
  constructor
  · intro hjt
    refine (em (∃ a, A a ∧ a)).elim id (fun hn => False.elim ?_)
    have hub : UB (¬ w) A := fun a ha =>
      swap_neg_le w a (hwl (¬ a) (fun ht => hn ⟨a, ha, ht⟩))
    exact (imp_of_le_prop _ _ ((hj (¬ w)).1 hub) hjt) hw
  · intro h
    obtain ⟨a, ha, ht⟩ := h
    exact imp_of_le_prop _ _ (((hj j).2 (le_refl_prop j)) a ha) ht

/-- Under failure of Actuality, the family of all current falsehoods already
has supremum `True` in bare C. No general completeness premise is needed. -/
theorem falsehoods_lub_top (hn : ¬ Actuality) : LUB True (fun p : Prop => ¬ p) := by
  intro q
  constructor
  · intro h
    refine (em q).elim (fun hq => ?_) (fun hnq => ?_)
    · have hnqq : (¬ q) ≤ q := h (¬ q) (fun hnq => hnq hq)
      have eqt : q = True := (neg_le_iff_box q).1 hnqq
      rw [eqt]
      exact le_refl_prop True
    · exfalso
      apply hn
      refine ⟨¬ q, hnq, fun p hp => ?_⟩
      have hnp : (¬ p) ≤ q := h (¬ p) (fun hnp => hnp hp)
      have hle := neg_mono_le (¬ p) q hnp
      rw [not_not_eq] at hle
      exact hle
  · intro h p _
    exact le_trans_prop p True q (le_top_prop p) h

theorem join_truth_actuality : JoinTruthReflection → Actuality := by
  intro h
  refine (em Actuality).elim id (fun hn => False.elim ?_)
  obtain ⟨a, hna, ha⟩ := (h (fun p : Prop => ¬ p) True (falsehoods_lub_top hn)).1 trivial
  exact hna ha

theorem actuality_iff_join_truth : Actuality ↔ JoinTruthReflection :=
  ⟨actuality_join_truth, join_truth_actuality⟩

/-- A given algebraic join is currently coextensive with the material union. -/
theorem actuality_join_coext {σ : Type} [Ty σ] (act : Actuality)
    (A : (σ → Prop) → Prop) (J : σ → Prop) (hJ : LUB J A) :
    ∀ x, J x ↔ ∃ F, A F ∧ F x := by
  intro x
  have h := actuality_join_truth act (fun p => ∃ F, A F ∧ p = F x) (J x)
    (evaluation_image_lub A J hJ x)
  constructor
  · intro hj
    obtain ⟨p, ⟨F, hF, e⟩, hp⟩ := h.1 hj
    exact ⟨F, hF, e ▸ hp⟩
  · intro hf
    obtain ⟨F, hF, hx⟩ := hf
    exact h.2 ⟨F x, ⟨F, hF, rfl⟩, hx⟩

/-- The RC + BC consequence needs no disjoint-refinement reconstruction. -/
theorem choice_completeness_join_coext {σ : Type} [Ty σ]
    (rc : RelationalChoice Prop Prop) (bc : BooleanCompleteness (Prop → Prop))
    (A : (σ → Prop) → Prop) (J : σ → Prop) (hJ : LUB J A) :
    ∀ x, J x ↔ ∃ F, A F ∧ F x :=
  actuality_join_coext (choice_completeness_actuality_sharp rc bc) A J hJ

end Classicism.Research.Choice
