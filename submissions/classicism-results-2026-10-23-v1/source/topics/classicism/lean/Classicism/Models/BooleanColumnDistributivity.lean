import Classicism.Models.BooleanColumnAlgebra
import Classicism.Models.BooleanColumnClosure
import Mathlib.SetTheory.Cardinal.Order

/-!
# Small binary tables in the concrete column Boolean algebra

Original supporting formalization (misc), 23 October 2026, of section 2
of `research/2026-10-23/boolean-valued-finite-choice.md` (unpaginated).
Every family of fewer than regular κ Boolean values can simultaneously
be decided below any actual column condition. The proof well-orders the
index type, recursively refines after taking actual small unions, and
then takes one final small union. Cone density turns this into the exact
binary distributivity equation.

No distributivity, generic filter, maximum principle, or model-existence
verdict is an assumption. This is external classical mathematics about
the concrete completion; it is not a typed Choice certificate.
-/

namespace Classicism.Meta.ChoiceBoolean.ColumnDistributivity

open ColumnConditions ColumnAlgebra

universe u

noncomputable section

variable {κ : Cardinal.{u}} {I : Type u}

abbrev cone (p : Condition κ) : Values κ :=
  ConditionCompletion.cone (Condition κ) p

/-- The value of a binary decision: false chooses the complement. -/
def bitValue (b : Values κ) : Bool → Values κ
  | false => bᶜ
  | true => b

/-- Every condition has an actual stronger condition deciding any Boolean
value. Cone inclusion alone is upgraded to actual extension by the
common-extension theorem for the completion. -/
theorem exists_deciding_extension (p : Condition κ) (b : Values κ) :
    ∃ q : Condition κ, q ≤ p ∧ ∃ v : Bool, cone q ≤ bitValue b v := by
  classical
  by_cases h : cone p ⊓ b = ⊥
  · refine ⟨p, le_rfl, false, ?_⟩
    exact le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr h.le)
  · obtain ⟨r, hr⟩ := ConditionCompletion.dense_cone (Condition κ) (cone p ⊓ b) h
    have hrp : cone r ⊓ cone p ≠ ⊥ := by
      intro hbot
      apply ConditionCompletion.cone_ne_bot (Condition κ) r
      exact (inf_eq_left.mpr
        (show cone r ≤ cone p from hr.trans inf_le_left)).symm.trans hbot
    obtain ⟨q, hqr, hqp⟩ :=
      (ConditionCompletion.cone_compatible_iff (Condition κ) r p).mp hrp
    refine ⟨q, hqp, true, ?_⟩
    exact (ConditionCompletion.cone_mono (Condition κ) hqr).trans
      (hr.trans inf_le_right)

private def decide (p : Condition κ) (b : Values κ) : Condition κ :=
  Classical.choose (exists_deciding_extension p b)

private theorem decide_le (p : Condition κ) (b : Values κ) : decide p b ≤ p :=
  (Classical.choose_spec (exists_deciding_extension p b)).1

private theorem decide_spec (p : Condition κ) (b : Values κ) :
    ∃ v : Bool, cone (decide p b) ≤ bitValue b v :=
  (Classical.choose_spec (exists_deciding_extension p b)).2

section WellOrdered

variable [LinearOrder I] [WellFoundedLT I]

/-- Pad the earlier history with the starting condition. This family is
indexed by I itself, so its cardinal bound is precisely the given one. -/
private def earlier (p : Condition κ) (i : I)
    (previous : ∀ j, j < i → Condition κ) : I → Condition κ := by
  classical
  exact fun j => if h : j < i then previous j h else p

/-- The recursion is defined even before its chain invariant is proved:
`amalgam` is an actual small condition for any indexed family. -/
private def decisionRun (hκ : κ.IsRegular) (hI : Cardinal.mk I < κ)
    (p : Condition κ) (b : I → Values κ) : I → Condition κ :=
  wellFounded_lt.fix (fun i previous =>
    decide (amalgam hκ hI (earlier p i previous)) (b i))

private theorem decisionRun_eq (hκ : κ.IsRegular) (hI : Cardinal.mk I < κ)
    (p : Condition κ) (b : I → Values κ) (i : I) :
    decisionRun hκ hI p b i =
      decide (amalgam hκ hI
        (earlier p i (fun j _ => decisionRun hκ hI p b j))) (b i) :=
  WellFounded.fix_eq _ _ _

/-- The recursively built conditions extend the initial condition and
every earlier stage, and decide their assigned Boolean values. -/
private theorem decisionRun_spec (hκ : κ.IsRegular) (hI : Cardinal.mk I < κ)
    (p : Condition κ) (b : I → Values κ) :
    ∀ i, decisionRun hκ hI p b i ≤ p ∧
      (∀ j, j < i → decisionRun hκ hI p b i ≤ decisionRun hκ hI p b j) ∧
      (∃ v : Bool, cone (decisionRun hκ hI p b i) ≤ bitValue (b i) v) := by
  classical
  intro i
  refine wellFounded_lt.induction
    (C := fun j : I => decisionRun hκ hI p b j ≤ p ∧
      (∀ k, k < j → decisionRun hκ hI p b j ≤ decisionRun hκ hI p b k) ∧
      (∃ v : Bool, cone (decisionRun hκ hI p b j) ≤ bitValue (b j) v)) i ?_
  intro i ih
  let f : I → Condition κ :=
    earlier p i (fun j _ => decisionRun hκ hI p b j)
  have hf : ∀ j k, f j ≤ f k ∨ f k ≤ f j := by
    intro j k
    by_cases hj : j < i
    · by_cases hk : k < i
      · simp only [f, earlier, dif_pos hj, dif_pos hk]
        rcases lt_trichotomy j k with hjk | hjk | hkj
        · exact Or.inr ((ih k hk).2.1 j hjk)
        · subst k
          exact Or.inl le_rfl
        · exact Or.inl ((ih j hj).2.1 k hkj)
      · left
        simpa only [f, earlier, dif_pos hj, dif_neg hk] using (ih j hj).1
    · by_cases hk : k < i
      · right
        simpa only [f, earlier, dif_neg hj, dif_pos hk] using (ih k hk).1
      · simp only [f, earlier, dif_neg hj, dif_neg hk]
        exact Or.inl le_rfl
  have hu (j : I) : amalgam hκ hI f ≤ f j :=
    amalgam_le hκ hI f (fun j k => compatible_of_comparable (hf j k)) j
  have hr : decisionRun hκ hI p b i ≤ amalgam hκ hI f := by
    rw [decisionRun_eq]
    exact decide_le _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [f, earlier, dif_neg (lt_irrefl i)] using hr.trans (hu i)
  · intro j hj
    simpa only [f, earlier, dif_pos hj] using hr.trans (hu j)
  · rw [decisionRun_eq]
    exact decide_spec _ _

end WellOrdered

/-- An actual common refinement decides the entire small Boolean table.
The empty index type is included. -/
theorem small_decision_refinement (hκ : κ.IsRegular) (hI : Cardinal.mk I < κ)
    (p : Condition κ) (b : I → Values κ) :
    ∃ q : Condition κ, q ≤ p ∧
      ∃ η : I → Bool, ∀ i, cone q ≤ bitValue (b i) (η i) := by
  classical
  by_cases hne : Nonempty I
  · obtain ⟨ord, wf⟩ := exists_wellFoundedLT I
    letI : LinearOrder I := ord
    letI : WellFoundedLT I := wf
    let r : I → Condition κ := decisionRun hκ hI p b
    have hs (i : I) := decisionRun_spec hκ hI p b i
    have hc : ∀ i j, Compatible (r i) (r j) := by
      intro i j
      apply compatible_of_comparable
      rcases lt_trichotomy i j with hij | hij | hji
      · exact Or.inr ((hs j).2.1 i hij)
      · subst j
        exact Or.inl le_rfl
      · exact Or.inl ((hs i).2.1 j hji)
    let q := amalgam hκ hI r
    have hq (i : I) : q ≤ r i := amalgam_le hκ hI r hc i
    let η : I → Bool := fun i => Classical.choose (hs i).2.2
    obtain ⟨i₀⟩ := hne
    refine ⟨q, (hq i₀).trans (hs i₀).1, η, ?_⟩
    intro i
    exact (ConditionCompletion.cone_mono (Condition κ) (hq i)).trans
      (Classical.choose_spec (hs i).2.2)
  · refine ⟨p, le_rfl, (fun _ => false), ?_⟩
    intro i
    exact False.elim (hne ⟨i⟩)

/-- The concrete completion satisfies binary distributivity for every
index type of cardinality less than regular κ. -/
theorem binary_distributivity (hκ : κ.IsRegular) (hI : Cardinal.mk I < κ)
    (b : I → Values κ) :
    (⨆ η : I → Bool, ⨅ i, bitValue (b i) (η i)) = ⊤ := by
  classical
  let J : Values κ := ⨆ η : I → Bool, ⨅ i, bitValue (b i) (η i)
  change J = ⊤
  by_contra hJ
  have hcompl : Jᶜ ≠ ⊥ := fun h => hJ (compl_eq_bot.mp h)
  obtain ⟨p, hp⟩ := ConditionCompletion.dense_cone (Condition κ) Jᶜ hcompl
  obtain ⟨q, hqp, η, hη⟩ := small_decision_refinement hκ hI p b
  have hqJ : cone q ≤ J :=
    (le_iInf hη).trans (le_iSup (fun η : I → Bool => ⨅ i, bitValue (b i) (η i)) η)
  have hqcompl : cone q ≤ Jᶜ :=
    (ConditionCompletion.cone_mono (Condition κ) hqp).trans hp
  have hqbot : cone q ≤ (⊥ : Values κ) :=
    (le_inf hqJ hqcompl).trans_eq (inf_compl_self J)
  exact ConditionCompletion.cone_ne_bot (Condition κ) q (bot_unique hqbot)

end

end Classicism.Meta.ChoiceBoolean.ColumnDistributivity
