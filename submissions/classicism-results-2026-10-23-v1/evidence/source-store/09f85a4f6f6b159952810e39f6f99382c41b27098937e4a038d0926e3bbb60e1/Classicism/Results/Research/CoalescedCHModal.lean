import Classicism.Results.SentenceSchemas.PossibilityDistinctness
import Classicism.Tools.Translate
import Classicism.Semantics.IntensionalFacts

/-!
# The modal part of structural CH contingency

Original research, misc, Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. This is the elementary modal argument for the proposed
coalesced sum of internal ZFC+CH and ZFC+not-CH Henkin models.

The consistency witnesses are explicit premises. No model existence,
set-theoretic consistency, or CH independence is assumed as an axiom.
-/

namespace Classicism.Research.CoalescedCH

theorem two_possible_contra (p q : Prop) :
    (□ (¬ p) ∨ □ (¬ q)) → ◇ p → ◇ q → False := by
  intro hb hp hq
  exact hb.elim
    (fun h => hp (by rw [← not_not_eq p, h, not_true_eq]))
    (fun h => hq (by rw [← not_not_eq q, h, not_true_eq]))

end Classicism.Research.CoalescedCH

#classicism_derive Classicism.Research.CoalescedCH.two_possible_contra

namespace Classicism.Meta.Research.CoalescedCH

open AxiomSet

variable {Sig : Signature}

/-- The disjunction ruled out by two independently consistent witnesses. -/
def eitherBoxNeg (p q : Sentence Sig) : Sentence Sig :=
  Term.disj (Term.box (Term.neg p)) (Term.box (Term.neg q))

theorem possibility_two_inconsistent (p q : Sentence Sig)
    (hpClosed : p.closedTypes = true) (hqClosed : q.closedTypes = true)
    (hp : Consistent (single p)) (hq : Consistent (single q)) :
    ¬ Consistent (possibility (empty : AxiomSet Sig) ∪ single (eitherBoxNeg p q)) := by
  intro hc
  apply hc
  have hd₁ : Theorem (C.axioms ∪
      (possibility (empty : AxiomSet Sig) ∪ single (eitherBoxNeg p q))) (Term.dia p) :=
    Theorem.ax (Or.inl (possibility_mem hpClosed (Consistent.empty_union hp)))
  have hd₂ : Theorem (C.axioms ∪
      (possibility (empty : AxiomSet Sig) ∪ single (eitherBoxNeg p q))) (Term.dia q) :=
    Theorem.ax (Or.inl (possibility_mem hqClosed (Consistent.empty_union hq)))
  have hb : Theorem (C.axioms ∪
      (possibility (empty : AxiomSet Sig) ∪ single (eitherBoxNeg p q)))
      (eitherBoxNeg p q) := Theorem.ax (Or.inr rfl)
  exact Derivable.notE hd₂ (Theorem.mp (Theorem.mp (Derivable.allE₂β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure
      Classicism.Research.CoalescedCH.two_possible_contra.derivable)) p q) hb) hd₁)

theorem distinctness_two_inconsistent (p q : Sentence Sig)
    (hpClosed : p.closedTypes = true) (hqClosed : q.closedTypes = true)
    (hp : Consistent (single p)) (hq : Consistent (single q)) :
    ¬ Consistent (distinctness (empty : AxiomSet Sig) ∪ single (eitherBoxNeg p q)) := by
  intro hc
  exact possibility_two_inconsistent p q hpClosed hqClosed hp hq
    (Consistent.of_entails
      (Entails.union
        (Entails.mono_left (subset_union_left _ _) (distinctness_entails_possibility empty))
        (Entails.union_right _ _)) hc)

theorem maximalism_two_inconsistent (p q : Sentence Sig)
    (hpClosed : p.closedTypes = true) (hqClosed : q.closedTypes = true)
    (hp : Consistent (single p)) (hq : Consistent (single q)) :
    ¬ Consistent (maximalist (Sig := Sig) ∪ single (eitherBoxNeg p q)) := by
  intro hc
  exact possibility_two_inconsistent p q hpClosed hqClosed hp hq
    (Consistent.of_entails
      (Entails.union
        (Entails.mono_left (subset_union_left _ _) maximalist_entails_possibility)
        (Entails.union_right _ _)) hc)

open CategoryTheory Intensional

/-- Opposite structural witnesses at accessible objects refute the modal
disjunction. The witnesses need not occur at the same object. -/
theorem not_holds_eitherBoxNeg_of_accessible
    {K : Type} [SmallCategory K] (A : Premodel Sig K) (hA : A.IsModel)
    (p q : Sentence Sig) {W V : K} (u : A.W₀ ⟶ W) (v : A.W₀ ⟶ V)
    (hp : A.Holds u p .nil) (hq : A.Holds v q .nil) :
    ¬ A.HoldsSentence (eitherBoxNeg p q) := by
  intro h
  rcases (A.holds_disj hA (𝟙 A.W₀) .nil _ _).1 h with h | h
  · have hn := (A.holds_box hA (𝟙 A.W₀) (Term.neg p) .nil).1 h u
    rw [Category.id_comp, IEnv.nil_eq (A.push u .nil)] at hn
    exact (A.holds_neg hA u .nil p).1 hn hp
  · have hn := (A.holds_box hA (𝟙 A.W₀) (Term.neg q) .nil).1 h v
    rw [Category.id_comp, IEnv.nil_eq (A.push v .nil)] at hn
    exact (A.holds_neg hA v .nil q).1 hn hq

#print axioms possibility_two_inconsistent
#print axioms distinctness_two_inconsistent
#print axioms maximalism_two_inconsistent
#print axioms not_holds_eitherBoxNeg_of_accessible

end Classicism.Meta.Research.CoalescedCH
