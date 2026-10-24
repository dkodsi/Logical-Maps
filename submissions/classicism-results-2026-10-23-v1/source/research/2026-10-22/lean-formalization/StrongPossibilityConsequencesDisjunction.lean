import StrongPossibilityConsequencesUniversalCore
import StrongPossibilityConsequencesReflection

/-!
# The restricted finite-disjunction criterion for SP consistency

Source: notes/reflection-universal-core-20261022.md §§5–7 and
notes/sp-failed-disjunction-20261022.md §17 (session deduction, misc).

The disjunction of the negated universal sentences is spelled not(and L),
including not(top) for the empty list. Thus the theorem is exact about the
existing finitary syntax and its actual derivations. It is a criterion, not a
proof that the criterion holds. Original Max consistency remains an explicit
known-but-not-yet-model-certified library input. No SP model is assumed.
-/

namespace Classicism.Meta.Research.StrongPossibilityConsequences.Disjunction

open AxiomSet
open UniversalCore
open Reflection

variable {Sig : Signature}

private theorem negate_of_inconsistent_extension {Ax : AxiomSet Sig} {p : Sentence Sig}
    (hbot : Theorem (C.axioms ∪ (Ax ∪ single p)) Term.bot) :
    Theorem (C.axioms ∪ Ax) (Term.neg p) :=
  Derivable.notI
    (Derivable.impE (Derivable.weaken₁ (Theorem.deductionC hbot)) Derivable.hyp₀)
    (Derivable.notI (Derivable.andE₁ Derivable.hyp₀) (Derivable.andE₂ Derivable.hyp₀))

theorem consistent_add_iff_not_neg {Ax : AxiomSet Sig} (p : Sentence Sig) :
    Consistent (Ax ∪ single p) ↔ ¬ Theorem (C.axioms ∪ Ax) (Term.neg p) := by
  constructor
  · intro hcon hn
    apply hcon
    exact Derivable.notE (Theorem.ax (Or.inr rfl))
      (Derivable.mono (fun _ ha => ha.elim Or.inl (fun h => Or.inr (Or.inl h))) hn)
  · intro hn hbot
    exact hn (negate_of_inconsistent_extension hbot)

def UniversalSentence (p : Sentence Sig) : Prop :=
  p.closedTypes = true ∧ ∃ u : Universal Sig [], p = u.formula

/-- Restricted disjunction property for the negations of the actual universal
identity grammar. Every list and every object formula here is finite. -/
def RestrictedDisjunction (Sig : Signature) : Prop :=
  ∀ L : List (Sentence Sig), (∀ a ∈ L, UniversalSentence a) →
    Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) (Term.neg (conjunction L)) →
    ∃ a ∈ L, Theorem (C.axioms ∪ (maximalist : AxiomSet Sig)) (Term.neg a)

theorem restricted_disjunction_of_core_consistent
    (hM : Consistent (maximalist : AxiomSet Sig))
    (hcore : Consistent (universalMaxConsistent Sig)) : RestrictedDisjunction Sig := by
  classical
  intro L hL hneg
  apply Classical.byContradiction
  intro hnone
  have htheorems : ∀ a ∈ L, Theorem (C.axioms ∪ universalMaxConsistent Sig) a := by
    intro a ha
    obtain ⟨hc, u, hu⟩ := hL a ha
    have hcon : Consistent (maximalist ∪ single a) :=
      (consistent_add_iff_not_neg a).mpr (fun hn => hnone ⟨a, ha, hn⟩)
    exact Theorem.ax ⟨hc, u, hu, hcon⟩
  have hmax : universalMaxConsistent Sig ⟹ maximalist :=
    Entails.trans universal_core_entails_sp (strongPossibility_entails_maximalist hM)
  exact hcore (Derivable.notE (conjunction_intro L htheorems) (Derivable.cut hmax hneg))

theorem core_consistent_of_restricted_disjunction
    (hdisj : RestrictedDisjunction Sig) : Consistent (universalMaxConsistent Sig) := by
  intro hbot
  obtain ⟨L, hL, hd⟩ := FiniteChoiceBasis.finiteSupport hbot
  have hcut : single (conjunction L) ⟹ FiniteChoiceBasis.ofList L := by
    intro a ha
    have hconjunction : Theorem (C.axioms ∪ single (conjunction L)) (conjunction L) :=
      Theorem.ax rfl
    exact conjunction_elim L hconjunction a ha
  have himp : C.Theorem (Term.imp (conjunction L) Term.bot) :=
    Theorem.deduction (fun h => h) (Derivable.cut hcut hd)
  have hn : C.Theorem (Term.neg (conjunction L)) :=
    Derivable.notI (Derivable.impE (Derivable.weaken₁ himp) Derivable.hyp₀)
      (Derivable.notI (Derivable.andE₁ Derivable.hyp₀) (Derivable.andE₂ Derivable.hyp₀))
  have hU : ∀ a ∈ L, UniversalSentence a := by
    intro a ha
    obtain ⟨hc, u, hu, _⟩ := hL a ha
    exact ⟨hc, u, hu⟩
  obtain ⟨a, ha, hna⟩ := hdisj L hU (Theorem.ofC hn)
  obtain ⟨_, _, _, hcon⟩ := hL a ha
  exact (consistent_add_iff_not_neg a).mp hcon hna

theorem core_consistent_iff_restricted_disjunction
    (hM : Consistent (maximalist : AxiomSet Sig)) :
    Consistent (universalMaxConsistent Sig) ↔ RestrictedDisjunction Sig :=
  ⟨restricted_disjunction_of_core_consistent hM, core_consistent_of_restricted_disjunction⟩

/-- An exact criterion for original finitary SP; its right-hand side has not
been proved globally and is not silently treated as an axiom. -/
theorem sp_consistent_iff_restricted_disjunction
    (hM : Consistent (maximalist : AxiomSet Sig)) :
    Consistent (strongPossibility Sig) ↔ RestrictedDisjunction Sig :=
  sp_consistent_iff_universal_core.trans (core_consistent_iff_restricted_disjunction hM)

#print axioms consistent_add_iff_not_neg
#print axioms restricted_disjunction_of_core_consistent
#print axioms core_consistent_of_restricted_disjunction
#print axioms core_consistent_iff_restricted_disjunction
#print axioms sp_consistent_iff_restricted_disjunction

end Classicism.Meta.Research.StrongPossibilityConsequences.Disjunction
