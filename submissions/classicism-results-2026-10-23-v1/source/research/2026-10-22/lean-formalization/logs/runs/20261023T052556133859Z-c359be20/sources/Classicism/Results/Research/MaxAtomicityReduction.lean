import Classicism.Syntax.SentenceSchemas
import Classicism.Certified.Schemas

/-!
# CONDITIONAL Maximalism/Atomicity reduction

Direct source: `research/2026-10-22/followup/max-atomicity-selector-audit.md`, §§8–9.
This module composes actual object-language derivations. Its hypotheses explicitly
include the missing non-theorem certificate and the Atomicity zero-identity derivation.
It does NOT construct a separating sentence or certify the proposed inconsistency.
No axiom postulates the rigid Boolean algebra, coding, or a selector.
-/

namespace Classicism.Meta.Research.MaxAtomicityReduction

open AxiomSet

/-- Max(C) contains the negation of a pure closed identity not provable in C.
The reference theory stays C, not C plus the proposed extra premises. -/
theorem maximalist_has_nonidentity {σ : Ty} {x y : Term Signature.pure [] σ}
    (hclosed : (Term.eq' x y).closedTypes = true)
    (hnot : ¬ C.Theorem (Term.eq' x y)) :
    maximalist (Term.neg (Term.eq' x y)) := by
  apply Or.inr
  apply distinctness_mem hclosed
  intro h
  apply hnot
  exact Derivable.mono (fun _ ha => ha.elim id False.elim) h

/-- A reusable conditional inconsistency criterion. Both the non-theorem
certificate and the derivation under Ax are inputs; neither is postulated. -/
theorem inconsistent_of_forced_identity (Ax : AxiomSet Signature.pure)
    {σ : Ty} {x y : Term Signature.pure [] σ}
    (hclosed : (Term.eq' x y).closedTypes = true)
    (hnot : ¬ C.Theorem (Term.eq' x y))
    (hforced : Theorem (C.axioms ∪ Ax) (Term.eq' x y)) :
    ¬ Consistent (maximalist ∪ Ax) := by
  intro hc
  have hn : Theorem (C.axioms ∪ (maximalist ∪ Ax))
      (Term.neg (Term.eq' x y)) :=
    Theorem.ax (Or.inl (maximalist_has_nonidentity hclosed hnot))
  have he : Theorem (C.axioms ∪ (maximalist ∪ Ax)) (Term.eq' x y) :=
    Derivable.mono (fun _ ha => ha.elim Or.inl (fun h => Or.inr (Or.inr h))) hforced
  exact hc (Derivable.notE he hn)

/-- Exact unboxed type-t target, conditional on its two outstanding certificates.
No necessity of Atomicity, C5, or object-language Choice is present. -/
theorem atomicityT_inconsistent_of_separator (q : Sentence Signature.pure)
    (hclosed : q.closedTypes = true)
    (hnot : ¬ C.Theorem (Term.eq' q Term.bot))
    (hforced : Theorem (C.axioms ∪ P.AtomicityT.schema) (Term.eq' q Term.bot)) :
    ¬ Consistent (maximalist ∪ P.AtomicityT.schema) :=
  inconsistent_of_forced_identity P.AtomicityT.schema
    (by simpa only [Term.closedTypes_eq', Term.closedTypes_bot, Bool.and_true] using hclosed)
    hnot hforced

/-- An explicit bundle of obligations, NOT an assertion that it is inhabited. -/
structure AtomicitySeparator where
  sentence : Sentence Signature.pure
  closedTypes : sentence.closedTypes = true
  not_zero_theorem : ¬ C.Theorem (Term.eq' sentence Term.bot)
  zero_under_atomicity :
    Theorem (C.axioms ∪ P.AtomicityT.schema) (Term.eq' sentence Term.bot)

theorem AtomicitySeparator.inconsistent (s : AtomicitySeparator) :
    ¬ Consistent (maximalist ∪ P.AtomicityT.schema) :=
  atomicityT_inconsistent_of_separator s.sentence s.closedTypes
    s.not_zero_theorem s.zero_under_atomicity

end Classicism.Meta.Research.MaxAtomicityReduction

#print axioms Classicism.Meta.Research.MaxAtomicityReduction.maximalist_has_nonidentity
#print axioms Classicism.Meta.Research.MaxAtomicityReduction.inconsistent_of_forced_identity
#print axioms Classicism.Meta.Research.MaxAtomicityReduction.atomicityT_inconsistent_of_separator
#print axioms Classicism.Meta.Research.MaxAtomicityReduction.AtomicitySeparator.inconsistent
