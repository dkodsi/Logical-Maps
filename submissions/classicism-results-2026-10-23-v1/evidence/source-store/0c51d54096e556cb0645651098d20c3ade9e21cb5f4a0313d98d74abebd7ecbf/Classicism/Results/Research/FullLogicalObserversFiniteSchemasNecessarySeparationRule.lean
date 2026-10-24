import Classicism.Results.Research.FullLogicalObserversFiniteSchemasRuleSubstitution

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

/- Convert the closed universal rule before substituting an arbitrary
qualification. This retains the precise original premise and conclusion. -/
noncomputable def necessaryFiniteSeparationBody :
    Formula Signature.pure [Ty.rel QualificationType] :=
  Term.imp C5Condition.term.weaken
    (Term.imp AtomicCondition.term.weaken
      (Term.imp (Term.box (.app AtomQualification.term.weaken Term.v0))
        (Term.box (.app SeparationCondition.term.weaken Term.v0))))

theorem necessaryFiniteSeparationBody_instantiate
    (X : Term Signature.pure [] QualificationType) :
    necessaryFiniteSeparationBody.instantiate X =
      Term.imp C5Condition.term
        (Term.imp AtomicCondition.term
          (Term.imp (Term.box (.app AtomQualification.term X))
            (Term.box (.app SeparationCondition.term X)))) := by
  simp only [necessaryFiniteSeparationBody, Term.instantiate_weaken,
    RuleSubstitution.instantiate_app, RuleSubstitution.instantiate_var]
  rfl

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before necessary_finite_separation_rule_universal"
  err.flush : IO Unit)

set_option maxHeartbeats 2000000 in
theorem necessary_finite_separation_rule_universal {Ax : AxiomSet Signature.pure} :
    Theorem (C.axioms ∪ Ax) (Term.forall' necessaryFiniteSeparationBody) := by
  finite_observer_convert (Theorem.ofCMinus qualified_necessary_separation.derivable)

/-- Specialize by substitution, with no normalization of the supplied X. -/
theorem necessary_finite_separation_rule {Ax : AxiomSet Signature.pure}
    (X : Term Signature.pure [] QualificationType) :
    Theorem (C.axioms ∪ Ax)
      (Term.imp C5Condition.term
        (Term.imp AtomicCondition.term
          (Term.imp (Term.box (.app AtomQualification.term X))
            (Term.box (.app SeparationCondition.term X))))) := by
  simpa only [necessaryFiniteSeparationBody_instantiate] using
    (Derivable.allEβ (necessary_finite_separation_rule_universal (Ax := Ax)) X)

#print axioms necessary_finite_separation_rule_universal
#print axioms necessary_finite_separation_rule

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: NecessarySeparationRule commands complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
