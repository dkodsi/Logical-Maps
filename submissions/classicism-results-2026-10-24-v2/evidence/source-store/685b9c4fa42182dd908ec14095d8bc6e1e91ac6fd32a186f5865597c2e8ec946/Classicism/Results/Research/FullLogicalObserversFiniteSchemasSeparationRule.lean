import Classicism.Results.Research.FullLogicalObserversFiniteSchemasRuleSubstitution

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

/- Convert the closed universal rule before substituting an arbitrary
qualification. This retains the precise original premise and conclusion. -/
noncomputable def finiteSeparationBody :
    Formula Signature.pure [Ty.rel QualificationType] :=
  Term.imp AtomicCondition.term.weaken
    (Term.imp (.app AtomQualification.term.weaken Term.v0)
      (.app SeparationCondition.term.weaken Term.v0))

theorem finiteSeparationBody_instantiate
    (X : Term Signature.pure [] QualificationType) :
    finiteSeparationBody.instantiate X =
      Term.imp AtomicCondition.term
        (Term.imp (.app AtomQualification.term X) (.app SeparationCondition.term X)) := by
  simp only [finiteSeparationBody, Term.instantiate_weaken,
    RuleSubstitution.instantiate_app, RuleSubstitution.instantiate_var]
  rfl

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before finite_separation_rule_universal"
  err.flush : IO Unit)

set_option maxHeartbeats 2000000 in
theorem finite_separation_rule_universal {Ax : AxiomSet Signature.pure} :
    Theorem (C.axioms ∪ Ax) (Term.forall' finiteSeparationBody) := by
  finite_observer_convert (Theorem.ofCMinus qualified_separation.derivable)

/-- Specialize by substitution, with no normalization of the supplied X. -/
theorem finite_separation_rule {Ax : AxiomSet Signature.pure}
    (X : Term Signature.pure [] QualificationType) :
    Theorem (C.axioms ∪ Ax)
      (Term.imp AtomicCondition.term
        (Term.imp (.app AtomQualification.term X) (.app SeparationCondition.term X))) := by
  simpa only [finiteSeparationBody_instantiate] using
    (Derivable.allEβ (finite_separation_rule_universal (Ax := Ax)) X)

#print axioms finite_separation_rule_universal
#print axioms finite_separation_rule

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: SeparationRule commands complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
