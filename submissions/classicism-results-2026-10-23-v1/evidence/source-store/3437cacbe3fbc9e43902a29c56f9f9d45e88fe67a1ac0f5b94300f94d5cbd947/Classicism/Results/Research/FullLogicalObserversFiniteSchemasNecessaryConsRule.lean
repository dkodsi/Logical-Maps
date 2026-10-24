import Classicism.Results.Research.FullLogicalObserversFiniteSchemasRuleSubstitution

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

/- Convert the closed universal rule before substituting an arbitrary
qualification. This retains the precise original premise and conclusion. -/
noncomputable def qualifiedNecessaryConsBody (σ : Ty) :
    Formula Signature.pure [Ty.rel QualificationType] :=
  Term.imp C5Condition.term.weaken
    (Term.imp (Term.box (.app AtomQualification.term.weaken Term.v0))
      (Term.box (.app AtomQualification.term.weaken
        (.app (.app ConjoinQualification.term.weaken
          (QuantifierCondition.term σ).weaken) Term.v0))))

theorem qualifiedNecessaryConsBody_instantiate (σ : Ty)
    (X : Term Signature.pure [] QualificationType) :
    (qualifiedNecessaryConsBody σ).instantiate X =
      Term.imp C5Condition.term
        (Term.imp (Term.box (.app AtomQualification.term X))
          (Term.box (.app AtomQualification.term
            (.app (.app ConjoinQualification.term (QuantifierCondition.term σ)) X)))) := by
  simp only [qualifiedNecessaryConsBody, Term.instantiate_weaken,
    RuleSubstitution.instantiate_app, RuleSubstitution.instantiate_var]
  rfl

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before qualified_necessary_cons_rule_universal"
  err.flush : IO Unit)

set_option maxHeartbeats 2000000 in
theorem qualified_necessary_cons_rule_universal {Ax : AxiomSet Signature.pure} (σ : Ty) :
    Theorem (C.axioms ∪ Ax) (Term.forall' (qualifiedNecessaryConsBody σ)) := by
  finite_observer_convert (Theorem.ofCMinus (c5_necessary_qualified_cons.derivable σ))

/-- Specialize by substitution, with no normalization of the supplied X. -/
theorem qualified_necessary_cons_rule {Ax : AxiomSet Signature.pure} (σ : Ty)
    (X : Term Signature.pure [] QualificationType) :
    Theorem (C.axioms ∪ Ax)
      (Term.imp C5Condition.term
        (Term.imp (Term.box (.app AtomQualification.term X))
          (Term.box (.app AtomQualification.term
            (.app (.app ConjoinQualification.term (QuantifierCondition.term σ)) X))))) := by
  simpa only [qualifiedNecessaryConsBody_instantiate] using
    (Derivable.allEβ (qualified_necessary_cons_rule_universal (Ax := Ax) σ) X)

#print axioms qualified_necessary_cons_rule_universal
#print axioms qualified_necessary_cons_rule

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: NecessaryConsRule commands complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
