import Classicism.Results.Research.FullLogicalObserversFiniteSchemasBase
import Classicism.Tools.Schema

set_option Elab.async false
set_option stderrAsMessages false

namespace Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
open AxiomSet
open Classicism.Research.FullLogicalObservers.FiniteQualification

/- The existing schema converter builds kernel-checked congruence and one-sided
normalization certificates against concrete syntax trees. Apply it before the
arbitrary recursive qualification is substituted under the formula's binders. -/
open Lean Lean.Meta in
private def closedRuleParts (ty : Expr) : MetaM (Expr × Expr) := do
  let ty ← whnf (← instantiateMVars ty)
  let (``Classicism.Meta.Derivable, #[sig, ax, ctx, hyps, p]) := ty.getAppFnArgs
    | throwError "finite observer conversion: expected a closed derivation"
  unless ← isDefEq sig (mkConst ``Signature.pure) do
    throwError "finite observer conversion: expected the pure signature"
  unless (← whnf ctx).isAppOfArity ``List.nil 1 do
    throwError "finite observer conversion: the object context must be empty"
  unless (← whnf hyps).isAppOfArity ``List.nil 1 do
    throwError "finite observer conversion: the hypothesis list must be empty"
  pure (ax, p)

syntax (name := finiteObserverConvert) "finite_observer_convert " term : tactic

open Lean Lean.Meta Lean.Elab.Tactic in
@[tactic finiteObserverConvert] private def evalFiniteObserverConvert : Tactic :=
    fun stx => withMainContext do
  let goal ← getMainGoal
  let (target, expected) ← closedRuleParts (← goal.getType)
  let d ← Lean.Elab.Term.elabTerm stx[1] none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let d ← instantiateMVars d
  let (actual, got) ← closedRuleParts (← inferType d)
  unless ← isDefEq actual target do
    throwError "finite observer conversion: the axiom sets differ"
  if (← getOptions).getBool `Classicism.Meta.Translate.convAxiom false then
    throwError "finite observer conversion: axiom-based debug conversion is disabled"
  let value ← instantiateMVars (← convertDeriv target d got expected)
  if value.hasMVar || value.hasSorry then
    throwError "finite observer conversion: incomplete conversion certificate"
  goal.assign value
  replaceMainGoal []

/-- The induction step with its qualification still an object-language variable. -/
noncomputable def qualifiedConsBody (σ : Ty) :
    Formula Signature.pure [Ty.rel QualificationType] :=
  Term.imp C5Condition.term.weaken
    (Term.imp (.app AtomQualification.term.weaken Term.v0)
      (.app AtomQualification.term.weaken
        (.app (.app ConjoinQualification.term.weaken
          (QuantifierCondition.term σ).weaken) Term.v0)))

private theorem instantiate_imp {Γ : Ctx} {τ : Ty}
    (p q : Formula Signature.pure (τ :: Γ)) (a : Term Signature.pure Γ τ) :
    (Term.imp p q).instantiate a =
      Term.imp (p.instantiate a) (q.instantiate a) := rfl

private theorem instantiate_app {Γ : Ctx} {τ σ : Ty} {ρ : RTy}
    (f : Term Signature.pure (τ :: Γ) (σ ⇒ ρ))
    (x : Term Signature.pure (τ :: Γ) σ) (a : Term Signature.pure Γ τ) :
    (Term.app f x).instantiate a =
      Term.app (f.instantiate a) (x.instantiate a) := rfl

private theorem instantiate_var {Γ : Ctx} {τ : Ty}
    (a : Term Signature.pure Γ τ) :
    (Term.var (.zero : Var (τ :: Γ) τ)).instantiate a = a := rfl

theorem qualifiedConsBody_instantiate (σ : Ty)
    (X : Term Signature.pure [] QualificationType) :
    (qualifiedConsBody σ).instantiate X =
      Term.imp C5Condition.term
        (Term.imp (.app AtomQualification.term X)
          (.app AtomQualification.term
            (.app (.app ConjoinQualification.term (QuantifierCondition.term σ)) X))) := by
  simp only [qualifiedConsBody, Term.instantiate_weaken, instantiate_app, instantiate_var]
  rfl

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: before closed cons rule conversion"
  err.flush : IO Unit)

set_option maxHeartbeats 2000000 in
theorem qualified_cons_rule_universal {Ax : AxiomSet Signature.pure} (σ : Ty) :
    Theorem (C.axioms ∪ Ax) (Term.forall' (qualifiedConsBody σ)) := by
  finite_observer_convert (Theorem.ofCMinus (c5_qualified_cons.derivable σ))

/-- Specialization uses substitution identities, without normalizing X. -/
theorem qualified_cons_rule {Ax : AxiomSet Signature.pure} (σ : Ty)
    (X : Term Signature.pure [] QualificationType) :
    Theorem (C.axioms ∪ Ax)
      (Term.imp C5Condition.term
        (Term.imp (.app AtomQualification.term X)
          (.app AtomQualification.term
            (.app (.app ConjoinQualification.term (QuantifierCondition.term σ)) X)))) := by
  simpa only [qualifiedConsBody_instantiate] using
    (Derivable.allEβ (qualified_cons_rule_universal (Ax := Ax) σ) X)

#print axioms qualified_cons_rule_universal
#print axioms qualified_cons_rule

#eval (do
  let err ← IO.getStderr
  err.putStrLn "Finite schemas: closed cons rule commands complete"
  err.flush : IO Unit)

end Classicism.Meta.Research.FullLogicalObserversFiniteSchemas
