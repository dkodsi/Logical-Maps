import Classicism.Results.Research.AnalyticTupleDomainsMeta
import Classicism.Results.Research.AnalyticPowerExistenceCertificates
import Classicism.Certified.Schemas

noncomputable section

namespace Classicism.Meta.Analytic

open AxiomSet

abbrev Premises : AxiomSet Signature.pure :=
  P.NecNecessityOfDistinctness.schema ∪ P.NecRigidComprehension.schema

abbrev Ax : AxiomSet Signature.pure := C.axioms ∪ Premises

def incl (ρ : RTy) {Γ : Ctx} (D E : Term Signature.pure Γ ρ) :
    Formula Signature.pure Γ := .app (.app (.inclR ρ) D) E

def rigid (ρ : RTy) {Γ : Ctx} (D : Term Signature.pure Γ ρ) :
    Formula Signature.pure Γ :=
  Term.conj (persist ρ D) (Term.box (Term.forall'
    (Term.imp (incl ρ D.weaken (.app (.boxR ρ) Term.v0))
      (Term.box (incl ρ D.weaken Term.v0)))))

/-- The expanded unary form used by the checked shallow-to-deep quotation. -/
def rigidUnary (σ : Ty) {Γ : Ctx} (X : Term Signature.pure Γ (σ ⇒ RTy.t)) :
    Formula Signature.pure Γ :=
  Term.conj (persistUnary σ X) (Term.box (Term.forall'
    (Term.imp
      (Term.forall' (Term.imp (.app X.weaken.weaken Term.v0)
        (Term.box (.app Term.v1 Term.v0))))
      (Term.box (Term.forall' (Term.imp (.app X.weaken.weaken Term.v0)
        (.app Term.v1 Term.v0)))))))

def represented (ρ : RTy) {Γ : Ctx} (D : Term Signature.pure Γ ρ)
    (P : Term Signature.pure Γ (ρ ⇒ RTy.t)) : Formula Signature.pure Γ :=
  Term.conj (rigidUnary ρ P) (Term.conj
    (Term.forall' (Term.imp (.app P.weaken Term.v0)
      (Term.conj (rigid ρ Term.v0) (incl ρ Term.v0 D.weaken))))
    (Term.box (Term.forall' (Term.exists' (Term.conj
      (.app P.weaken.weaken Term.v0)
      (.app (.app (.coextR ρ) (.app (.app (.andR ρ) Term.v0) D.weaken.weaken))
        (.app (.app (.andR ρ) Term.v1) D.weaken.weaken)))))))

def hasPower (ρ : RTy) {Γ : Ctx} (D : Term Signature.pure Γ ρ) :
    Formula Signature.pure Γ :=
  Term.exists' (represented ρ D.weaken Term.v0)

theorem c5 : Theorem Ax (P.NecNecessityOfDistinctness.quoted RTy.t) :=
  Theorem.ax (Or.inl ⟨RTy.t, by trivial, rfl⟩)

theorem necessaryRC (ρ : RTy) (hρ : ρ.Closed) :
    Theorem Ax (P.NecRigidComprehension.quoted ρ) :=
  Theorem.ax (Or.inr ⟨ρ, hρ, rfl⟩)

open Lean Lean.Meta in
/-- Read a closed pure-language certificate without changing its axiom set. -/
private def closedCertificateParts (ty : Expr) : MetaM (Expr × Expr) := do
  let ty ← whnf (← instantiateMVars ty)
  let (``Classicism.Meta.Derivable, #[sig, ax, ctx, hyps, p]) := ty.getAppFnArgs
    | throwError "analytic conversion: expected a closed derivation"
  unless ← isDefEq sig (mkConst ``Signature.pure) do
    throwError "analytic conversion: expected the pure signature"
  unless (← whnf ctx).isAppOfArity ``List.nil 1 do
    throwError "analytic conversion: the object context must be empty"
  unless (← whnf hyps).isAppOfArity ``List.nil 1 do
    throwError "analytic conversion: the hypothesis list must be empty"
  pure (ax, p)

syntax (name := analyticConvertClosed) "analytic_convert_closed " term : tactic

open Lean Lean.Meta Lean.Elab.Tactic in
/-- Use the existing schema converter on a closed premise, before context
weakening. It supplies actual delta/beta/eta conversion certificates. -/
@[tactic analyticConvertClosed] private def evalAnalyticConvertClosed : Tactic :=
    fun stx => withMainContext do
  let goal ← getMainGoal
  let (target, expected) ← closedCertificateParts (← goal.getType)
  let d ← Lean.Elab.Term.elabTerm stx[1] none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let d ← instantiateMVars d
  let (actual, got) ← closedCertificateParts (← inferType d)
  unless ← isDefEq actual target do
    throwError "analytic conversion: the axiom sets differ"
  if (← getOptions).getBool `Classicism.Meta.Translate.convAxiom false then
    throwError "analytic conversion: axiom-based debug conversion is disabled"
  let value ← instantiateMVars (← convertDeriv target d got expected)
  if value.hasMVar || value.hasSorry then
    throwError "analytic conversion: the conversion certificate is incomplete"
  goal.assign value
  replaceMainGoal []

theorem hasPower_rule (ρ : RTy) (hρ : ρ.Closed) {Γ : Ctx}
    {Δ : List (Formula Signature.pure Γ)} (D : Term Signature.pure Γ ρ)
    (hD : Derivable Ax Δ (persist ρ D)) : Derivable Ax Δ (hasPower ρ D) := by
  -- Normalize the closed quoted boundary before substituting an arbitrary D.
  have rule : Theorem Ax
      (Term.forall' (σ := ρ) (Term.imp (persist ρ Term.v0) (hasPower ρ Term.v0))) :=
    Derivable.conv
      (Derivable.impE (Derivable.impE
        (Theorem.ofCMinus (Classicism.Research.Analytic.exists_represented_power.derivable ρ))
        c5) (necessaryRC ρ hρ))
      (Conv.of_nf_left 3 _ _ rfl)
  exact Derivable.impE (Derivable.allEβ (Derivable.ofTheorem rule) D) hD

theorem rigid_real_rule (σ : Ty) (hσ : σ.Closed) {Γ : Ctx}
    {Δ : List (Formula Signature.pure Γ)}
    (h : Derivable Ax Δ (Term.dia (Classicism.Research.Analytic.HasReal.term σ).close)) :
    Derivable Ax Δ (Classicism.Research.Analytic.HasRigidReal.term σ).close := by
  have rule : Theorem Ax (Term.imp
      (Term.dia (Classicism.Research.Analytic.HasReal.term σ))
      (Classicism.Research.Analytic.HasRigidReal.term σ)) := by
    refine Derivable.impE (Derivable.impE (Derivable.impE (Derivable.impE
      (Theorem.ofCMinus (Classicism.Research.Analytic.rigidify_possible.derivable σ))
      c5) ?_) ?_) ?_
    · analytic_convert_closed (necessaryRC (σ ⇒ RTy.t) ⟨hσ, trivial⟩)
    · analytic_convert_closed (necessaryRC (σ ⇒ σ ⇒ RTy.t) ⟨hσ, hσ, trivial⟩)
    · analytic_convert_closed
        (necessaryRC (σ ⇒ σ ⇒ σ ⇒ RTy.t) ⟨hσ, hσ, hσ, trivial⟩)
  exact Derivable.impE (Derivable.ofTheorem rule) h

theorem tuple_hasPower (σ : Ty) (hσ : σ.Closed) (k : Nat) {Γ : Ctx}
    {Δ : List (Formula Signature.pure Γ)} (X : Term Signature.pure Γ (σ ⇒ RTy.t))
    (hX : Derivable Ax Δ (persist (σ ⇒ RTy.t) X)) :
    Derivable Ax Δ (hasPower (relArity σ k) (domain σ k X)) :=
  hasPower_rule _ (relArity_closed σ hσ k) _ (Derivable.impE
    (Derivable.weaken (Derivable.mono (fun _ h => False.elim h)
      (domain_persistence_imp σ k X)) (List.nil_subset _)) hX)

end Classicism.Meta.Analytic

#print axioms Classicism.Meta.Analytic.hasPower_rule
#print axioms Classicism.Meta.Analytic.rigid_real_rule
