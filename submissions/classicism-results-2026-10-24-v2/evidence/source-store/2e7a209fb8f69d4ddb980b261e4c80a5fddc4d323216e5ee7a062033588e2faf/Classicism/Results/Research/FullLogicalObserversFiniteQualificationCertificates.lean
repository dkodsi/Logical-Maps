import Classicism.Results.Research.FullLogicalObserversFiniteQualificationDerivations
import Classicism.Tools.QuoteTerm

#classicism_quote_term
  Classicism.Research.FullLogicalObservers.FiniteQualification.TrueQualification
  Classicism.Research.FullLogicalObservers.FiniteQualification.ConjoinQualification
  Classicism.Research.FullLogicalObservers.FiniteQualification.QuantifierCondition
  Classicism.Research.FullLogicalObservers.FiniteQualification.SeparationCondition
  Classicism.Research.FullLogicalObservers.FiniteQualification.AtomicCondition
  Classicism.Research.FullLogicalObservers.FiniteQualification.ActualCondition

/- Use the unchanged quoter for this one term. Its reflection is proved below
after introducing the qualification argument and reducing the environments. -/
open Lean Meta Elab Term Command in
run_cmd liftTermElabM do
  let n := ``Classicism.Research.FullLogicalObservers.FiniteQualification.AtomQualification
  let info ← getConstInfo n
  let value := Lean.mkConst n
  let quotedType ← (Classicism.Meta.Quote.quoteTy info.type).run {}
  let quoted ← (Classicism.Meta.Quote.quoteTerm
    ((← unfoldDefinition? value).getD value)).run {}
  let termType := mkApp3 (Lean.mkConst ``Classicism.Meta.Term)
    (Lean.mkConst ``Classicism.Meta.Signature.pure)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``Classicism.Meta.Ty)) quotedType
  let term ← elabTermEnsuringType quoted (some termType)
  synthesizeSyntheticMVarsNoPostponing
  let term ← instantiateMVars term
  if term.hasMVar then throwError "AtomQualification quotation has unresolved metavariables"
  let termName := n ++ Name.mkSimple "term"
  let decl : DefinitionVal := { name := termName, levelParams := [], type := termType, value := term, hints := .abbrev, safety := .safe }
  withOptions (Elab.async.set · false) do addDecl (.defnDecl decl)
  enableRealizationsForConst termName

namespace Classicism.Research.FullLogicalObservers.FiniteQualification
open Classicism.Meta

theorem AtomQualification.reflect :
    AtomQualification.term.denote (Interp.ofDomain Classicism.e) Env.nil =
      AtomQualification := by
  funext X
  dsimp only [AtomQualification.term, AtomQualification, BoolFull, PatchedPrincipal,
    Classicism.Atom, Classicism.Rel.le, Classicism.instRelProp,
    Classicism.Box, Classicism.Dia, Term.denote, Var.denote,
    Term.forall', Term.conj, Term.disj, Term.neg, Term.imp, Term.iff,
    Term.eq', Term.box, Term.dia, Term.top, Term.bot]
  -- The full function identity also rewrites the partial application under X.
  simp only [Var.denote, Classicism.Rel.or, Classicism.Rel.neg,
    patched_principal_imp, Classicism.Box, Classicism.Dia,
    Classicism.Meta.top_eq, Classicism.Meta.bot_eq,
    Classicism.Meta.imp_eq, Classicism.Meta.iff_eq']

/-- The same literal C5 formula, with its nested boxes reflected locally. The
automatic reflection simplifier leaves environment projections inside top. -/
def C5Condition.term : Sentence Signature.pure :=
  Term.box (Term.forall' (σ := Classicism.Meta.Ty.t)
    (Term.forall' (σ := Classicism.Meta.Ty.t)
      (Term.imp (Term.neg (Term.eq' Term.v1 Term.v0))
        (Term.box (Term.neg (Term.eq' Term.v1 Term.v0))))))

theorem C5Condition.reflect :
    C5Condition.term.denote (Interp.ofDomain Classicism.e) Env.nil = C5Condition := by
  change
    ((∀ x y : Prop,
        ¬ (x ≠ y) ∨ ((x ≠ y) = ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q))) =
      ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q)) =
    ((∀ x y : Prop, x ≠ y → (x ≠ y) = True) = True)
  simp only [Classicism.Meta.top_eq, Classicism.Meta.imp_eq]

end Classicism.Research.FullLogicalObservers.FiniteQualification

#print axioms Classicism.Research.FullLogicalObservers.FiniteQualification.C5Condition.reflect
#print axioms Classicism.Research.FullLogicalObservers.FiniteQualification.AtomQualification.reflect
