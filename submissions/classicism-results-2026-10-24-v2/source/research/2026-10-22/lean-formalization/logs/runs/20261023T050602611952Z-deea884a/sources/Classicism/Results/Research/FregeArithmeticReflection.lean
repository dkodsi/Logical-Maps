import Classicism.Results.Research.CrossBaseFirstOrder
import Classicism.Semantics.Relational

/-!
# Reflection of the existing first-order arithmetic grammar

Direct source: research/2026-10-22/notes/relational-coding-recursion-20261022.md
§§34.2, 38, unpaginated original research, misc.

This is ordinary metatheory: the existing AForm.toTerm syntax, interpreted in
the standard Prop-valued denotation, agrees with the evaluator used by the
cross-base structural induction. External syntax codes and environments are
not object-language types. This reflection theorem does not itself construct
a C derivation for each formula code, nor an intensional-model interpretation.
-/

namespace Classicism.Meta.Research.FregeArithmeticReflection

open Classicism.Research.CrossBaseFirstOrder

local instance (σ : Ty) : Classicism.Ty (σ.denote Classicism.e) := ⟨()⟩

/-- Read precisely the existing number-variable context, innermost first. -/
noncomputable def environment (σ : Ty) {k : Nat}
    (env : Env Classicism.e (numCtx σ k)) : NumEnv (σ.denote Classicism.e) k :=
  fun i => (numVar σ i).denote env

theorem environment_cons (σ : Ty) {k : Nat}
    (env : Env Classicism.e (numCtx σ k))
    (x : Num (σ.denote Classicism.e)) :
    environment σ (.cons x env) = extendEnv x (environment σ env) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem term_reflect (σ : Ty) {k : Nat} (t : ATerm k)
    (env : Env Classicism.e (numCtx σ k)) :
    (t.toTerm σ).denote (Interp.ofDomain Classicism.e) env =
      readTerm t (environment σ env) := by
  induction t with
  | var i => rfl
  | zero =>
      exact (Term.denote_close _ _ env).trans (Classicism.Arith.zero.reflect σ)
  | suc t ih =>
      simp only [ATerm.toTerm, Term.denote, Term.denote_close,
        Classicism.Arith.suc.reflect, ih, readTerm, Classicism.Arith.suc]

theorem formula_reflect (σ : Ty) {k : Nat} (φ : AForm k)
    (env : Env Classicism.e (numCtx σ k)) :
    (φ.toTerm σ).denote (Interp.ofDomain Classicism.e) env =
      readFormula φ (environment σ env) := by
  induction φ generalizing env with
  | nat t =>
      simp only [AForm.toTerm, Term.denote, Term.denote_close,
        Classicism.Arith.N.reflect, term_reflect, readFormula]
  | sum t u v =>
      simp only [AForm.toTerm, Term.denote, Term.denote_close,
        Classicism.Arith.Sum.reflect, term_reflect, readFormula]
  | prod t u v =>
      simp only [AForm.toTerm, Term.denote, Term.denote_close,
        Classicism.Arith.Prod.reflect, term_reflect, readFormula]
  | eq t u =>
      simp only [AForm.toTerm, Term.eq', Term.denote, term_reflect, readFormula]
  | neg φ ih =>
      simp only [AForm.toTerm, Term.neg, Term.denote, ih, readFormula]
  | disj φ ψ ihφ ihψ =>
      simp only [AForm.toTerm, Term.disj, Term.denote, ihφ, ihψ, readFormula]
  | conj φ ψ ihφ ihψ =>
      simp only [AForm.toTerm, Term.conj, Term.denote, ihφ, ihψ, readFormula]
  | all φ ih =>
      simp only [AForm.toTerm, Term.forall', Term.imp, Term.disj, Term.neg,
        Term.denote, Term.denote_close, Classicism.Arith.N.reflect,
        Var.denote, imp_eq, ih, environment_cons, readFormula, Classicism.Arith.N]

theorem sentence_reflect (σ : Ty) (φ : AForm 0) :
    (φ.toTerm σ).holds (Interp.ofDomain Classicism.e) =
      readSentence (σ.denote Classicism.e) φ := by
  have he : environment σ (Env.nil Classicism.e) =
      (fun i : Fin 0 => Fin.elim0 i : NumEnv (σ.denote Classicism.e) 0) := by
    funext i
    exact Fin.elim0 i
  exact (formula_reflect σ φ .nil).trans (congrArg (readFormula φ) he)

end Classicism.Meta.Research.FregeArithmeticReflection

#print axioms Classicism.Meta.Research.FregeArithmeticReflection.term_reflect
#print axioms Classicism.Meta.Research.FregeArithmeticReflection.formula_reflect
#print axioms Classicism.Meta.Research.FregeArithmeticReflection.sentence_reflect
