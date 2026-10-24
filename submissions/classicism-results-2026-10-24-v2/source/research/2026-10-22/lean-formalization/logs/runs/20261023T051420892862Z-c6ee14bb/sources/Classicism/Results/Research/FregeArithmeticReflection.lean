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
    environment σ (k := k + 1) (.cons (σ := Ty.nu σ) x env) =
      extendEnv x (environment σ env) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem apply_eq {α β : Type} {f g : α → β} {x y : α}
    (hf : f = g) (hx : x = y) : f x = g y :=
  (congrFun hf x).trans (congrArg g hx)

theorem term_reflect (σ : Ty) {k : Nat} (t : ATerm k)
    (env : Env Classicism.e (numCtx σ k)) :
    (t.toTerm σ).denote (Interp.ofDomain Classicism.e) env =
      readTerm t (environment σ env) := by
  induction t with
  | var i => rfl
  | zero =>
      exact (Term.denote_close _ _ env).trans (Classicism.Arith.zero.reflect σ)
  | suc t ih =>
      exact apply_eq
        ((Term.denote_close _ (Classicism.Arith.suc.term σ) env).trans
          (Classicism.Arith.suc.reflect σ)) ih

theorem formula_reflect (σ : Ty) {k : Nat} (φ : AForm k)
    (env : Env Classicism.e (numCtx σ k)) :
    (φ.toTerm σ).denote (Interp.ofDomain Classicism.e) env =
      readFormula φ (environment σ env) := by
  induction φ with
  | nat t =>
      exact apply_eq
        ((Term.denote_close _ (Classicism.Arith.N.term σ) env).trans
          (Classicism.Arith.N.reflect σ)) (term_reflect σ t env)
  | sum t u v =>
      exact apply_eq (apply_eq (apply_eq
        ((Term.denote_close _ (Classicism.Arith.Sum.term σ) env).trans
          (Classicism.Arith.Sum.reflect σ)) (term_reflect σ t env))
        (term_reflect σ u env)) (term_reflect σ v env)
  | prod t u v =>
      exact apply_eq (apply_eq (apply_eq
        ((Term.denote_close _ (Classicism.Arith.Prod.term σ) env).trans
          (Classicism.Arith.Prod.reflect σ)) (term_reflect σ t env))
        (term_reflect σ u env)) (term_reflect σ v env)
  | eq t u =>
      exact congrArg₂ Eq (term_reflect σ t env) (term_reflect σ u env)
  | neg φ ih =>
      exact congrArg Not (ih env)
  | disj φ ψ ihφ ihψ =>
      exact congrArg₂ Or (ihφ env) (ihψ env)
  | conj φ ψ ihφ ihψ =>
      exact congrArg₂ And (ihφ env) (ihψ env)
  | all φ ih =>
      change (∀ x : Num (σ.denote Classicism.e),
        ¬ ((Classicism.Arith.N.term σ).close.denote (Interp.ofDomain Classicism.e)
          (.cons (σ := Ty.nu σ) x env)) x ∨
          (φ.toTerm σ).denote (Interp.ofDomain Classicism.e) (.cons x env)) = _
      apply congrArg (fun F : Num (σ.denote Classicism.e) → Prop => ∀ x, F x)
      funext x
      have hN := (Term.denote_close (Interp.ofDomain Classicism.e)
        (Classicism.Arith.N.term σ) (.cons (σ := Ty.nu σ) x env)).trans
          (Classicism.Arith.N.reflect σ)
      have hφ := (ih (.cons (σ := Ty.nu σ) x env)).trans
        (congrArg (readFormula φ) (environment_cons σ env x))
      exact (congrArg₂ Or (congrArg Not (congrFun hN x)) hφ).trans (imp_eq _ _)

theorem sentence_reflect (σ : Ty) (φ : AForm 0) :
    Sentence.holds (Interp.ofDomain Classicism.e) (φ.toTerm σ) =
      readSentence (σ.denote Classicism.e) φ := by
  have he : environment σ (Env.nil : Env Classicism.e []) =
      (fun i : Fin 0 => Fin.elim0 i : NumEnv (σ.denote Classicism.e) 0) := by
    funext i
    exact Fin.elim0 i
  exact (formula_reflect σ φ .nil).trans (congrArg (readFormula φ) he)

end Classicism.Meta.Research.FregeArithmeticReflection

#print axioms Classicism.Meta.Research.FregeArithmeticReflection.term_reflect
#print axioms Classicism.Meta.Research.FregeArithmeticReflection.formula_reflect
#print axioms Classicism.Meta.Research.FregeArithmeticReflection.sentence_reflect
