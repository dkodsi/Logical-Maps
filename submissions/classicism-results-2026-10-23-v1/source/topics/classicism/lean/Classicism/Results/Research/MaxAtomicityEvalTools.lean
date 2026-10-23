import Classicism.Semantics.BooleanValued

/-!
# Compositional evaluation of finite pure syntax

Direct source: the defining equations of BooleanValued.eval (misc,
23 October 2026, unpaginated). Small rewriting lemmas expose one constructor
at a time, avoiding a large whole-term definitional-equality calculation.
These are external semantic identities; no object-language axiom is added.
-/

namespace Classicism.Meta.Research.MaxAtomicityEvalTools

open BooleanValued

noncomputable section

variable {B : Type} [CompleteBooleanAlgebra B]
variable {Sig : Signature} (I : Interpretation Sig B) {Γ : Ctx}

theorem eval_conj (p q : Formula Sig Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.conj p q) env = eval I p env ⊓ eval I q env := rfl

theorem eval_disj (p q : Formula Sig Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.disj p q) env = eval I p env ⊔ eval I q env := rfl

theorem eval_neg (p : Formula Sig Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.neg p) env = (eval I p env)ᶜ := rfl

theorem eval_imp (p q : Formula Sig Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.imp p q) env = (eval I p env)ᶜ ⊔ eval I q env := rfl

theorem eval_iff (p q : Formula Sig Γ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.iff p q) env =
      ((eval I p env)ᶜ ⊔ eval I q env) ⊓ ((eval I q env)ᶜ ⊔ eval I p env) := rfl

theorem eval_eq {σ : Ty} (a b : Term Sig Γ σ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.eq' a b) env = crisp (eval I a env) (eval I b env) := rfl

theorem eval_forall {σ : Ty} (p : Formula Sig (σ :: Γ))
    (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.forall' p) env = ⨅ x : Dom I.E B σ, eval I p (.cons x env) := rfl

theorem eval_exists {σ : Ty} (p : Formula Sig (σ :: Γ))
    (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.exists' p) env = ⨆ x : Dom I.E B σ, eval I p (.cons x env) := rfl

theorem eval_app {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ))
    (a : Term Sig Γ σ) (env : IEnv (Dom I.E B) Γ) :
    eval I (.app f a) env = eval I f env (eval I a env) := rfl

theorem eval_lam {σ : Ty} {ρ : RTy} (p : Term Sig (σ :: Γ) ρ)
    (env : IEnv (Dom I.E B) Γ) :
    eval I (.lam p) env = fun x => eval I p (.cons x env) := rfl

theorem eval_v0 {σ : Ty} (x : Dom I.E B σ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.v0 : Term Sig (σ :: Γ) σ) (.cons x env) = x := rfl

theorem eval_v1 {σ τ : Ty} (x : Dom I.E B σ) (y : Dom I.E B τ)
    (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.v1 : Term Sig (σ :: τ :: Γ) τ) (.cons x (.cons y env)) = y := rfl

theorem eval_v2 {σ τ υ : Ty} (x : Dom I.E B σ) (y : Dom I.E B τ)
    (z : Dom I.E B υ) (env : IEnv (Dom I.E B) Γ) :
    eval I (Term.v2 : Term Sig (σ :: τ :: υ :: Γ) υ)
      (.cons x (.cons y (.cons z env))) = z := rfl

end

end Classicism.Meta.Research.MaxAtomicityEvalTools
