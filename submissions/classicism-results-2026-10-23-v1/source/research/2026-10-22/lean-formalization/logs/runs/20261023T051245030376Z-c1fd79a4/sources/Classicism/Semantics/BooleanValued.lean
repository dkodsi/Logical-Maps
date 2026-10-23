import Classicism.Syntax.Entailment
import Classicism.Semantics.Env
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Full Boolean-valued interpretation: ordinary metatheory

The truth sort is a complete Boolean algebra B, equality is crisp, and every
relational arrow is the full external function space. Quantifiers are arbitrary
meets and joins. This file proves the interpretation obligations for renaming,
substitution and beta/eta/delta conversion, including holes under binders.
It does not assume soundness of C; that is proved in BooleanValuedSoundness.

Sources: writeups/full-boolean-valued-atom-and-atomless.md sections 1-2
(construction attributed there to Bacon, Could the truths of mathematics have
been different?, 9 October 2025 draft, online appendix B.2, pp. 7-9), and
research/2026-10-22/followup/max-atomicity-selector-audit.md section 9.
The present rule-by-rule formalization is original work (misc); the local notes
are unpaginated. No claim that Bacon supplied this Lean proof is intended.
The syntactic proof organization follows Semantics/Denotation.lean.

Classical equality and function extensionality here belong to external Lean
metatheory, not to a shallow C proof. No forcing construction is assumed.
-/

namespace Classicism.Meta.BooleanValued
noncomputable section

mutual
  def Dom (E B : Type) : Ty → Type
    | .e => E
    | .var _ => E
    | .rel ρ => RDom E B ρ
  def RDom (E B : Type) : RTy → Type
    | .t => B
    | .arr σ ρ => Dom E B σ → RDom E B ρ
end

attribute [reducible] Dom RDom

structure Interpretation (Sig : Signature) (B : Type) where
  E : Type
  const : ∀ c : Sig.Const, Dom E B (Sig.typeOf c)

def Interpretation.ofDomain (E B : Type) : Interpretation Signature.pure B :=
  ⟨E, fun c => nomatch c⟩

variable {Sig : Signature} {B : Type} [CompleteBooleanAlgebra B]

/-- Equality always has value top or bottom. -/
def crisp {A : Type} (a b : A) : B := by
  classical
  exact if a = b then ⊤ else ⊥

@[simp] theorem crisp_self {A : Type} (a : A) : (crisp a a : B) = ⊤ := by
  simp [crisp]

@[simp] theorem crisp_of_ne {A : Type} {a b : A} (h : a ≠ b) :
    (crisp a b : B) = ⊥ := by simp [crisp, h]

/-- Written as the exact interpretation of the language's abbreviation for top,
so delta at the truth sort is definitional, even before using Boolean laws. -/
def topValue : B := (⨅ p : B, p) ⊔ (⨅ p : B, p)ᶜ

@[simp] theorem topValue_eq_top : (topValue : B) = ⊤ := by simp [topValue]

def constVal (E : Type) : ∀ ρ : RTy, B → RDom E B ρ
  | .t, p => p
  | .arr _ ρ, p => fun _ => constVal E ρ p

def negVal (E : Type) : ∀ ρ : RTy, RDom E B ρ → RDom E B ρ
  | .t, p => pᶜ
  | .arr _ ρ, X => fun z => negVal E ρ (X z)

def andVal (E : Type) : ∀ ρ : RTy, RDom E B ρ → RDom E B ρ → RDom E B ρ
  | .t, p, q => p ⊓ q
  | .arr _ ρ, X, Y => fun z => andVal E ρ (X z) (Y z)

def orVal (E : Type) : ∀ ρ : RTy, RDom E B ρ → RDom E B ρ → RDom E B ρ
  | .t, p, q => p ⊔ q
  | .arr _ ρ, X, Y => fun z => orVal E ρ (X z) (Y z)

def coextVal (E : Type) : ∀ ρ : RTy, RDom E B ρ → RDom E B ρ → B
  | .t, p, q => (pᶜ ⊔ q) ⊓ (qᶜ ⊔ p)
  | .arr _ ρ, X, Y => ⨅ z, coextVal E ρ (X z) (Y z)

def boxVal (E : Type) : ∀ ρ : RTy, RDom E B ρ → RDom E B ρ
  | .t, p => crisp p topValue
  | .arr _ ρ, X => fun z => boxVal E ρ (X z)

def inclVal (E : Type) : ∀ ρ : RTy, RDom E B ρ → RDom E B ρ → B
  | .t, p, q => pᶜ ⊔ q
  | .arr _ ρ, X, Y => ⨅ z, inclVal E ρ (X z) (Y z)

/-- Full-function interpretation of every constructor of the actual C syntax. -/
def eval (I : Interpretation Sig B) :
    ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → IEnv (Dom I.E B) Γ → Dom I.E B σ
  | _, _, .var v, env => env.get v
  | _, _, .const c, _ => I.const c
  | _, _, .app f a, env => eval I f env (eval I a env)
  | _, _, .lam b, env => fun x => eval I b (.cons x env)
  | _, _, .and, _ => fun p q => p ⊓ q
  | _, _, .or, _ => fun p q => p ⊔ q
  | _, _, .not, _ => fun p => pᶜ
  | _, _, .all _, _ => fun F => ⨅ x, F x
  | _, _, .ex _, _ => fun F => ⨆ x, F x
  | _, _, .eq _, _ => fun a b => crisp a b
  | _, _, .constR ρ, _ => constVal I.E ρ
  | _, _, .negR ρ, _ => negVal I.E ρ
  | _, _, .andR ρ, _ => andVal I.E ρ
  | _, _, .orR ρ, _ => orVal I.E ρ
  | _, _, .coextR ρ, _ => coextVal I.E ρ
  | _, _, .boxR ρ, _ => boxVal I.E ρ
  | _, _, .inclR ρ, _ => inclVal I.E ρ

@[simp] theorem eval_top (I : Interpretation Sig B) {Γ : Ctx}
    (env : IEnv (Dom I.E B) Γ) : eval I (Term.top : Formula Sig Γ) env = ⊤ :=
  topValue_eq_top

@[simp] theorem eval_bot (I : Interpretation Sig B) {Γ : Ctx}
    (env : IEnv (Dom I.E B) Γ) : eval I (Term.bot : Formula Sig Γ) env = ⊥ := by
  change (⨅ p : B, p) ⊓ (⨅ p : B, p)ᶜ = ⊥
  simp

theorem eval_box (I : Interpretation Sig B) {Γ : Ctx} (p : Formula Sig Γ)
    (env : IEnv (Dom I.E B) Γ) : eval I (Term.box p) env = crisp (eval I p env) (⊤ : B) := by
  change crisp (eval I p env) (eval I Term.top env) = _
  rw [eval_top]

theorem eval_rename (I : Interpretation Sig B) :
    ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} (a : Term Sig Γ σ)
      (env : IEnv (Dom I.E B) Δ),
      eval I (a.rename r) env = eval I a (IEnv.ren r env)
  | _, _, r, _, .var v, env => (IEnv.get_ren r env v).symm
  | _, _, _, _, .const _, _ | _, _, _, _, .and, _ | _, _, _, _, .or, _ | _, _, _, _, .not, _
  | _, _, _, _, .all _, _ | _, _, _, _, .ex _, _ | _, _, _, _, .eq _, _
  | _, _, _, _, .constR _, _ | _, _, _, _, .negR _, _ | _, _, _, _, .andR _, _ | _, _, _, _, .orR _, _
  | _, _, _, _, .coextR _, _ | _, _, _, _, .boxR _, _ | _, _, _, _, .inclR _, _ => rfl
  | _, _, r, _, .app f a, env => by
    simp only [Term.rename_app, eval, eval_rename I r f, eval_rename I r a]
  | _, _, r, _, .lam b, env => by
    simp only [Term.rename_lam, eval]
    funext x
    rw [eval_rename I (Ren.lift r) b, IEnv.ren_lift]

theorem eval_weaken (I : Interpretation Sig B) {Γ : Ctx} {σ τ : Ty}
    (a : Term Sig Γ σ) (x : Dom I.E B τ) (env : IEnv (Dom I.E B) Γ) :
    eval I (a.weaken (τ := τ)) (.cons x env) = eval I a env := by
  rw [Term.weaken, eval_rename, IEnv.ren_shift]

def subEnv (I : Interpretation Sig B) {Γ Δ : Ctx} (s : Sub Sig Γ Δ)
    (env : IEnv (Dom I.E B) Δ) : IEnv (Dom I.E B) Γ :=
  IEnv.ofFun fun _ v => eval I (s _ v) env

@[simp] theorem get_subEnv (I : Interpretation Sig B) {Γ Δ : Ctx}
    (s : Sub Sig Γ Δ) (env : IEnv (Dom I.E B) Δ) {σ : Ty} (v : Var Γ σ) :
    (subEnv I s env).get v = eval I (s _ v) env := IEnv.get_ofFun _ v

theorem subEnv_lift (I : Interpretation Sig B) {Γ Δ : Ctx} {σ : Ty}
    (s : Sub Sig Γ Δ) (x : Dom I.E B σ) (env : IEnv (Dom I.E B) Δ) :
    subEnv I (Sub.lift s) (.cons x env) = .cons x (subEnv I s env) := by
  apply IEnv.ext
  intro τ v
  cases v with
  | zero => rfl
  | succ v =>
    simp only [get_subEnv, Sub.lift, IEnv.get]
    exact eval_weaken I (s _ v) x env

theorem subEnv_id (I : Interpretation Sig B) {Γ : Ctx} (env : IEnv (Dom I.E B) Γ) :
    subEnv I Sub.id env = env := by
  apply IEnv.ext
  intro σ v
  simp only [get_subEnv, Sub.id, eval]

theorem eval_subst (I : Interpretation Sig B) :
    ∀ {Γ Δ : Ctx} (s : Sub Sig Γ Δ) {σ : Ty} (a : Term Sig Γ σ)
      (env : IEnv (Dom I.E B) Δ),
      eval I (a.subst s) env = eval I a (subEnv I s env)
  | _, _, s, _, .var v, env => (get_subEnv I s env v).symm
  | _, _, _, _, .const _, _ | _, _, _, _, .and, _ | _, _, _, _, .or, _ | _, _, _, _, .not, _
  | _, _, _, _, .all _, _ | _, _, _, _, .ex _, _ | _, _, _, _, .eq _, _
  | _, _, _, _, .constR _, _ | _, _, _, _, .negR _, _ | _, _, _, _, .andR _, _ | _, _, _, _, .orR _, _
  | _, _, _, _, .coextR _, _ | _, _, _, _, .boxR _, _ | _, _, _, _, .inclR _, _ => rfl
  | _, _, s, _, .app f a, env => by
    simp only [Term.subst_app, eval, eval_subst I s f, eval_subst I s a]
  | _, _, s, _, .lam b, env => by
    simp only [Term.subst_lam, eval]
    funext x
    rw [eval_subst I (Sub.lift s) b, subEnv_lift]

theorem subEnv_cons (I : Interpretation Sig B) {Γ Δ : Ctx} {σ : Ty}
    (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) (env : IEnv (Dom I.E B) Δ) :
    subEnv I (Sub.cons a s) env = .cons (eval I a env) (subEnv I s env) := by
  apply IEnv.ext
  intro τ v
  cases v <;> rfl

theorem eval_instantiate (I : Interpretation Sig B) {Γ : Ctx} {σ τ : Ty}
    (b : Term Sig (σ :: Γ) τ) (a : Term Sig Γ σ) (env : IEnv (Dom I.E B) Γ) :
    eval I (b.instantiate a) env = eval I b (.cons (eval I a env) env) := by
  rw [Term.instantiate, eval_subst, subEnv_cons, subEnv_id]

theorem eval_close (I : Interpretation Sig B) {Γ : Ctx} {σ : Ty}
    (a : Term Sig [] σ) (env : IEnv (Dom I.E B) Γ) :
    eval I a.close env = eval I a .nil := by
  rw [Term.close, eval_rename]
  exact congrArg (eval I a) (IEnv.nil_eq _)

theorem beta_value (I : Interpretation Sig B) {Γ : Ctx} {σ : Ty}
    {a b : Term Sig Γ σ} (h : Beta a b) (env : IEnv (Dom I.E B) Γ) :
    eval I a env = eval I b env := by
  cases h with
  | intro b a =>
    show (fun x => eval I b (.cons x env)) (eval I a env) = _
    rw [eval_instantiate]

theorem eta_value (I : Interpretation Sig B) {Γ : Ctx} {σ : Ty}
    {a b : Term Sig Γ σ} (h : Eta a b) (env : IEnv (Dom I.E B) Γ) :
    eval I a env = eval I b env := by
  cases h with
  | intro f =>
    show (fun x => eval I f.weaken (.cons x env) x) = _
    funext x
    rw [eval_weaken]

/-- Exact delta unfolding; no Boolean-completeness or soundness premise. -/
theorem delta_value (I : Interpretation Sig B) :
    ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, Delta a b →
      ∀ env : IEnv (Dom I.E B) Γ, eval I a env = eval I b env
  | _, _, .constR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .negR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .andR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .orR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .coextR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .boxR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .inclR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .var _, _, h, _ | _, _, .const _, _, h, _ | _, _, .app _ _, _, h, _ | _, _, .lam _, _, h, _
  | _, _, .and, _, h, _ | _, _, .or, _, h, _ | _, _, .not, _, h, _ | _, _, .all _, _, h, _
  | _, _, .ex _, _, h, _ | _, _, .eq _, _, h, _ => nomatch h

theorem step_value (I : Interpretation Sig B)
    {R : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Term Sig Γ σ → Prop}
    (hR : ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, R a b →
      ∀ env : IEnv (Dom I.E B) Γ, eval I a env = eval I b env) :
    ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, Step R a b →
      ∀ env : IEnv (Dom I.E B) Γ, eval I a env = eval I b env
  | _, _, _, _, .here h, env => hR h env
  | _, _, _, _, .appL (f := f) (f' := f') (a := a) h, env => by
    show eval I f env (eval I a env) = eval I f' env (eval I a env)
    rw [step_value I hR h env]
  | _, _, _, _, .appR (f := f) (a := a) (a' := a') h, env => by
    show eval I f env (eval I a env) = eval I f env (eval I a' env)
    rw [step_value I hR h env]
  | _, _, _, _, .lam (b := b) (b' := b') h, env => by
    show (fun x => eval I b (.cons x env)) = (fun x => eval I b' (.cons x env))
    funext x
    exact step_value I hR h (.cons x env)

theorem conv_value (I : Interpretation Sig B) {Γ : Ctx} {σ : Ty}
    {a b : Term Sig Γ σ} (h : a ≡ b) (env : IEnv (Dom I.E B) Γ) :
    eval I a env = eval I b env := by
  induction h with
  | rel h => exact step_value I (fun h env => h.elim (beta_value I · env)
      (fun h => h.elim (eta_value I · env) (delta_value I · env))) h env
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Context congruence uses equality under every assignment, including bound ones. -/
theorem hole_value (I : Interpretation Sig B) :
    ∀ {Γ Γ' : Ctx} {σ τ : Ty} (K : Hole Sig Γ σ Γ' τ) {a b : Term Sig Γ' τ},
      (∀ env', eval I a env' = eval I b env') →
      ∀ env : IEnv (Dom I.E B) Γ, eval I (K.plug a) env = eval I (K.plug b) env
  | _, _, _, _, .hole, _, _, e, env => e env
  | _, _, _, _, .appL K c, a, b, e, env => by
    show eval I (K.plug a) env (eval I c env) = eval I (K.plug b) env (eval I c env)
    rw [hole_value I K e env]
  | _, _, _, _, .appR f K, a, b, e, env => by
    show eval I f env (eval I (K.plug a) env) = eval I f env (eval I (K.plug b) env)
    rw [hole_value I K e env]
  | _, _, _, _, .lam K, a, b, e, env => by
    show (fun x => eval I (K.plug a) (.cons x env)) =
      (fun x => eval I (K.plug b) (.cons x env))
    funext x
    exact hole_value I K e (.cons x env)

end
end Classicism.Meta.BooleanValued
