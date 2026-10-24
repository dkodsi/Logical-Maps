import Classicism.Results.Research.InfinitaryComprehensionSupport
import Classicism.Results.Research.InfinitaryComprehensionConsequences
import Classicism.Results.Research.ModalConcreteToCSyntax

/-!
# The actual finite lambda-free reduct of the infinitary language

The source is the concrete syntax used by the checked finite reconstruction,
not merely a second syntax using the same type codes. Its constants become
free infinitary parameters. Binder variables are transported by the existing
`toCVar`/`fromCVar` inverse maps. Renaming and capture-avoiding substitution
commute with the embedding, including beneath both quantifier binders.

`evalFinite` is an explicit recursive interpretation of that finite syntax in
the canonical Henkin model. `eval_embed` proves its agreement with the actual
infinitary interpreter. `finite_comprehension` then extracts concrete strong
finite comprehension from the new schema; no semantic preservation premise is
assumed. The finite source signature and this reduct use universe zero, as do
the existing concrete finite syntax and categorical Premodel APIs.

This is not a proof that an arbitrary C5 Premodel has the canonical Henkin
presentation, nor a soundness proof for all of the finite derivation calculus.
Those are separate bridges. No infinitary formula is translated into finitary C.

Direct source: research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md, sections 1 and 4 (misc, 23 October 2026).
-/

namespace Classicism.Research.InfinitaryComprehension.FiniteBridge

open Classicism.Meta
open Classicism.Research.ModalConcreteToC (toCVar fromCVar
  fromCVar_toCVar toCVar_fromCVar)

abbrev FTerm := ModalComprehensionConcreteSyntax.Term
abbrev FVar := ModalComprehensionConcreteSyntax.Var
abbrev FRen := ModalComprehensionConcreteSyntax.Ren
abbrev FSub := ModalComprehensionConcreteSyntax.Sub

variable {Const : Ty → Type}

/-- The finite source's constants are genuine parameters of the larger syntax. -/
def embed : {Γ : Ctx} → {σ : Ty} → FTerm Const Γ σ → Term Const Γ σ
  | _, _, .var v => .var (toCVar v)
  | _, _, .const c => .param c
  | _, _, .app f a => .app (embed f) (embed a)
  | _, _, .top => .top
  | _, _, .imp p q => .imp (embed p) (embed q)
  | _, _, .iff p q => .iff (embed p) (embed q)
  | _, _, .eq a b => .eq (embed a) (embed b)
  | _, _, .boxOp => .boxOp
  | _, _, .all p => .all (embed p)
  | _, _, .ex p => .ex (embed p)

def embedRen {Γ Δ : Ctx} (r : FRen Γ Δ) : Ren Γ Δ :=
  fun v => toCVar (r (fromCVar v))

theorem embedRen_lift {Γ Δ : Ctx} {σ : Ty} (r : FRen Γ Δ) :
    @Eq (Ren (σ :: Γ) (σ :: Δ))
      (embedRen (ModalComprehensionConcreteSyntax.Ren.lift r))
      (Ren.lift (embedRen r)) := by
  funext τ v
  cases v <;> rfl

theorem embed_rename {Γ Δ : Ctx} {σ : Ty}
    (r : FRen Γ Δ) (a : FTerm Const Γ σ) :
    embed (a.rename r) = (embed a).rename (embedRen r) := by
  induction a generalizing Δ with
  | var v =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, embed,
        Term.rename, embedRen, fromCVar_toCVar]
  | const c => rfl
  | app f a ihf iha =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, embed,
        Term.rename, ihf, iha]
  | top => rfl
  | imp p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, embed,
        Term.rename, ihp, ihq]
  | iff p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, embed,
        Term.rename, ihp, ihq]
  | eq a b iha ihb =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, embed,
        Term.rename, iha, ihb]
  | boxOp => rfl
  | all p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, embed,
        Term.rename, ih, embedRen_lift]
  | ex p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, embed,
        Term.rename, ih, embedRen_lift]

theorem embedRen_shift {Γ : Ctx} {σ : Ty} :
    @Eq (Ren Γ (σ :: Γ))
      (embedRen (ModalComprehensionConcreteSyntax.Ren.shift : FRen Γ (σ :: Γ)))
      (fun v => .succ v) := by
  funext τ v
  simp only [embedRen, ModalComprehensionConcreteSyntax.Ren.shift,
    toCVar, toCVar_fromCVar]

theorem embed_wk {Γ : Ctx} {σ τ : Ty} (a : FTerm Const Γ τ) :
    embed (a.wk (σ := σ)) = ConsequenceCalculus.wk (embed a) := by
  rw [ModalComprehensionConcreteSyntax.Term.wk, embed_rename, embedRen_shift]
  rfl

def embedSub {Γ Δ : Ctx} (s : FSub Const Γ Δ) :
    ConsequenceCalculus.Sub (Param := Const) Γ Δ :=
  fun v => embed (s (fromCVar v))

theorem embedSub_lift {Γ Δ : Ctx} {σ : Ty} (s : FSub Const Γ Δ) :
    @Eq (ConsequenceCalculus.Sub (Param := Const) (σ :: Γ) (σ :: Δ))
      (embedSub (ModalComprehensionConcreteSyntax.Sub.lift s))
      (ConsequenceCalculus.Sub.lift (embedSub s)) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v => exact embed_wk (s (fromCVar v))

theorem embed_subst {Γ Δ : Ctx} {σ : Ty}
    (s : FSub Const Γ Δ) (a : FTerm Const Γ σ) :
    embed (a.subst s) = ConsequenceCalculus.subst (embedSub s) (embed a) := by
  induction a generalizing Δ with
  | var v =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, embed,
        ConsequenceCalculus.subst, embedSub, fromCVar_toCVar]
  | const c => rfl
  | app f a ihf iha =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, embed,
        ConsequenceCalculus.subst, ihf, iha]
  | top => rfl
  | imp p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, embed,
        ConsequenceCalculus.subst, ihp, ihq]
  | iff p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, embed,
        ConsequenceCalculus.subst, ihp, ihq]
  | eq a b iha ihb =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, embed,
        ConsequenceCalculus.subst, iha, ihb]
  | boxOp => rfl
  | all p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, embed,
        ConsequenceCalculus.subst, ih, embedSub_lift]
  | ex p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, embed,
        ConsequenceCalculus.subst, ih, embedSub_lift]

theorem embedSub_single {Γ : Ctx} {σ : Ty} (a : FTerm Const Γ σ) :
    @Eq (ConsequenceCalculus.Sub (Param := Const) (σ :: Γ) Γ)
      (embedSub (ModalComprehensionConcreteSyntax.Sub.cons a
        ModalComprehensionConcreteSyntax.Sub.id))
      (ConsequenceCalculus.Sub.single (embed a)) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v =>
      simp only [embedSub, ModalComprehensionConcreteSyntax.Sub.cons,
        ModalComprehensionConcreteSyntax.Sub.id, fromCVar, embed,
        ConsequenceCalculus.Sub.single, toCVar_fromCVar]

theorem embed_inst {Γ : Ctx} {σ τ : Ty}
    (p : FTerm Const (σ :: Γ) τ) (a : FTerm Const Γ σ) :
    embed (p.inst a) = ConsequenceCalculus.inst (embed p) (embed a) := by
  rw [ModalComprehensionConcreteSyntax.Term.inst, embed_subst, embedSub_single]
  rfl

abbrev FiniteEnv (M : Henkin.Model.{0}) (Γ : Ctx) :=
  ∀ {σ}, FVar Γ σ → M.Dom σ

def finiteCons {M : Henkin.Model.{0}} {Γ : Ctx} {σ : Ty}
    (x : M.Dom σ) (env : FiniteEnv M Γ) : FiniteEnv M (σ :: Γ)
  | _, .zero => x
  | _, .succ v => env v

def toInfEnv {M : Henkin.Model.{0}} {Γ : Ctx}
    (env : FiniteEnv M Γ) : Henkin.Env M Γ := fun v => env (fromCVar v)

def fromInfEnv {M : Henkin.Model.{0}} {Γ : Ctx}
    (env : Henkin.Env M Γ) : FiniteEnv M Γ := fun v => env (toCVar v)

theorem toInfEnv_from {M : Henkin.Model.{0}} {Γ : Ctx} (env : Henkin.Env M Γ) :
    @Eq (Henkin.Env M Γ) (toInfEnv (fromInfEnv env)) env := by
  funext σ v
  simp only [toInfEnv, fromInfEnv, toCVar_fromCVar]

theorem fromInfEnv_to {M : Henkin.Model.{0}} {Γ : Ctx} (env : FiniteEnv M Γ) :
    @Eq (FiniteEnv M Γ) (fromInfEnv (toInfEnv env)) env := by
  funext σ v
  simp only [toInfEnv, fromInfEnv, fromCVar_toCVar]

theorem toInfEnv_cons {M : Henkin.Model.{0}} {Γ : Ctx} {σ : Ty}
    (x : M.Dom σ) (env : FiniteEnv M Γ) :
    @Eq (Henkin.Env M (σ :: Γ))
      (toInfEnv (finiteCons x env)) (Henkin.Env.cons x (toInfEnv env)) := by
  funext τ v
  cases v <;> rfl

/-- The actual finite reduct: quantifiers and first-class box are interpreted,
not replaced by truth-preservation assumptions. -/
def evalFinite (M : Henkin.Model.{0}) (η : Henkin.Assignment M Const) :
    {Γ : Ctx} → {σ : Ty} → FTerm Const Γ σ → FiniteEnv M Γ → M.Dom σ
  | _, _, .var v, env => env v
  | _, _, .const c, _ => η c
  | _, _, .app f a, env => M.app (evalFinite M η f env) (evalFinite M η a env)
  | _, _, .top, _ => M.top
  | _, _, .imp p q, env => M.imp (evalFinite M η p env) (evalFinite M η q env)
  | _, _, .iff p q, env => M.iff (evalFinite M η p env) (evalFinite M η q env)
  | _, _, .eq a b, env => M.eq (evalFinite M η a env) (evalFinite M η b env)
  | _, _, .boxOp, _ => M.boxObj
  | _, _, .all p, env => M.iAnd _ (fun x => evalFinite M η p (finiteCons x env))
  | _, _, .ex p, env => M.iOr _ (fun x => evalFinite M η p (finiteCons x env))

theorem eval_embed (M : Henkin.Model.{0}) (η : Henkin.Assignment M Const)
    {Γ : Ctx} {σ : Ty} (a : FTerm Const Γ σ) (env : FiniteEnv M Γ) :
    Henkin.eval M η (embed a) (toInfEnv env) = evalFinite M η a env := by
  induction a with
  | var v => simp only [embed, Henkin.eval, toInfEnv, fromCVar_toCVar, evalFinite]
  | const c => rfl
  | app f a ihf iha => simp only [embed, Henkin.eval, evalFinite, ihf, iha]
  | top => rfl
  | imp p q ihp ihq => simp only [embed, Henkin.eval, evalFinite, ihp, ihq]
  | iff p q ihp ihq => simp only [embed, Henkin.eval, evalFinite, ihp, ihq]
  | eq a b iha ihb => simp only [embed, Henkin.eval, evalFinite, iha, ihb]
  | boxOp => rfl
  | all p ih =>
      apply congrArg (M.iAnd _)
      funext x
      rw [← toInfEnv_cons]
      exact ih (finiteCons x env)
  | ex p ih =>
      apply congrArg (M.iOr _)
      funext x
      rw [← toInfEnv_cons]
      exact ih (finiteCons x env)

theorem eval_embed_infinite_env (M : Henkin.Model.{0})
    (η : Henkin.Assignment M Const) {Γ : Ctx} {σ : Ty}
    (a : FTerm Const Γ σ) (env : Henkin.Env M Γ) :
    Henkin.eval M η (embed a) env = evalFinite M η a (fromInfEnv env) := by
  have h := eval_embed M η a (fromInfEnv env)
  rw [toInfEnv_from] at h
  exact h

/-- Comprehension of a concrete finite source matrix, derived from the actual
infinitary schema. The witness represents every world, not merely the root. -/
theorem finite_comprehension (M : Henkin.Model.{0}) {w : M.World}
    (hc : Henkin.Comp M w) (η : Henkin.Assignment M Const)
    {Γ : Ctx} (A : FTerm Const Γ Ty.t) :
    ∃ R : M.Dom (RTy.ofArgs Γ), ∀ (env : FiniteEnv M Γ) (v : M.World),
      M.truth (Henkin.uncurry M Γ R (toInfEnv env)) v ↔
        M.truth (evalFinite M η A env) v := by
  obtain ⟨R, hR⟩ := (Henkin.eval_comprehension_iff M η (embed A) w).1
    (hc Const η Γ (embed A))
  refine ⟨R, ?_⟩
  intro env v
  have h := hR (toInfEnv env) v
  rw [eval_embed] at h
  exact h

/-- Semantic local consequence is unchanged by the finite embedding. This is
proved from recursive evaluation, not supplied as an interface field. -/
theorem sequent_at_iff (M : Henkin.Model.{0}) (η : Henkin.Assignment M Const)
    {Γ : Ctx} (Δ : List (FTerm Const Γ Ty.t)) (p : FTerm Const Γ Ty.t)
    (env : FiniteEnv M Γ) (w : M.World) :
    ((∀ q ∈ Δ, M.truth (evalFinite M η q env) w) →
      M.truth (evalFinite M η p env) w) ↔
    ((∀ q ∈ Δ.map embed, M.truth (Henkin.eval M η q (toInfEnv env)) w) →
      M.truth (Henkin.eval M η (embed p) (toInfEnv env)) w) := by
  constructor
  · intro h hΔ
    rw [eval_embed]
    apply h
    intro q hq
    have hq' := hΔ (embed q) (List.mem_map.mpr ⟨q, hq, rfl⟩)
    simpa only [eval_embed] using hq'
  · intro h hΔ
    have hp := h (by
      intro q hq
      obtain ⟨r, hr, hrq⟩ := List.mem_map.mp hq
      subst q
      simpa only [eval_embed] using hΔ r hr)
    simpa only [eval_embed] using hp

#print axioms embed_rename
#print axioms embed_subst
#print axioms embed_inst
#print axioms eval_embed
#print axioms finite_comprehension
#print axioms sequent_at_iff

end Classicism.Research.InfinitaryComprehension.FiniteBridge
