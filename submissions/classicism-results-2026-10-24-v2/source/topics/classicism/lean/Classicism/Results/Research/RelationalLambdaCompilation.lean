import Classicism.Results.Research.RelationalBracketSubstitution
import Classicism.Results.Research.BetaIdentityContextualClosure

/-!
# Compiling raw lambda terms to relational bracket terms

Original research, misc, 23 October 2026. Every raw Meta.Term constructor
is compiled: variables and application are preserved, lambda is compiled
by bracket abstraction, and all logical/nonlogical constants are typed
opaque atoms. Renaming commutes literally. Substitution commutes as an
OBJECT IDENTITY, using the already derived bracket substitution coherence
and theorem-level abstraction congruence.

The actual concrete derivation calculus interprets every constructor of
BetaIdentity.EqProof, hence contextual beta/eta conversion. NamedAxiom
remains the explicit family of comprehension definitions for combinators.
No meanings or delta equations are assigned to the opaque logical atoms;
this is not whole-C proof transport or finite-name erasure.
-/

namespace Classicism.Research.RelationalLambdaCompilation
open Classicism.Meta (Ty RTy Ctx Signature)
open RelationalBracketAbstraction (BasisConst)
open RelationalBracketInterpretation
  (BTerm embed embedVar embed_wk embed_inst NamedAxiom bracket_beta_derives
   bracket_congruence_derives bracket_substitution_derives)
open ModalComprehensionConcreteSyntax (Derives calculus)

/-- Each source constant is preserved as an opaque typed atom, including
the type-indexed operations whose delta laws are outside this theorem. -/
inductive Atoms (Sig : Signature) : Ty → Type
  | nonlogical (c : Sig.Const) : Atoms Sig (Sig.typeOf c)
  | and : Atoms Sig (RTy.t ⇒ RTy.t ⇒ RTy.t)
  | or : Atoms Sig (RTy.t ⇒ RTy.t ⇒ RTy.t)
  | not : Atoms Sig (RTy.t ⇒ RTy.t)
  | all (σ : Ty) : Atoms Sig ((σ ⇒ RTy.t) ⇒ RTy.t)
  | ex (σ : Ty) : Atoms Sig ((σ ⇒ RTy.t) ⇒ RTy.t)
  | eq (σ : Ty) : Atoms Sig (σ ⇒ σ ⇒ RTy.t)
  | constR (ρ : RTy) : Atoms Sig (RTy.t ⇒ ρ)
  | negR (ρ : RTy) : Atoms Sig (ρ ⇒ ρ)
  | andR (ρ : RTy) : Atoms Sig (ρ ⇒ ρ ⇒ ρ)
  | orR (ρ : RTy) : Atoms Sig (ρ ⇒ ρ ⇒ ρ)
  | coextR (ρ : RTy) : Atoms Sig (ρ ⇒ ρ ⇒ RTy.t)
  | boxR (ρ : RTy) : Atoms Sig (ρ ⇒ ρ)
  | inclR (ρ : RTy) : Atoms Sig (ρ ⇒ ρ ⇒ RTy.t)

variable {Sig : Signature}

def compile : {Γ : Ctx} → {σ : Ty} → Classicism.Meta.Term Sig Γ σ →
    BTerm (Atoms Sig) Γ σ
  | _, _, .var v => .var v
  | _, _, .const c => .const (.original (.nonlogical c))
  | _, _, .app f a => .app (compile f) (compile a)
  | _, _, .lam b => (compile b).bracket
  | _, _, .and => .const (.original .and)
  | _, _, .or => .const (.original .or)
  | _, _, .not => .const (.original .not)
  | _, _, .all σ => .const (.original (.all σ))
  | _, _, .ex σ => .const (.original (.ex σ))
  | _, _, .eq σ => .const (.original (.eq σ))
  | _, _, .constR ρ => .const (.original (.constR ρ))
  | _, _, .negR ρ => .const (.original (.negR ρ))
  | _, _, .andR ρ => .const (.original (.andR ρ))
  | _, _, .orR ρ => .const (.original (.orR ρ))
  | _, _, .coextR ρ => .const (.original (.coextR ρ))
  | _, _, .boxR ρ => .const (.original (.boxR ρ))
  | _, _, .inclR ρ => .const (.original (.inclR ρ))

/-- Literal renaming coherence, including under compiled abstraction. -/
theorem compile_rename {Γ Δ : Ctx} {σ : Ty} (r : Classicism.Meta.Ren Γ Δ)
    (M : Classicism.Meta.Term Sig Γ σ) :
    compile (M.rename r) = (compile M).rename r := by
  induction M generalizing Δ with
  | var v => rfl
  | const c => rfl
  | app f a ihf iha =>
      change RelationalBracketAbstraction.Term.app (compile (f.rename r))
        (compile (a.rename r)) =
        .app ((compile f).rename r) ((compile a).rename r)
      rw [ihf, iha]
  | lam b ih =>
      change (compile (b.rename (Classicism.Meta.Ren.lift r))).bracket =
        (compile b).bracket.rename r
      rw [ih, RelationalBracketAbstraction.Term.bracket_rename]
  | and => rfl
  | or => rfl
  | not => rfl
  | all σ => rfl
  | ex σ => rfl
  | eq σ => rfl
  | constR ρ => rfl
  | negR ρ => rfl
  | andR ρ => rfl
  | orR ρ => rfl
  | coextR ρ => rfl
  | boxR ρ => rfl
  | inclR ρ => rfl

theorem compile_weaken {Γ : Ctx} {σ τ : Ty}
    (M : Classicism.Meta.Term Sig Γ τ) :
    compile (M.weaken (τ := σ)) = (compile M).wk :=
  compile_rename Classicism.Meta.Ren.shift M

def compileSub {Γ Θ : Ctx} (s : Classicism.Meta.Sub Sig Γ Θ) :
    RelationalBracketAbstraction.Sub (Atoms Sig) Γ Θ :=
  fun τ v => compile (s τ v)

theorem compileSub_lift {Γ Θ : Ctx} {σ : Ty}
    (s : Classicism.Meta.Sub Sig Γ Θ) :
    compileSub (Classicism.Meta.Sub.lift (σ := σ) s) =
      RelationalBracketAbstraction.Sub.lift (compileSub s) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v => exact compile_weaken (s _ v)

theorem compileSub_cons_id {Γ : Ctx} {σ : Ty}
    (a : Classicism.Meta.Term Sig Γ σ) :
    compileSub (Classicism.Meta.Sub.cons a Classicism.Meta.Sub.id) =
      RelationalBracketAbstraction.Sub.cons (compile a)
        RelationalBracketAbstraction.Sub.id := by
  funext τ v
  cases v <;> rfl

/-- Substitution coherence is proved as literal object equality, not
incorrectly asserted as syntactic equality of the bracket expansions. -/
theorem compile_subst_derives {Γ Θ : Ctx} {σ : Ty}
    (s : Classicism.Meta.Sub Sig Γ Θ) (M : Classicism.Meta.Term Sig Γ σ) :
    Derives (BasisConst (Atoms Sig)) (NamedAxiom (Atoms Sig)) Θ []
      (.eq (embed (compile (M.subst s))) (embed ((compile M).subst (compileSub s)))) := by
  induction M generalizing Θ with
  | var v => exact .eqRefl _
  | const c => exact .eqRefl _
  | app f a ihf iha =>
      simpa only [Classicism.Meta.Term.subst, compile,
        RelationalBracketAbstraction.Term.subst, embed] using
        Derives.eqApp (ihf s) (iha s)
  | @lam Γ σ ρ b ih =>
      have hb := ih (Classicism.Meta.Sub.lift (σ := σ) s)
      rw [compileSub_lift] at hb
      exact .eqTrans
        (bracket_congruence_derives
          (compile (b.subst (Classicism.Meta.Sub.lift s)))
          ((compile b).subst (RelationalBracketAbstraction.Sub.lift (compileSub s))) hb)
        (bracket_substitution_derives (compileSub s) (compile b))
  | and => exact .eqRefl _
  | or => exact .eqRefl _
  | not => exact .eqRefl _
  | all σ => exact .eqRefl _
  | ex σ => exact .eqRefl _
  | eq σ => exact .eqRefl _
  | constR ρ => exact .eqRefl _
  | negR ρ => exact .eqRefl _
  | andR ρ => exact .eqRefl _
  | orR ρ => exact .eqRefl _
  | coextR ρ => exact .eqRefl _
  | boxR ρ => exact .eqRefl _
  | inclR ρ => exact .eqRefl _

/-- The one-variable instance relates the compiler's substitution with
the concrete target's genuine capture-avoiding instantiation operation. -/
theorem compile_inst_derives {Γ : Ctx} {σ τ : Ty}
    (M : Classicism.Meta.Term Sig (σ :: Γ) τ) (a : Classicism.Meta.Term Sig Γ σ) :
    Derives (BasisConst (Atoms Sig)) (NamedAxiom (Atoms Sig)) Γ []
      (.eq (embed (compile (M.instantiate a))) ((embed (compile M)).inst (embed (compile a)))) := by
  have h : Derives (BasisConst (Atoms Sig)) (NamedAxiom (Atoms Sig)) Γ []
      (.eq (embed (compile (M.instantiate a))) (embed ((compile M).inst (compile a)))) := by
    simpa only [Classicism.Meta.Term.instantiate, compileSub_cons_id,
      RelationalBracketAbstraction.Term.inst] using
      compile_subst_derives (Classicism.Meta.Sub.cons a Classicism.Meta.Sub.id) M
  simpa only [embed_inst] using h

/-- Actual proof induction interprets all six raw equality constructors.
The zeta case invokes the concrete calculus's derived theorem-level zeta,
and the beta case uses bracket beta plus the proved substitution theorem. -/
theorem eqProof_derives {Γ : Ctx} {τ : Ty}
    {a b : Classicism.Meta.Term Sig Γ τ}
    (h : Classicism.Meta.Research.BetaIdentity.EqProof a b) :
    Derives (BasisConst (Atoms Sig)) (NamedAxiom (Atoms Sig)) Γ []
      (.eq (embed (compile a)) (embed (compile b))) := by
  induction h with
  | refl a => exact .eqRefl _
  | symm _ ih => exact .eqSymm ih
  | trans _ _ ih₁ ih₂ => exact .eqTrans ih₁ ih₂
  | app _ _ ihf iha =>
      simpa only [compile, embed] using Derives.eqApp ihf iha
  | beta M a =>
      simpa only [compile, embed] using
        Derives.eqTrans (bracket_beta_derives (compile M) (compile a) [])
        (.eqSymm (compile_inst_derives M a))
  | @zeta Γ σ ρ f g _ ih =>
      apply (calculus (BasisConst (Atoms Sig)) (NamedAxiom (Atoms Sig))).theorem_zeta
      change Derives (BasisConst (Atoms Sig)) (NamedAxiom (Atoms Sig)) (σ :: Γ) []
        (.eq (.app (embed (compile f)).wk (.var .zero))
          (.app (embed (compile g)).wk (.var .zero)))
      simpa only [compile, compile_weaken, embed, embed_wk, embedVar] using ih

/-- The independently certified contextual beta/eta closure now has an
interpretation in the actual lambda-free concrete derivation relation. -/
theorem contextual_beta_eta_derives {Γ : Ctx} {τ : Ty}
    {a b : Classicism.Meta.Term Sig Γ τ}
    (h : Classicism.Meta.Research.BetaIdentity.ContextConversion a b) :
    Derives (BasisConst (Atoms Sig)) (NamedAxiom (Atoms Sig)) Γ []
      (.eq (embed (compile a)) (embed (compile b))) :=
  eqProof_derives (Classicism.Meta.Research.BetaIdentity.contextual_conversion_sound h)

#print axioms compile_rename
#print axioms compile_subst_derives
#print axioms compile_inst_derives
#print axioms eqProof_derives
#print axioms contextual_beta_eta_derives

end Classicism.Research.RelationalLambdaCompilation
