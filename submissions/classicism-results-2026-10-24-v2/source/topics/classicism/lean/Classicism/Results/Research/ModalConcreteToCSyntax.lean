import Classicism.Results.Research.ModalComprehensionConcreteSyntax
import Classicism.Syntax.Conversion

/-!
# Concrete lambda-free syntax interpreted in C's actual syntax

Original research, misc, 23 October 2026. Direct source:
modal-comprehension-abstraction-audit.txt, the translation into C.

This is one direction of the syntax translation. Primitive source binders
become C's quantified abstractions; the source B constant becomes lambda
p.(p=top). The source language itself still has no lambda constructor.
Application is translated homomorphically, so the box equation is conversion,
not an invented literal equality of syntax trees. No derivation translation
or converse equivalence is claimed by this syntax module alone.
-/

namespace Classicism.Research.ModalConcreteToC
open Classicism.Meta

abbrev SourceVar := ModalComprehensionConcreteSyntax.Var
abbrev SourceTerm := ModalComprehensionConcreteSyntax.Term
abbrev SourceRen := ModalComprehensionConcreteSyntax.Ren
abbrev SourceSub := ModalComprehensionConcreteSyntax.Sub

def signature (Const : Ty → Type) : Signature where
  Const := Sigma Const
  typeOf := Sigma.fst

def toCVar : {Γ : Ctx} → {σ : Ty} → SourceVar Γ σ → Var Γ σ
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (toCVar v)

def fromCVar : {Γ : Ctx} → {σ : Ty} → Var Γ σ → SourceVar Γ σ
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (fromCVar v)

theorem fromCVar_toCVar {Γ σ} (v : SourceVar Γ σ) : fromCVar (toCVar v) = v := by
  induction v <;> simp_all only [fromCVar, toCVar]

theorem toCVar_fromCVar {Γ σ} (v : Var Γ σ) : toCVar (fromCVar v) = v := by
  induction v <;> simp_all only [fromCVar, toCVar]

def toCRen {Γ Δ} (r : SourceRen Γ Δ) : Ren Γ Δ :=
  fun _ v => toCVar (r (fromCVar v))

theorem toCRen_lift {Γ Δ σ} (r : SourceRen Γ Δ) :
    toCRen (ModalComprehensionConcreteSyntax.Ren.lift (σ := σ) r) =
      Ren.lift (toCRen r) := by
  funext τ v
  cases v <;> rfl

theorem toCRen_shift {Γ σ} :
    toCRen (ModalComprehensionConcreteSyntax.Ren.shift : SourceRen Γ (σ :: Γ)) =
      Ren.shift := by
  funext τ v
  simp only [toCRen, ModalComprehensionConcreteSyntax.Ren.shift, toCVar,
    toCVar_fromCVar, Ren.shift]

variable {Const : Ty → Type}

def toC : {Γ : Ctx} → {σ : Ty} → SourceTerm Const Γ σ → Term (signature Const) Γ σ
  | _, _, .var v => .var (toCVar v)
  | _, σ, .const c => Term.const (Sig := signature Const) (Sigma.mk σ c)
  | _, _, .app f a => .app (toC f) (toC a)
  | _, _, .top => Term.top
  | _, _, .imp p q => Term.imp (toC p) (toC q)
  | _, _, .iff p q => Term.iff (toC p) (toC q)
  | _, _, .eq a b => Term.eq' (toC a) (toC b)
  | _, _, .boxOp => .lam (Term.box (.var .zero))
  | _, _, .all p => Term.forall' (toC p)
  | _, _, .ex p => Term.exists' (toC p)

theorem toC_rename {Γ Δ σ} (r : SourceRen Γ Δ) (a : SourceTerm Const Γ σ) :
    toC (a.rename r) = (toC a).rename (toCRen r) := by
  induction a generalizing Δ with
  | var v =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, toC,
        Term.rename_var, toCRen, fromCVar_toCVar]
  | const c => rfl
  | app f a ihf iha =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, toC,
        Term.rename_app, ihf, iha]
  | top => rfl
  | imp p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, toC,
        Term.imp, Term.disj, Term.neg, Term.rename_app, Term.rename_or,
        Term.rename_not, ihp, ihq]
  | iff p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, toC,
        Term.iff, Term.conj, Term.imp, Term.disj, Term.neg, Term.rename_app,
        Term.rename_and, Term.rename_or, Term.rename_not, ihp, ihq]
  | eq a b iha ihb =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, toC,
        Term.eq', Term.rename_app, Term.rename_eq, iha, ihb]
  | boxOp => rfl
  | all p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, toC,
        Term.forall', Term.rename_app, Term.rename_all, Term.rename_lam,
        ih, toCRen_lift]
  | ex p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.rename, toC,
        Term.exists', Term.rename_app, Term.rename_ex, Term.rename_lam,
        ih, toCRen_lift]

theorem toC_wk {Γ σ τ} (a : SourceTerm Const Γ τ) :
    toC (a.wk (σ := σ)) = (toC a).weaken := by
  rw [ModalComprehensionConcreteSyntax.Term.wk, toC_rename, toCRen_shift]

def toCSub {Γ Δ} (s : SourceSub Const Γ Δ) : Sub (signature Const) Γ Δ :=
  fun _ v => toC (s (fromCVar v))

theorem toCSub_lift {Γ Δ σ} (s : SourceSub Const Γ Δ) :
    toCSub (ModalComprehensionConcreteSyntax.Sub.lift (σ := σ) s) =
      Sub.lift (toCSub s) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v => exact toC_wk (s (fromCVar v))

theorem toC_subst {Γ Δ σ} (s : SourceSub Const Γ Δ) (a : SourceTerm Const Γ σ) :
    toC (a.subst s) = (toC a).subst (toCSub s) := by
  induction a generalizing Δ with
  | var v =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, toC,
        Term.subst_var, toCSub, fromCVar_toCVar]
  | const c => rfl
  | app f a ihf iha =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, toC,
        Term.subst_app, ihf, iha]
  | top => rfl
  | imp p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, toC,
        Term.imp, Term.disj, Term.neg, Term.subst_app, Term.subst_or,
        Term.subst_not, ihp, ihq]
  | iff p q ihp ihq =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, toC,
        Term.iff, Term.conj, Term.imp, Term.disj, Term.neg, Term.subst_app,
        Term.subst_and, Term.subst_or, Term.subst_not, ihp, ihq]
  | eq a b iha ihb =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, toC,
        Term.eq', Term.subst_app, Term.subst_eq, iha, ihb]
  | boxOp => rfl
  | all p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, toC,
        Term.forall', Term.subst_app, Term.subst_all, Term.subst_lam,
        ih, toCSub_lift]
  | ex p ih =>
      simp only [ModalComprehensionConcreteSyntax.Term.subst, toC,
        Term.exists', Term.subst_app, Term.subst_ex, Term.subst_lam,
        ih, toCSub_lift]

theorem toCSub_cons_id {Γ σ} (a : SourceTerm Const Γ σ) :
    toCSub (ModalComprehensionConcreteSyntax.Sub.cons a
      ModalComprehensionConcreteSyntax.Sub.id) = Sub.cons (toC a) Sub.id := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v =>
      simp only [toCSub, fromCVar, ModalComprehensionConcreteSyntax.Sub.cons,
        ModalComprehensionConcreteSyntax.Sub.id, toC, toCVar_fromCVar,
        Sub.cons_succ, Sub.id]

theorem toC_inst {Γ σ τ} (p : SourceTerm Const (σ :: Γ) τ)
    (a : SourceTerm Const Γ σ) : toC (p.inst a) = (toC p).instantiate (toC a) := by
  rw [ModalComprehensionConcreteSyntax.Term.inst, toC_subst, toCSub_cons_id]

def coextC : (ρ : RTy) → {Γ : Ctx} →
    Term (signature Const) Γ ρ → Term (signature Const) Γ ρ →
      Term (signature Const) Γ Ty.t
  | .t, _, p, q => Term.iff p q
  | .arr σ ρ, _, f, g => Term.forall' (coextC ρ
      (.app f.weaken (.var .zero)) (.app g.weaken (.var .zero)))

theorem toC_coext (ρ : RTy) : ∀ {Γ} (p q : SourceTerm Const Γ ρ),
    toC (ModalComprehensionConcreteSyntax.Term.coext ρ p q) =
      coextC ρ (toC p) (toC q) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [ModalComprehensionConcreteSyntax.Term.coext, toC, coextC,
        ih, toC_wk, toCVar]

theorem toC_box {Γ} (p : SourceTerm Const Γ Ty.t) :
    Conv (toC p.box) (Term.box (toC p)) :=
  Conv.beta (Term.box (.var .zero)) (toC p)

#print axioms toC_rename
#print axioms toC_subst
#print axioms toC_inst
#print axioms toC_coext
#print axioms toC_box

end Classicism.Research.ModalConcreteToC
