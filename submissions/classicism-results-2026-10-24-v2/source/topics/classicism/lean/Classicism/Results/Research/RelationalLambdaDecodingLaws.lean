import Classicism.Results.Research.RelationalLambdaDecoding
import Classicism.Syntax.Conversion

/-!
# The relational combinator laws decode to beta conversion

Original research, misc, 23 October 2026. Each of the five basis laws is
proved by explicit beta contractions of its decoded lambda term. The final
theorem is induction on the actual constructors of bracket-term equality;
no object derivability, semantic equality or additional conversion axiom is
assumed. The statements retain the relational codomain restrictions of the
typed basis, including the relational intermediate type of S.

This module was prepared without a compiler run. The axiom-report commands
below are requests for a later check, not a claim that such a check ran.
-/

namespace Classicism.Research.RelationalLambdaDecoding

open Classicism.Meta
open RelationalBracketAbstraction (BasisConst Equal)
open RelationalLambdaCompilation (Atoms)

variable {Sig : Signature} {Γ : Ctx}

/-- Substitution beneath a new binder respects weakening. -/
private theorem weaken_subst_lift {Δ : Ctx} {σ τ : Ty}
    (s : Sub Sig Γ Δ) (a : Term Sig Γ σ) :
    (a.weaken (τ := τ)).subst (Sub.lift s) = (a.subst s).weaken := by
  simp only [Term.weaken, Term.subst_rename, Term.rename_subst]
  rfl

/-- The decoded I law is one beta contraction. -/
theorem decode_lawI {ρ : RTy} (a : Term Sig Γ ρ) :
    Conv (Term.app (decodeBasis (.I ρ)) a) a := by
  simpa only [decodeBasis, Term.v0, Term.instantiate, Term.subst_var,
    Sub.cons_zero] using
    (Conv.beta (Term.v0 : Term Sig (ρ :: Γ) ρ) a)

/-- The decoded K law is two beta contractions. -/
theorem decode_lawK {σ : Ty} {ρ : RTy}
    (a : Term Sig Γ ρ) (b : Term Sig Γ σ) :
    Conv (Term.app (Term.app (decodeBasis (.K σ ρ)) a) b) a := by
  have h₁ : Conv (Term.app (decodeBasis (.K σ ρ)) a)
      (Term.lam (a.weaken (τ := σ))) := by
    simpa only [decodeBasis, Term.v1, Term.instantiate, Term.subst_lam,
      Term.subst_var, Sub.lift_succ, Sub.cons_zero] using
      (Conv.beta (Term.lam Term.v1 : Term Sig (ρ :: Γ) (σ ⇒ ρ)) a)
  have h₂ : Conv (Term.app (Term.lam (a.weaken (τ := σ))) b) a := by
    simpa only [Term.instantiate_weaken] using
      (Conv.beta (a.weaken (τ := σ)) b)
  exact Conv.trans (Conv.app_congr h₁ (Conv.refl b)) h₂

/-- The decoded S law is three beta contractions, with both arguments
substituted into the same innermost application variable. -/
theorem decode_lawS {σ : Ty} {τ ρ : RTy}
    (f : Term Sig Γ (σ ⇒ τ ⇒ ρ))
    (g : Term Sig Γ (σ ⇒ τ)) (a : Term Sig Γ σ) :
    Conv (Term.app (Term.app (Term.app (decodeBasis (.S σ τ ρ)) f) g) a)
      (Term.app (Term.app f a) (Term.app g a)) := by
  have h₁ : Conv (Term.app (decodeBasis (.S σ τ ρ)) f)
      (Term.lam (Term.lam
        (Term.app (Term.app f.weaken.weaken Term.v0)
          (Term.app Term.v1 Term.v0)))) := by
    simpa only [decodeBasis, Term.v0, Term.v1, Term.v2, Term.instantiate,
      Term.subst_lam, Term.subst_app, Term.subst_var, Sub.lift_zero,
      Sub.lift_succ, Sub.cons_zero, Term.weaken, Term.rename_var, Ren.shift] using
      (Conv.beta
        (Term.lam (Term.lam
          (Term.app (Term.app Term.v2 Term.v0) (Term.app Term.v1 Term.v0))) :
          Term Sig ((σ ⇒ τ ⇒ ρ) :: Γ) ((σ ⇒ τ) ⇒ σ ⇒ ρ)) f)
  have h₂ : Conv
      (Term.app (Term.lam (Term.lam
        (Term.app (Term.app f.weaken.weaken Term.v0)
          (Term.app Term.v1 Term.v0)))) g)
      (Term.lam (Term.app (Term.app f.weaken Term.v0)
        (Term.app g.weaken Term.v0))) := by
    simpa only [Term.v0, Term.v1, Term.instantiate, Term.subst_lam,
      Term.subst_app, Term.subst_var, Sub.lift_zero, Sub.lift_succ,
      Sub.cons_zero, weaken_subst_lift, Term.instantiate_weaken] using
      (Conv.beta
        (Term.lam (Term.app (Term.app f.weaken.weaken Term.v0)
          (Term.app Term.v1 Term.v0)) :
          Term Sig ((σ ⇒ τ) :: Γ) (σ ⇒ ρ)) g)
  have h₃ : Conv
      (Term.app (Term.lam (Term.app (Term.app f.weaken Term.v0)
        (Term.app g.weaken Term.v0))) a)
      (Term.app (Term.app f a) (Term.app g a)) := by
    simpa only [Term.v0, Term.instantiate, Term.subst_app, Term.subst_var,
      Sub.cons_zero, Term.instantiate_weaken] using
      (Conv.beta
        (Term.app (Term.app f.weaken Term.v0) (Term.app g.weaken Term.v0)) a)
  exact Conv.trans
    (Conv.app_congr (Conv.app_congr h₁ (Conv.refl g)) (Conv.refl a))
    (Conv.trans (Conv.app_congr h₂ (Conv.refl a)) h₃)

/-- The decoded C law is three beta contractions. Its exchanged arguments
may have arbitrary types, including e and opaque type variables. -/
theorem decode_lawC {σ τ : Ty} {ρ : RTy}
    (f : Term Sig Γ (σ ⇒ τ ⇒ ρ))
    (b : Term Sig Γ τ) (a : Term Sig Γ σ) :
    Conv (Term.app (Term.app (Term.app (decodeBasis (.C σ τ ρ)) f) b) a)
      (Term.app (Term.app f a) b) := by
  have h₁ : Conv (Term.app (decodeBasis (.C σ τ ρ)) f)
      (Term.lam (Term.lam
        (Term.app (Term.app f.weaken.weaken Term.v0) Term.v1))) := by
    simpa only [decodeBasis, Term.v0, Term.v1, Term.v2, Term.instantiate,
      Term.subst_lam, Term.subst_app, Term.subst_var, Sub.lift_zero,
      Sub.lift_succ, Sub.cons_zero, Term.weaken, Term.rename_var, Ren.shift] using
      (Conv.beta
        (Term.lam (Term.lam
          (Term.app (Term.app Term.v2 Term.v0) Term.v1)) :
          Term Sig ((σ ⇒ τ ⇒ ρ) :: Γ) (τ ⇒ σ ⇒ ρ)) f)
  have h₂ : Conv
      (Term.app (Term.lam (Term.lam
        (Term.app (Term.app f.weaken.weaken Term.v0) Term.v1))) b)
      (Term.lam (Term.app (Term.app f.weaken Term.v0) b.weaken)) := by
    simpa only [Term.v0, Term.v1, Term.instantiate, Term.subst_lam,
      Term.subst_app, Term.subst_var, Sub.lift_zero, Sub.lift_succ,
      Sub.cons_zero, weaken_subst_lift, Term.instantiate_weaken] using
      (Conv.beta
        (Term.lam (Term.app (Term.app f.weaken.weaken Term.v0) Term.v1) :
          Term Sig (τ :: Γ) (σ ⇒ ρ)) b)
  have h₃ : Conv
      (Term.app (Term.lam (Term.app (Term.app f.weaken Term.v0) b.weaken)) a)
      (Term.app (Term.app f a) b) := by
    simpa only [Term.v0, Term.instantiate, Term.subst_app, Term.subst_var,
      Sub.cons_zero, Term.instantiate_weaken] using
      (Conv.beta (Term.app (Term.app f.weaken Term.v0) b.weaken) a)
  exact Conv.trans
    (Conv.app_congr (Conv.app_congr h₁ (Conv.refl b)) (Conv.refl a))
    (Conv.trans (Conv.app_congr h₂ (Conv.refl a)) h₃)

/-- The decoded W law is two beta contractions; the repeated argument is
not restricted to a relational type. -/
theorem decode_lawW {σ : Ty} {ρ : RTy}
    (f : Term Sig Γ (σ ⇒ σ ⇒ ρ)) (a : Term Sig Γ σ) :
    Conv (Term.app (Term.app (decodeBasis (.W σ ρ)) f) a)
      (Term.app (Term.app f a) a) := by
  have h₁ : Conv (Term.app (decodeBasis (.W σ ρ)) f)
      (Term.lam (Term.app (Term.app f.weaken Term.v0) Term.v0)) := by
    simpa only [decodeBasis, Term.v0, Term.v1, Term.instantiate,
      Term.subst_lam, Term.subst_app, Term.subst_var, Sub.lift_zero,
      Sub.lift_succ, Sub.cons_zero] using
      (Conv.beta
        (Term.lam (Term.app (Term.app Term.v1 Term.v0) Term.v0) :
          Term Sig ((σ ⇒ σ ⇒ ρ) :: Γ) (σ ⇒ ρ)) f)
  have h₂ : Conv
      (Term.app (Term.lam (Term.app (Term.app f.weaken Term.v0) Term.v0)) a)
      (Term.app (Term.app f a) a) := by
    simpa only [Term.v0, Term.instantiate, Term.subst_app, Term.subst_var,
      Sub.cons_zero, Term.instantiate_weaken] using
      (Conv.beta (Term.app (Term.app f.weaken Term.v0) Term.v0) a)
  exact Conv.trans (Conv.app_congr h₁ (Conv.refl a)) h₂

/-- Decode a derivation in the actual five-law combinator equality to raw
lambda conversion. No extra rule is added to either relation. -/
theorem equal_conv {σ : Ty}
    {a b : RelationalBracketAbstraction.Term (Atoms Sig) Γ σ}
    (h : Equal (Atoms Sig) a b) : Conv (decode a) (decode b) := by
  induction h with
  | refl a => exact Conv.refl (decode a)
  | symm _ ih => exact Conv.symm ih
  | trans _ _ ih₁ ih₂ => exact Conv.trans ih₁ ih₂
  | app _ _ ih₁ ih₂ =>
      simpa only [decode] using Conv.app_congr ih₁ ih₂
  | lawI a =>
      simpa only [decode] using decode_lawI (decode a)
  | lawK a b =>
      simpa only [decode] using decode_lawK (decode a) (decode b)
  | lawS f g a =>
      simpa only [decode] using decode_lawS (decode f) (decode g) (decode a)
  | lawC f b a =>
      simpa only [decode] using decode_lawC (decode f) (decode b) (decode a)
  | lawW f a =>
      simpa only [decode] using decode_lawW (decode f) (decode a)

#print axioms decode_lawI
#print axioms decode_lawK
#print axioms decode_lawS
#print axioms decode_lawC
#print axioms decode_lawW
#print axioms equal_conv

end Classicism.Research.RelationalLambdaDecoding
