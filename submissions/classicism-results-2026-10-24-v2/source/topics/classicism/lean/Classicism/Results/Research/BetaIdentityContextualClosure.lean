import Classicism.Syntax.Term

/-!
# Contextual beta/eta conversion from beta identities and a theorem-level zeta rule

Original metatheoretic research, 23 October 2026; direct source `misc`.
This file imports raw typed syntax and substitution algebra ONLY. It does not import
the existing Conversion or Derivation modules, the shallow logic, or any semantic
model. Its new proof relation has NO abstraction-congruence, eta, or conversion rule.
Primitive lambda TERM FORMATION is assumed; this is not a construction of lambda
abstraction from a lambda-free logical base or a modal comprehension principle.

The additional `zeta` rule is explicit: a theorem equating applications to a fresh
variable yields equality of the functions. There are no formula hypotheses in this
proof relation. Ordinary bridges from Functionality, modalized Functionality, or
all-type Intensionality to this rule are NOT certified by this file.
-/

namespace Classicism.Meta.Research.BetaIdentity

variable {Sig : Signature}

/-- Equality theorems in a raw syntax calculus with beta identities and zeta.
The application rule is ordinary equality congruence. Abstraction congruence is
deliberately absent and will be derived below. -/
inductive EqProof : {Γ : Ctx} → {τ : Ty} → Term Sig Γ τ → Term Sig Γ τ → Prop
  | refl {Γ : Ctx} {τ : Ty} (a : Term Sig Γ τ) : EqProof a a
  | symm {Γ : Ctx} {τ : Ty} {a b : Term Sig Γ τ} : EqProof a b → EqProof b a
  | trans {Γ : Ctx} {τ : Ty} {a b c : Term Sig Γ τ} :
      EqProof a b → EqProof b c → EqProof a c
  | app {Γ : Ctx} {σ : Ty} {ρ : RTy}
      {f g : Term Sig Γ (σ ⇒ ρ)} {a b : Term Sig Γ σ} :
      EqProof f g → EqProof a b → EqProof (.app f a) (.app g b)
  | beta {Γ : Ctx} {σ : Ty} {ρ : RTy}
      (b : Term Sig (σ :: Γ) ρ) (a : Term Sig Γ σ) :
      EqProof (.app (.lam b) a) (b.instantiate a)
  | zeta {Γ : Ctx} {σ : Ty} {ρ : RTy} {f g : Term Sig Γ (σ ⇒ ρ)} :
      EqProof (.app f.weaken (.var .zero)) (.app g.weaken (.var .zero)) →
      EqProof f g

/-- Pure de Bruijn substitution bookkeeping, not an object-language conversion. -/
theorem instantiate_lift_shift {Γ : Ctx} {σ τ : Ty} (b : Term Sig (σ :: Γ) τ) :
    (b.rename (Ren.lift (Ren.shift (σ := σ)))).instantiate (.var .zero) = b := by
  rw [Term.instantiate, Term.subst_rename]
  have h : Sub.compRen (Sub.cons (Term.var (Sig := Sig) (Var.zero (Γ := Γ))) Sub.id)
      (Ren.lift (Ren.shift (σ := σ))) = Sub.id := by
    funext υ v
    cases v <;> rfl
  rw [h, Term.subst_id]

/-- Beta at a fresh variable, using the beta constructor and syntax bookkeeping. -/
theorem beta_at_fresh {Γ : Ctx} {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) :
    EqProof (.app (Term.lam b).weaken (.var .zero)) b := by
  change EqProof (.app ((Term.lam b).rename Ren.shift) (.var .zero)) b
  rw [Term.rename_lam]
  have h := EqProof.beta (b.rename (Ren.lift (Ren.shift (σ := σ)))) (.var .zero)
  rw [instantiate_lift_shift] at h
  exact h

/-- Theorem-level abstraction congruence is derived, not a constructor. -/
theorem lam_congr {Γ : Ctx} {σ : Ty} {ρ : RTy}
    {b c : Term Sig (σ :: Γ) ρ} (h : EqProof b c) : EqProof (.lam b) (.lam c) :=
  EqProof.zeta (EqProof.trans (beta_at_fresh b)
    (EqProof.trans h (EqProof.symm (beta_at_fresh c))))

/-- Eta is a consequence of beta identity and the theorem-level zeta rule. -/
theorem eta {Γ : Ctx} {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) :
    EqProof (.lam (.app f.weaken (.var .zero))) f :=
  EqProof.zeta (beta_at_fresh (.app f.weaken (.var .zero)))

/-- Syntactic contextual beta/eta steps. Its `lam` constructor describes the
conversion relation being justified; it is not a rule of `EqProof`. -/
inductive ContextStep : {Γ : Ctx} → {τ : Ty} → Term Sig Γ τ → Term Sig Γ τ → Prop
  | beta {Γ : Ctx} {σ : Ty} {ρ : RTy}
      (b : Term Sig (σ :: Γ) ρ) (a : Term Sig Γ σ) :
      ContextStep (.app (.lam b) a) (b.instantiate a)
  | eta {Γ : Ctx} {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) :
      ContextStep (.lam (.app f.weaken (.var .zero))) f
  | appLeft {Γ : Ctx} {σ : Ty} {ρ : RTy}
      {f g : Term Sig Γ (σ ⇒ ρ)} (a : Term Sig Γ σ) :
      ContextStep f g → ContextStep (.app f a) (.app g a)
  | appRight {Γ : Ctx} {σ : Ty} {ρ : RTy}
      (f : Term Sig Γ (σ ⇒ ρ)) {a b : Term Sig Γ σ} :
      ContextStep a b → ContextStep (.app f a) (.app f b)
  | lam {Γ : Ctx} {σ : Ty} {ρ : RTy} {b c : Term Sig (σ :: Γ) ρ} :
      ContextStep b c → ContextStep (.lam b) (.lam c)

theorem contextStep_sound {Γ : Ctx} {τ : Ty} {a b : Term Sig Γ τ}
    (h : ContextStep a b) : EqProof a b := by
  induction h with
  | beta b a => exact EqProof.beta b a
  | eta f => exact eta f
  | appLeft a _ ih => exact EqProof.app ih (EqProof.refl a)
  | appRight f _ ih => exact EqProof.app (EqProof.refl f) ih
  | lam _ ih => exact lam_congr ih

/-- The equivalence closure of contextual beta/eta reduction. -/
inductive ContextConversion : {Γ : Ctx} → {τ : Ty} → Term Sig Γ τ → Term Sig Γ τ → Prop
  | step {Γ : Ctx} {τ : Ty} {a b : Term Sig Γ τ} :
      ContextStep a b → ContextConversion a b
  | refl {Γ : Ctx} {τ : Ty} (a : Term Sig Γ τ) : ContextConversion a a
  | symm {Γ : Ctx} {τ : Ty} {a b : Term Sig Γ τ} :
      ContextConversion a b → ContextConversion b a
  | trans {Γ : Ctx} {τ : Ty} {a b c : Term Sig Γ τ} :
      ContextConversion a b → ContextConversion b c → ContextConversion a c

/-- Every contextual beta/eta conversion has a derivation in the independent
beta-identity-plus-zeta proof relation. -/
theorem contextual_conversion_sound {Γ : Ctx} {τ : Ty} {a b : Term Sig Γ τ}
    (h : ContextConversion a b) : EqProof a b := by
  induction h with
  | step h => exact contextStep_sound h
  | refl a => exact EqProof.refl a
  | symm _ ih => exact EqProof.symm ih
  | trans _ _ ih₁ ih₂ => exact EqProof.trans ih₁ ih₂

#print axioms lam_congr
#print axioms eta
#print axioms contextual_conversion_sound

end Classicism.Meta.Research.BetaIdentity
