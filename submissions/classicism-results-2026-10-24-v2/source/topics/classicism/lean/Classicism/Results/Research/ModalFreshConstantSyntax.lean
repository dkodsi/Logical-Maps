import Classicism.Results.Research.ModalComprehensionConcreteSyntax

/-!
# Fresh constant replacement in the concrete lambda-free syntax

This module supplies the syntax map needed to connect closed naming with
the de Bruijn comprehension calculus. Constants may be interpreted by
admitted terms in the target context. Under a binder their images are
weakened, so a new parameter is never captured. The construction and its
commutation equations are proved on finite syntax trees; no lambda, choice,
proof-preservation field or conservativity theorem is assumed.

This is syntax transport. Transport of the full calculus's axiom and rule
instances is a subsequent proof obligation.
-/

namespace Classicism.Research.ModalFreshConstantSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionConcreteSyntax

variable {C D : Ty → Type}

abbrev ConstImage (C D : Ty → Type) (Δ : Ctx) :=
  ∀ {σ}, C σ → Term D Δ σ

/-- Simultaneous interpretation of constants and substitution of variables. -/
def translate {Γ Δ σ} (cs : ConstImage C D Δ) (vs : Sub D Γ Δ) :
    Term C Γ σ → Term D Δ σ
  | .var v => vs v
  | .const c => cs c
  | .app f a => .app (translate cs vs f) (translate cs vs a)
  | .top => .top
  | .imp p q => .imp (translate cs vs p) (translate cs vs q)
  | .iff p q => .iff (translate cs vs p) (translate cs vs q)
  | .eq a b => .eq (translate cs vs a) (translate cs vs b)
  | .boxOp => .boxOp
  | .all p => .all (translate (fun c => (cs c).wk) (Sub.lift vs) p)
  | .ex p => .ex (translate (fun c => (cs c).wk) (Sub.lift vs) p)

theorem rename_translate {Γ Δ Θ σ} (cs : ConstImage C D Δ)
    (vs : Sub D Γ Δ) (r : Ren Δ Θ) (t : Term C Γ σ) :
    (translate cs vs t).rename r =
      translate (fun c => (cs c).rename r) (fun v => (vs v).rename r) t := by
  have hl {Γ Δ Θ υ} (s : Sub D Γ Δ) (r : Ren Δ Θ) :
      @Eq (Sub D (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => (Sub.lift s v).rename (Ren.lift r))
        (Sub.lift (fun v => (s v).rename r)) := by
    funext τ v
    cases v with
    | zero => rfl
    | succ v => exact Term.rename_wk r (s v)
  have hc {Δ Θ υ} (cs : ConstImage C D Δ) (r : Ren Δ Θ) :
      @Eq (ConstImage C D (υ :: Θ))
        (fun {τ} (c : C τ) => ((cs c).wk (σ := υ)).rename (Ren.lift r))
        (fun c => ((cs c).rename r).wk) := by
    funext τ c
    exact Term.rename_wk r (cs c)
  induction t generalizing Δ Θ <;>
    simp_all only [translate, Term.rename, hl, hc]

theorem subst_translate {Γ Δ Θ σ} (cs : ConstImage C D Δ)
    (vs : Sub D Γ Δ) (s : Sub D Δ Θ) (t : Term C Γ σ) :
    (translate cs vs t).subst s =
      translate (fun c => (cs c).subst s) (fun v => (vs v).subst s) t := by
  have hl {Γ Δ Θ υ} (vs : Sub D Γ Δ) (s : Sub D Δ Θ) :
      @Eq (Sub D (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => (Sub.lift vs v).subst (Sub.lift s))
        (Sub.lift (fun v => (vs v).subst s)) := by
    funext τ v
    cases v with
    | zero => rfl
    | succ v => exact Term.subst_wk s (vs v)
  have hc {Δ Θ υ} (cs : ConstImage C D Δ) (s : Sub D Δ Θ) :
      @Eq (ConstImage C D (υ :: Θ))
        (fun {τ} (c : C τ) => ((cs c).wk (σ := υ)).subst (Sub.lift s))
        (fun c => ((cs c).subst s).wk) := by
    funext τ c
    exact Term.subst_wk s (cs c)
  induction t generalizing Δ Θ <;>
    simp_all only [translate, Term.subst, hl, hc]

theorem translate_rename {Γ Δ Θ σ} (cs : ConstImage C D Θ)
    (vs : Sub D Δ Θ) (r : Ren Γ Δ) (t : Term C Γ σ) :
    translate cs vs (t.rename r) = translate cs (fun v => vs (r v)) t := by
  have hl {Γ Δ Θ υ} (vs : Sub D Δ Θ) (r : Ren Γ Δ) :
      @Eq (Sub D (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => Sub.lift vs (Ren.lift r v))
        (Sub.lift (fun v => vs (r v))) := by
    funext τ v
    cases v <;> rfl
  induction t generalizing Δ Θ <;>
    simp_all only [Term.rename, translate, hl]

/-- Lifting both interpretation maps commutes with weakening the source. -/
theorem translate_wk {Γ Δ σ τ} (cs : ConstImage C D Δ)
    (vs : Sub D Γ Δ) (t : Term C Γ τ) :
    translate (fun c => (cs c).wk) (Sub.lift vs) (t.wk (σ := σ)) =
      (translate cs vs t).wk := by
  simp only [Term.wk, translate_rename, rename_translate]
  rfl

theorem translate_subst {Γ Δ Θ σ} (cs : ConstImage C D Θ)
    (vs : Sub D Δ Θ) (s : Sub C Γ Δ) (t : Term C Γ σ) :
    translate cs vs (t.subst s) =
      translate cs (fun v => translate cs vs (s v)) t := by
  have hl {Γ Δ Θ υ} (cs : ConstImage C D Θ)
      (vs : Sub D Δ Θ) (s : Sub C Γ Δ) :
      @Eq (Sub D (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) =>
          translate (fun c => (cs c).wk) (Sub.lift vs) (Sub.lift s v))
        (Sub.lift (fun v => translate cs vs (s v))) := by
    funext τ v
    cases v with
    | zero => rfl
    | succ v => exact translate_wk cs vs (s v)
  induction t generalizing Δ Θ <;>
    simp_all only [Term.subst, translate, hl]

theorem translate_coext (ρ : RTy) :
    ∀ {Γ Δ} (cs : ConstImage C D Δ) (vs : Sub D Γ Δ) (p q : Term C Γ ρ),
    translate cs vs (Term.coext ρ p q) =
      Term.coext ρ (translate cs vs p) (translate cs vs q) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
      intros
      simp only [Term.coext, translate, ih, translate_wk, Sub.lift]

/-- One new constant, typed at κ and absent from the old signature C. -/
inductive FreshConst (C : Ty → Type) (κ : Ty) : Ty → Type where
  | old {σ} : C σ → FreshConst C κ σ
  | fresh : FreshConst C κ κ

/-- The new constant is replaced by an arbitrary admitted target term. -/
def constantImage {Γ κ} (a : Term C Γ κ) : ConstImage (FreshConst C κ) C Γ
  | _, .old c => .const c
  | _, .fresh => a

/-- Insert a genuinely new variable at the front of the context. -/
def replaceFresh {Γ κ σ} (t : Term (FreshConst C κ) Γ σ) : Term C (κ :: Γ) σ :=
  translate (constantImage (.var .zero)) (fun v => .var (.succ v)) t

theorem replaceFresh_constant {Γ κ} :
    replaceFresh (Term.const (Γ := Γ) (FreshConst.fresh (C := C) (κ := κ))) =
      Term.var (Const := C) (Var.zero (Γ := Γ) (σ := κ)) := rfl

/-- Under a quantifier the inserted parameter moves past the bound variable. -/
theorem fresh_constant_under_binder {Γ κ υ} :
    translate (fun c => ((constantImage (C := C)
      (Term.var (Var.zero (Γ := Γ) (σ := κ)))) c).wk (σ := υ))
      (Sub.lift (fun {τ} (v : Var Γ τ) => Term.var (Const := C) (Var.succ v)))
      (Term.const (Γ := υ :: Γ) (FreshConst.fresh (C := C) (κ := κ))) =
      Term.var (Const := C) (Var.succ (Var.zero (Γ := Γ) (σ := κ))) := rfl

/-- After replacement, instantiating the fresh parameter by a recovers the
uniform interpretation in which the new constant denotes a. -/
theorem replaceFresh_inst {Γ κ σ} (t : Term (FreshConst C κ) Γ σ)
    (a : Term C Γ κ) :
    (replaceFresh t).inst a = translate (constantImage a) Sub.id t := by
  simp only [replaceFresh, Term.inst, subst_translate]
  have hc :
      @Eq (ConstImage (FreshConst C κ) C Γ)
        (fun {τ} (c : FreshConst C κ τ) =>
          (constantImage (Term.var (Var.zero (Γ := Γ) (σ := κ))) c).subst
            (Sub.cons a Sub.id)) (constantImage a) := by
    funext τ c
    cases c <;> rfl
  rw [hc]
  rfl

#print axioms rename_translate
#print axioms subst_translate
#print axioms translate_subst
#print axioms translate_coext
#print axioms replaceFresh_inst

end Classicism.Research.ModalFreshConstantSyntax
