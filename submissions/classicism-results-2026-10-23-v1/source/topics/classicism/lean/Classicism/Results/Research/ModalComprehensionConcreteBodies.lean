import Classicism.Results.Research.ModalComprehensionConcreteSyntax

/-!
# Concrete finite-body codes for strong modal comprehension

Original research, misc, 23 October 2026. This fills the remaining syntactic
part of UniformComprehension: a finite formula/binder spine is encoded as
the admitted one-variable formula `□diagram(H)`. No witness is selected.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open ModalComprehensionRepresentation (AdmittedBody diagram UniformRepresents)

abbrev Body (Const : Ty → Type) (Γ : Ctx) (ρ : RTy) :=
  AdmittedBody (language Const) Γ ρ

namespace Body
variable {Const : Ty → Type}

def rename {Γ Δ} {ρ : RTy} (r : Ren Γ Δ) : Body Const Γ ρ → Body Const Δ ρ
  | .atom p => .atom (p.rename r)
  | .bind A => .bind (rename (Ren.lift r) A)

def subst {Γ Δ} {ρ : RTy} (s : Sub Const Γ Δ) : Body Const Γ ρ → Body Const Δ ρ
  | .atom p => .atom (p.subst s)
  | .bind A => .bind (subst (Sub.lift s) A)

theorem subst_id {Γ} {ρ : RTy} (A : Body Const Γ ρ) : A.subst Sub.id = A := by
  induction A with
  | atom p => exact congrArg (AdmittedBody.atom (L := language Const)) (Term.subst_id p)
  | bind A ih =>
      change AdmittedBody.bind (Body.subst (Sub.lift Sub.id) A) = AdmittedBody.bind A
      rw [Sub.lift_id, ih]

theorem subst_rename {Γ Δ Θ} {ρ : RTy} (s : Sub Const Δ Θ) (r : Ren Γ Δ)
    (A : Body Const Γ ρ) :
    (A.rename r).subst s = A.subst (fun v => s (r v)) := by
  have hl {Γ Δ Θ υ} (s : Sub Const Δ Θ) (r : Ren Γ Δ) :
      @Eq (Sub Const (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => Sub.lift s (Ren.lift r v))
        (Sub.lift (fun v => s (r v))) := by
    funext τ v
    cases v <;> rfl
  induction A generalizing Δ Θ with
  | atom p =>
      exact congrArg (AdmittedBody.atom (L := language Const)) (Term.subst_rename s r p)
  | bind A ih =>
      change AdmittedBody.bind (Body.subst (Sub.lift s) (Body.rename (Ren.lift r) A)) =
        AdmittedBody.bind (Body.subst (Sub.lift (fun v => s (r v))) A)
      rw [ih, hl]

theorem diagram_subst {Γ Δ} {ρ : RTy} (s : Sub Const Γ Δ) (A : Body Const Γ ρ)
    (H : Term Const Γ ρ) :
    (diagram A H).subst s = diagram (A.subst s) (H.subst s) := by
  induction A generalizing Δ with
  | atom p => rfl
  | bind A ih =>
    change Term.all (Term.subst (Sub.lift s)
      (diagram A (Term.app H.wk (Term.var .zero)))) =
      Term.all (diagram (Body.subst (Sub.lift s) A)
        (Term.app (H.subst s).wk (Term.var .zero)))
    apply congrArg Term.all
    rw [ih]
    simp only [Term.subst, Term.subst_wk, Sub.lift]
    rfl

/-- The actual formula with one newly bound representative variable. -/
def code {Γ} {ρ : RTy} (A : Body Const Γ ρ) : Term Const (ρ :: Γ) Ty.t :=
  Term.box (diagram (A.rename Ren.shift) (.var .zero))

theorem code_inst {Γ} {ρ : RTy} (A : Body Const Γ ρ) (H : Term Const Γ ρ) :
    (code A).inst H = UniformRepresents A H := by
  simp only [code, Term.inst, Term.box, Term.subst, diagram_subst, subst_rename]
  change Term.box (diagram (A.subst Sub.id) H) = Term.box (diagram A H)
  rw [subst_id]

/-- Saturate an already admitted relation-valued term into a finite body. -/
def ofTerm : (ρ : RTy) → {Γ : Ctx} → Term Const Γ ρ → Body Const Γ ρ
  | .t, _, p => .atom p
  | σ ⇒ ρ, _, p => .bind (ofTerm ρ (.app p.wk (.var .zero)))

theorem diagram_ofTerm (ρ : RTy) : ∀ {Γ} (p H : Term Const Γ ρ),
    diagram (ofTerm ρ p) H = Term.coext ρ H p := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
    intro Γ p H
    change Term.all (diagram (ofTerm ρ (.app p.wk (.var .zero)))
      (.app H.wk (.var .zero))) =
      Term.all (Term.coext ρ (.app H.wk (.var .zero)) (.app p.wk (.var .zero)))
    exact congrArg Term.all (ih _ _)

theorem rename_ofTerm (ρ : RTy) : ∀ {Γ Δ} (r : Ren Γ Δ) (p : Term Const Γ ρ),
    (ofTerm ρ p).rename r = ofTerm ρ (p.rename r) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
    intros
    simp only [ofTerm, rename, ih, Term.rename, Term.rename_wk, Ren.lift]

/-- The unary representation code used by the core is literally an instance
of the full finite-body SC schema; it needs no separate axiom. -/
theorem code_bind_ofTerm {Γ σ} {ρ : RTy} (M : Term Const (σ :: Γ) ρ) :
    code (.bind (ofTerm ρ M)) = Term.representativeBody M := by
  change Term.box (.all (diagram ((ofTerm ρ M).rename (Ren.lift Ren.shift))
    (.app (.var (.succ .zero)) (.var .zero)))) = _
  rw [rename_ofTerm, diagram_ofTerm]
  rfl

end Body

#print axioms Body.code_inst
#print axioms Body.code_bind_ofTerm

end Classicism.Research.ModalComprehensionConcreteSyntax
