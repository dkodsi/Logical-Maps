import Classicism.Results.Research.ModalComprehensionRepresentation

/-!
# Concrete lambda-free syntax for the representation theorem

Original research, misc, 23 October 2026; source proof:
`research/2026-10-23/operator-characterizations/modal-comprehension-abstraction-audit.txt`.

The inductive grammar has application and primitive quantifier BINDERS, but
no lambda constructor. All terms/bodies are finite admitted syntax. Constants
have a typed signature. Native equality below is equality of syntax trees;
function extensionality, where used, compares substitution maps only.
No C proof rules, object extensionality, or choice are imported.
-/

namespace Classicism.Research.ModalComprehensionConcreteSyntax
open Classicism.Meta
open Classicism.Research.ModalComprehensionRepresentation (Language)

abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type
  | zero {Γ σ} : Var (σ :: Γ) σ
  | succ {Γ σ τ} : Var Γ σ → Var (τ :: Γ) σ

inductive Term (Const : Ty → Type) : Ctx → Ty → Type
  | var {Γ σ} : Var Γ σ → Term Const Γ σ
  | const {Γ σ} : Const σ → Term Const Γ σ
  | app {Γ σ} {ρ : RTy} : Term Const Γ (σ ⇒ ρ) → Term Const Γ σ → Term Const Γ ρ
  | top {Γ} : Term Const Γ Ty.t
  | imp {Γ} : Term Const Γ Ty.t → Term Const Γ Ty.t → Term Const Γ Ty.t
  | iff {Γ} : Term Const Γ Ty.t → Term Const Γ Ty.t → Term Const Γ Ty.t
  | eq {Γ σ} : Term Const Γ σ → Term Const Γ σ → Term Const Γ Ty.t
  | boxOp {Γ} : Term Const Γ (RTy.t ⇒ RTy.t)
  | all {Γ σ} : Term Const (σ :: Γ) Ty.t → Term Const Γ Ty.t
  | ex {Γ σ} : Term Const (σ :: Γ) Ty.t → Term Const Γ Ty.t

abbrev Ren (Γ Δ : Ctx) := ∀ {σ}, Var Γ σ → Var Δ σ

namespace Ren
def id : Ren Γ Γ := fun v => v
def shift : Ren Γ (σ :: Γ) := Var.succ
def lift (r : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)
def comp (r : Ren Δ Θ) (s : Ren Γ Δ) : Ren Γ Θ := fun v => r (s v)

theorem lift_id : @Eq (Ren (σ :: Γ) (σ :: Γ))
    (lift (id : Ren Γ Γ)) id := by
  funext τ v
  cases v <;> rfl

theorem lift_comp (r : Ren Δ Θ) (s : Ren Γ Δ) :
    @Eq (Ren (σ :: Γ) (σ :: Θ))
      (lift (comp r s)) (comp (lift r) (lift s)) := by
  funext τ v
  cases v <;> rfl

theorem lift_shift (r : Ren Γ Δ) :
    @Eq (Ren Γ (σ :: Δ)) (comp (lift r) shift) (comp shift r) := rfl
end Ren

namespace Term
variable {Const : Ty → Type}

def rename {Γ Δ σ} (r : Ren Γ Δ) : Term Const Γ σ → Term Const Δ σ
  | .var v => .var (r v)
  | .const c => .const c
  | .app f a => .app (rename r f) (rename r a)
  | .top => .top
  | .imp p q => .imp (rename r p) (rename r q)
  | .iff p q => .iff (rename r p) (rename r q)
  | .eq a b => .eq (rename r a) (rename r b)
  | .boxOp => .boxOp
  | .all p => .all (rename (Ren.lift r) p)
  | .ex p => .ex (rename (Ren.lift r) p)

def wk {Γ σ τ} (a : Term Const Γ τ) : Term Const (σ :: Γ) τ := a.rename Ren.shift

theorem rename_id {Γ σ} (a : Term Const Γ σ) : a.rename Ren.id = a := by
  induction a <;> simp_all only [rename, Ren.lift_id] <;> rfl

theorem rename_comp {Γ Δ Θ σ} (r : Ren Δ Θ) (s : Ren Γ Δ) (a : Term Const Γ σ) :
    (a.rename s).rename r = a.rename (Ren.comp r s) := by
  induction a generalizing Δ Θ <;>
    simp_all only [rename, Ren.lift_comp] <;> rfl

theorem rename_wk {Γ Δ σ τ} (r : Ren Γ Δ) (a : Term Const Γ τ) :
    (a.wk (σ := σ)).rename (Ren.lift r) = (a.rename r).wk := by
  simp only [wk, rename_comp, Ren.lift_shift]

end Term

abbrev Sub (Const : Ty → Type) (Γ Δ : Ctx) := ∀ {σ}, Var Γ σ → Term Const Δ σ

namespace Sub
variable {Const : Ty → Type}
def id : Sub Const Γ Γ := Term.var
def cons (a : Term Const Δ σ) (s : Sub Const Γ Δ) : Sub Const (σ :: Γ) Δ
  | _, .zero => a
  | _, .succ v => s v
def lift (s : Sub Const Γ Δ) : Sub Const (σ :: Γ) (σ :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => (s v).wk

theorem lift_id : @Eq (Sub Const (σ :: Γ) (σ :: Γ))
    (lift (id : Sub Const Γ Γ)) id := by
  funext τ v
  cases v <;> rfl
end Sub

namespace Term
variable {Const : Ty → Type}

def subst {Γ Δ σ} (s : Sub Const Γ Δ) : Term Const Γ σ → Term Const Δ σ
  | .var v => s v
  | .const c => .const c
  | .app f a => .app (subst s f) (subst s a)
  | .top => .top
  | .imp p q => .imp (subst s p) (subst s q)
  | .iff p q => .iff (subst s p) (subst s q)
  | .eq a b => .eq (subst s a) (subst s b)
  | .boxOp => .boxOp
  | .all p => .all (subst (Sub.lift s) p)
  | .ex p => .ex (subst (Sub.lift s) p)

def inst {Γ σ τ} (p : Term Const (σ :: Γ) τ) (a : Term Const Γ σ) : Term Const Γ τ :=
  p.subst (Sub.cons a Sub.id)

theorem subst_id {Γ σ} (a : Term Const Γ σ) : a.subst Sub.id = a := by
  induction a <;> simp_all only [subst, Sub.lift_id] <;> rfl

theorem subst_rename {Γ Δ Θ σ} (s : Sub Const Δ Θ) (r : Ren Γ Δ)
    (a : Term Const Γ σ) :
    (a.rename r).subst s = a.subst (fun v => s (r v)) := by
  have hl {Γ Δ Θ υ} (s : Sub Const Δ Θ) (r : Ren Γ Δ) :
      @Eq (Sub Const (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => Sub.lift s (Ren.lift r v))
        (Sub.lift (fun v => s (r v))) := by
    funext τ v
    cases v <;> rfl
  induction a generalizing Δ Θ <;> simp_all only [rename, subst, hl]

theorem rename_subst {Γ Δ Θ σ} (r : Ren Δ Θ) (s : Sub Const Γ Δ)
    (a : Term Const Γ σ) :
    (a.subst s).rename r = a.subst (fun v => (s v).rename r) := by
  have hl {Γ Δ Θ υ} (r : Ren Δ Θ) (s : Sub Const Γ Δ) :
      @Eq (Sub Const (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => (Sub.lift s v).rename (Ren.lift r))
        (Sub.lift (fun v => (s v).rename r)) := by
    funext τ v
    cases v with
    | zero => rfl
    | succ v => exact rename_wk r (s v)
  induction a generalizing Δ Θ <;> simp_all only [subst, rename, hl]

theorem subst_wk {Γ Δ σ τ} (s : Sub Const Γ Δ) (a : Term Const Γ τ) :
    (a.wk (σ := σ)).subst (Sub.lift s) = (a.subst s).wk := by
  simp only [wk, subst_rename, rename_subst]
  rfl

theorem subst_comp {Γ Δ Θ σ} (s : Sub Const Γ Δ) (t : Sub Const Δ Θ)
    (a : Term Const Γ σ) :
    (a.subst s).subst t = a.subst (fun v => (s v).subst t) := by
  have hl {Γ Δ Θ υ} (s : Sub Const Γ Δ) (t : Sub Const Δ Θ) :
      @Eq (Sub Const (υ :: Γ) (υ :: Θ))
        (fun {τ} (v : Var (υ :: Γ) τ) => (Sub.lift s v).subst (Sub.lift t))
        (Sub.lift (fun v => (s v).subst t)) := by
    funext τ v
    cases v with
    | zero => rfl
    | succ v => exact subst_wk t (s v)
  induction a generalizing Δ Θ <;> simp_all only [subst, hl]

theorem inst_wk {Γ σ τ} (p : Term Const Γ τ) (a : Term Const Γ σ) : p.wk.inst a = p := by
  simp only [inst, wk, subst_rename]
  exact subst_id p

/-- Insert a new variable below the innermost binder, then substitute it
away. This is purely capture-avoiding syntax substitution, not beta. -/
theorem subst_insert {Γ σ τ υ} (M : Term Const (σ :: Γ) τ) (H : Term Const Γ υ) :
    (M.rename (Ren.lift (Ren.shift (σ := υ)))).subst
      (Sub.lift (Sub.cons H Sub.id)) = M := by
  rw [subst_rename]
  have hs : @Eq (Sub Const (σ :: Γ) (σ :: Γ))
      (fun {τ} (v : Var (σ :: Γ) τ) =>
        Sub.lift (Sub.cons H Sub.id) (Ren.lift Ren.shift v)) Sub.id := by
    funext τ v
    cases v <;> rfl
  rw [hs, subst_id]

def box {Γ} (p : Term Const Γ Ty.t) : Term Const Γ Ty.t := .app .boxOp p

def coext : (ρ : RTy) → {Γ : Ctx} → Term Const Γ ρ → Term Const Γ ρ → Term Const Γ Ty.t
  | .t, _, p, q => .iff p q
  | σ ⇒ ρ, _, f, g => .all (coext ρ (.app f.wk (.var .zero)) (.app g.wk (.var .zero)))

theorem rename_coext (ρ : RTy) : ∀ {Γ Δ} (r : Ren Γ Δ) (p q : Term Const Γ ρ),
    (coext ρ p q).rename r = coext ρ (p.rename r) (q.rename r) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
    intros
    simp only [coext, rename, ih, rename_wk, Ren.lift]

theorem subst_coext (ρ : RTy) : ∀ {Γ Δ} (s : Sub Const Γ Δ) (p q : Term Const Γ ρ),
    (coext ρ p q).subst s = coext ρ (p.subst s) (q.subst s) := by
  induction ρ using RTy.induction with
  | t => intros; rfl
  | arr σ ρ ih =>
    intros
    simp only [coext, subst, ih, subst_wk, Sub.lift]

def representativeBody {Γ σ} {ρ : RTy} (M : Term Const (σ :: Γ) ρ) :
    Term Const ((σ ⇒ ρ) :: Γ) Ty.t :=
  box (.all (coext ρ (.app (.var (.succ .zero)) (.var .zero))
    (M.rename (Ren.lift Ren.shift))))

theorem representativeBody_inst {Γ σ} {ρ : RTy} (M : Term Const (σ :: Γ) ρ)
    (H : Term Const Γ (σ ⇒ ρ)) :
    (representativeBody M).inst H =
      box (.all (coext ρ (.app H.wk (.var .zero)) M)) := by
  simp only [representativeBody, inst, box, subst, subst_coext, Sub.lift,
    Sub.cons, subst_insert]

def universalBody {Γ} (σ : Ty) : Term Const ((σ ⇒ RTy.t) :: Γ) Ty.t :=
  .all (.app (.var (.succ .zero)) (.var .zero))

def existentialBody {Γ} (σ : Ty) : Term Const ((σ ⇒ RTy.t) :: Γ) Ty.t :=
  .ex (.app (.var (.succ .zero)) (.var .zero))

end Term

/-- Every field of the previously abstract syntax interface is now a concrete
finite syntax operation or a proved syntax equation. No lambda is available. -/
def language (Const : Ty → Type) : Language where
  Term := Term Const
  var₀ := .var .zero
  wk := Term.wk
  app := .app
  top := .top
  imp := .imp
  iff := .iff
  eq := .eq
  boxOp := .boxOp
  box := Term.box
  box_app _ := rfl
  all := .all
  ex := .ex
  inst := Term.inst
  coext := Term.coext
  coext_t _ _ := rfl
  coext_arr _ _ := rfl
  inst_var _ := rfl
  inst_wk := Term.inst_wk
  inst_app _ _ _ := rfl
  inst_coext p q a := Term.subst_coext _ _ p q
  representativeBody := Term.representativeBody
  representativeBody_inst := Term.representativeBody_inst
  universalBody := Term.universalBody
  universalBody_inst _ := rfl
  existentialBody := Term.existentialBody
  existentialBody_inst _ := rfl

#print axioms language
#print axioms Term.representativeBody_inst

end Classicism.Research.ModalComprehensionConcreteSyntax
