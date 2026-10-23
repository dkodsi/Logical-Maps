import Classicism.Models.NominalTypedHierarchy
import Classicism.Syntax.Derivation

/-!
# Renaming and substitution in the supported hierarchy

These are statements about the actual intrinsically typed Term syntax and the
supported hierarchy's evaluator, including its lambda values. No full function
space at a relational type is substituted for the supported function space.

Source: nominal-choice-classification-20261022.md §2 (local, unpaginated, misc),
with explicit original proofs of the syntactic interface. Uncompiled candidate.
-/

namespace Classicism.Meta.Nominal.Hierarchy
noncomputable section
variable {G : Type} [Group G] {A : Action G} {I : SupportIdeal A}
variable (W : Nom A I)

def envOfFun : ∀ {Γ}, (∀ σ, Var Γ σ → dom W σ) → env W Γ
  | [], _ => ()
  | σ :: _, f => (f σ .zero, envOfFun (fun τ v => f τ (.succ v)))

@[simp] theorem lookup_envOfFun : ∀ {Γ σ} (f : ∀ τ, Var Γ τ → dom W τ) (v : Var Γ σ),
    (lookup W v).fn (envOfFun W f) = f σ v
  | _, _, _, .zero => rfl
  | _, _, f, .succ v => lookup_envOfFun (fun τ v => f τ (.succ v)) v

theorem env_ext : ∀ {Γ} {η θ : env W Γ},
    (∀ σ (v : Var Γ σ), (lookup W v).fn η = (lookup W v).fn θ) → η = θ
  | [], _, _, _ => Subsingleton.elim _ _
  | _ :: _, η, θ, h => Prod.ext (h _ .zero) (env_ext (fun _ v => h _ (.succ v)))

def pullRen {Γ Δ} (r : Ren Γ Δ) (η : env W Δ) : env W Γ :=
  envOfFun W (fun _ v => (lookup W (r _ v)).fn η)

@[simp] theorem lookup_pullRen {Γ Δ σ} (r : Ren Γ Δ) (η : env W Δ) (v : Var Γ σ) :
    (lookup W v).fn (pullRen W r η) = (lookup W (r _ v)).fn η :=
  lookup_envOfFun W _ v

theorem pullRen_lift {Γ Δ σ} (r : Ren Γ Δ) (η : env W Δ) (x : dom W σ) :
    pullRen W (Ren.lift r) (x, η) = (x, pullRen W r η) := by
  apply env_ext W
  intro τ v
  cases v with
  | zero => rfl
  | succ _ => rfl

theorem pullRen_shift {Γ σ} (η : env W Γ) (x : dom W σ) :
    pullRen W Ren.shift (x, η) = η := by
  apply env_ext W
  intro τ v
  exact lookup_pullRen W Ren.shift (x, η) v

variable {Sig : Signature} (C : FixedConstants W Sig)

theorem denote_rename : ∀ {Γ Δ} (r : Ren Γ Δ) {σ} (t : Term Sig Γ σ) (η : env W Δ),
    (denote W C (t.rename r)).fn η = (denote W C t).fn (pullRen W r η)
  | _, _, r, _, .var v, η => (lookup_pullRen W r η v).symm
  | _, _, _, _, .const _, _ | _, _, _, _, .and, _ | _, _, _, _, .or, _
  | _, _, _, _, .not, _ | _, _, _, _, .all _, _ | _, _, _, _, .ex _, _
  | _, _, _, _, .eq _, _ | _, _, _, _, .constR _, _ | _, _, _, _, .negR _, _
  | _, _, _, _, .andR _, _ | _, _, _, _, .orR _, _ | _, _, _, _, .coextR _, _
  | _, _, _, _, .boxR _, _ | _, _, _, _, .inclR _, _ => rfl
  | _, _, r, _, .app f x, η => by
    simp only [Term.rename_app, denote_app, denote_rename r f η, denote_rename r x η]
  | _, _, r, _, .lam b, η => by
    apply Subtype.ext
    funext x
    change (denote W C (b.rename (Ren.lift r))).fn (x, η) = _
    rw [denote_rename, pullRen_lift]
    rfl

@[simp] theorem denote_weaken {Γ σ τ} (t : Term Sig Γ τ) (η : env W Γ) (x : dom W σ) :
    (denote W C t.weaken).fn (x, η) = (denote W C t).fn η := by
  rw [Term.weaken, denote_rename, pullRen_shift]

@[simp] theorem denote_close {Γ σ} (t : Term Sig [] σ) (η : env W Γ) :
    (denote W C t.close).fn η = (denote W C t).fn () := by
  rw [Term.close, denote_rename]
  exact congrArg ((denote W C t).fn) (Subsingleton.elim _ _)

def pullSub {Γ Δ} (s : Sub Sig Γ Δ) (η : env W Δ) : env W Γ :=
  envOfFun W (fun _ v => (denote W C (s _ v)).fn η)

@[simp] theorem lookup_pullSub {Γ Δ σ} (s : Sub Sig Γ Δ) (η : env W Δ) (v : Var Γ σ) :
    (lookup W v).fn (pullSub W C s η) = (denote W C (s _ v)).fn η :=
  lookup_envOfFun W _ v

theorem pullSub_lift {Γ Δ σ} (s : Sub Sig Γ Δ) (η : env W Δ) (x : dom W σ) :
    pullSub W C (Sub.lift s) (x, η) = (x, pullSub W C s η) := by
  apply env_ext W
  intro τ v
  cases v with
  | zero => rfl
  | succ v =>
    change (lookup W (.succ v)).fn (pullSub W C (Sub.lift s) (x, η)) = _
    rw [lookup_pullSub, Sub.lift_succ, denote_weaken]
    exact (lookup_pullSub W C s η v).symm

theorem denote_subst : ∀ {Γ Δ} (s : Sub Sig Γ Δ) {σ} (t : Term Sig Γ σ) (η : env W Δ),
    (denote W C (t.subst s)).fn η = (denote W C t).fn (pullSub W C s η)
  | _, _, s, _, .var v, η => (lookup_pullSub W C s η v).symm
  | _, _, _, _, .const _, _ | _, _, _, _, .and, _ | _, _, _, _, .or, _
  | _, _, _, _, .not, _ | _, _, _, _, .all _, _ | _, _, _, _, .ex _, _
  | _, _, _, _, .eq _, _ | _, _, _, _, .constR _, _ | _, _, _, _, .negR _, _
  | _, _, _, _, .andR _, _ | _, _, _, _, .orR _, _ | _, _, _, _, .coextR _, _
  | _, _, _, _, .boxR _, _ | _, _, _, _, .inclR _, _ => rfl
  | _, _, s, _, .app f x, η => by
    simp only [Term.subst_app, denote_app, denote_subst s f η, denote_subst s x η]
  | _, _, s, _, .lam b, η => by
    apply Subtype.ext
    funext x
    change (denote W C (b.subst (Sub.lift s))).fn (x, η) = _
    rw [denote_subst, pullSub_lift]
    rfl

theorem pullSub_cons_id {Γ σ} (t : Term Sig Γ σ) (η : env W Γ) :
    pullSub W C (Sub.cons t Sub.id) η = ((denote W C t).fn η, η) := by
  apply env_ext W
  intro τ v
  cases v with
  | zero => rfl
  | succ v => exact lookup_pullSub W C (Sub.cons t Sub.id) η (.succ v)

@[simp] theorem denote_instantiate {Γ σ τ} (b : Term Sig (σ :: Γ) τ)
    (t : Term Sig Γ σ) (η : env W Γ) :
    (denote W C (b.instantiate t)).fn η = (denote W C b).fn ((denote W C t).fn η, η) := by
  rw [Term.instantiate, denote_subst, pullSub_cons_id]

@[simp] theorem denote_top {Γ} (η : env W Γ) :
    (denote W C (Term.top : Formula Sig Γ)).fn η = truthConst W True := by
  classical
  apply Subtype.ext
  funext w
  apply propext
  change (_ ∨ ¬_) ↔ True
  exact ⟨fun _ => True.intro, fun _ => Classical.em _⟩

@[simp] theorem denote_bot {Γ} (η : env W Γ) :
    (denote W C (Term.bot : Formula Sig Γ)).fn η = truthConst W False := by
  apply Subtype.ext
  funext w
  apply propext
  change (_ ∧ ¬_) ↔ False
  exact ⟨fun h => h.2 h.1, False.elim⟩

@[simp] theorem holds_box {Γ} (p : Formula Sig Γ) (η : env W Γ) (w : W) :
    Holds W C η w (Term.box p) ↔ ∀ v : W, Holds W C η v p := by
  rw [Term.box, holds_eq, denote_top]
  exact boxOp_at W ((denote W C p).fn η) w

end
end Classicism.Meta.Nominal.Hierarchy
