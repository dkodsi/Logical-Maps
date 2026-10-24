import Classicism.Syntax.Term

/-!
# A concrete infinitary, lambda-free object language

This is ordinary metatheory, not a shallow proof in C. The types are exactly
`Meta.Ty`/`Meta.RTy`; original type instances are their `Closed` instances.
`Param` supplies an arbitrary universe-small family of free parameters at
each type, while bound contexts remain finite. An infinitary connective has
an arbitrary `Type u` of children. The inductive grammar enforces well-founded
syntax and has no lambda constructor, truth predicate, or model predicate.

The universe parameter is a metatheoretic size bound for one Lean instance;
the construction and theorems are universe-polymorphic.
-/

namespace Classicism.Research.InfinitaryComprehension

open Classicism.Meta

universe u

/-- Infinitary typed terms with finite de Bruijn bound contexts. -/
inductive Term (Param : Ty → Type u) : Ctx → Ty → Type (u + 1)
  | var {Γ σ} : Var Γ σ → Term Param Γ σ
  | param {Γ σ} : Param σ → Term Param Γ σ
  | app {Γ σ} {ρ : RTy} :
      Term Param Γ (σ ⇒ ρ) → Term Param Γ σ → Term Param Γ ρ
  | top {Γ} : Term Param Γ Ty.t
  | bot {Γ} : Term Param Γ Ty.t
  | neg {Γ} : Term Param Γ Ty.t → Term Param Γ Ty.t
  | conj {Γ} : Term Param Γ Ty.t → Term Param Γ Ty.t → Term Param Γ Ty.t
  | disj {Γ} : Term Param Γ Ty.t → Term Param Γ Ty.t → Term Param Γ Ty.t
  | imp {Γ} : Term Param Γ Ty.t → Term Param Γ Ty.t → Term Param Γ Ty.t
  | iff {Γ} : Term Param Γ Ty.t → Term Param Γ Ty.t → Term Param Γ Ty.t
  | eq {Γ σ} : Term Param Γ σ → Term Param Γ σ → Term Param Γ Ty.t
  | boxOp {Γ} : Term Param Γ (RTy.t ⇒ RTy.t)
  | all {Γ σ} : Term Param (σ :: Γ) Ty.t → Term Param Γ Ty.t
  | ex {Γ σ} : Term Param (σ :: Γ) Ty.t → Term Param Γ Ty.t
  | iAnd {Γ} (I : Type u) : (I → Term Param Γ Ty.t) → Term Param Γ Ty.t
  | iOr {Γ} (I : Type u) : (I → Term Param Γ Ty.t) → Term Param Γ Ty.t

abbrev Formula (Param : Ty → Type u) (Γ : Ctx) := Term Param Γ Ty.t
abbrev Ren (Γ Δ : Ctx) := ∀ {σ}, Var Γ σ → Var Δ σ

namespace Ren

def lift (r : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

/-- Retain the variables on the left of an appended context. -/
def embed : (Γ Δ : Ctx) → Ren Γ (Γ ++ Δ)
  | [], _, _, v => nomatch v
  | _ :: _, _, _, .zero => .zero
  | _ :: Γ, Δ, _, .succ v => .succ (embed Γ Δ v)

end Ren

/-- The final variable after a finite context. -/
def lastVar (Γ : Ctx) (σ : Ty) : Var (Γ ++ [σ]) σ :=
  match Γ with
  | [] => .zero
  | _ :: Γ => .succ (lastVar Γ σ)

namespace Term

variable {Param : Ty → Type u}

abbrev box {Γ} (p : Formula Param Γ) : Formula Param Γ := .app .boxOp p

def rename {Γ Δ σ} (r : Ren Γ Δ) : Term Param Γ σ → Term Param Δ σ
  | .var v => .var (r v)
  | .param p => .param p
  | .app f a => .app (rename r f) (rename r a)
  | .top => .top
  | .bot => .bot
  | .neg p => .neg (rename r p)
  | .conj p q => .conj (rename r p) (rename r q)
  | .disj p q => .disj (rename r p) (rename r q)
  | .imp p q => .imp (rename r p) (rename r q)
  | .iff p q => .iff (rename r p) (rename r q)
  | .eq a b => .eq (rename r a) (rename r b)
  | .boxOp => .boxOp
  | .all p => .all (rename (Ren.lift r) p)
  | .ex p => .ex (rename (Ren.lift r) p)
  | .iAnd I p => .iAnd I (fun i => rename r (p i))
  | .iOr I p => .iOr I (fun i => rename r (p i))

/-- Apply a relation to the displayed finite family of argument variables. -/
def applyVars {Δ : Ctx} : (Γ : Ctx) →
    Term Param Δ (RTy.ofArgs Γ) →
    (∀ {σ}, Var Γ σ → Term Param Δ σ) → Formula Param Δ
  | [], f, _ => f
  | _ :: Γ, f, xs =>
      applyVars Γ (.app f (xs .zero)) (fun v => xs (.succ v))

/-- Close a finite argument context while retaining the outer context. -/
def closeAll {Δ : Ctx} : (Γ : Ctx) → Formula Param (Γ ++ Δ) → Formula Param Δ
  | [], p => p
  | _ :: Γ, p => closeAll Γ (.all p)

/-- The matrix `R[xs] ↔ A`, with R bound outside the finite argument tuple. -/
def compBody {Γ : Ctx} (A : Formula Param Γ) :
    Formula Param (Γ ++ [Ty.rel (RTy.ofArgs Γ)]) :=
  .iff
    (applyVars Γ (.var (lastVar Γ _))
      (fun v => .var (Ren.embed Γ _ v)))
    (A.rename (Ren.embed Γ _))

/-- The actual object-language formula `∃R □∀xs (R[xs] ↔ A)`.
The parameter family stays free; validity quantifies its assignments. -/
def comprehension {Γ : Ctx} (A : Formula Param Γ) : Formula Param [] :=
  .ex (.box (closeAll Γ A.compBody))

end Term

end Classicism.Research.InfinitaryComprehension
