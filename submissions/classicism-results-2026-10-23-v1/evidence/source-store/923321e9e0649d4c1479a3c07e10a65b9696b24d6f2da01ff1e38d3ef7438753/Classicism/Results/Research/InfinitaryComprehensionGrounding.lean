import Classicism.Results.Research.InfinitaryComprehensionSyntax
import Classicism.Semantics.Env

/-!
# Grounding the auxiliary type variables

Source: the closed-type proviso in `InfinitaryComprehensionSyntax` and the
canonical-model construction in the main Infinitary Comprehension note,
section 4 (misc, 23 October 2026, unpaginated).

The original language has only closed types. The finite repository uses
`Ty.var` as an auxiliary metalogical device. This explicit retyping sends
those variables to `e`; every original closed type is unchanged. It allows a
canonical presentation indexed by the convenient `Ty` datatype to use only
the actual closed-type C5 instances of the input model.

This is source development, not a compilation certificate.
-/

namespace Classicism.Research.InfinitaryComprehension.Grounding

open Classicism.Meta

universe u

mutual
  def groundTy : Ty → Ty
    | .e => .e
    | .rel ρ => .rel (groundRTy ρ)
    | .var _ => .e
  def groundRTy : RTy → RTy
    | .t => .t
    | .arr σ ρ => .arr (groundTy σ) (groundRTy ρ)
end

mutual
  theorem groundTy_closed : ∀ σ : Ty, (groundTy σ).Closed
    | .e => trivial
    | .rel ρ => groundRTy_closed ρ
    | .var _ => trivial
  theorem groundRTy_closed : ∀ ρ : RTy, (groundRTy ρ).Closed
    | .t => trivial
    | .arr σ ρ => ⟨groundTy_closed σ, groundRTy_closed ρ⟩
end

mutual
  theorem groundTy_eq_of_closed : ∀ (σ : Ty), σ.Closed → groundTy σ = σ
    | .e, _ => rfl
    | .rel ρ, h => congrArg Ty.rel (groundRTy_eq_of_closed ρ h)
    | .var _, h => False.elim h
  theorem groundRTy_eq_of_closed : ∀ (ρ : RTy), ρ.Closed → groundRTy ρ = ρ
    | .t, _ => rfl
    | .arr σ ρ, h => by
        change groundTy σ ⇒ groundRTy ρ = σ ⇒ ρ
        rw [groundTy_eq_of_closed σ h.1, groundRTy_eq_of_closed ρ h.2]
end

abbrev groundCtx (Γ : Ctx) : Ctx := Γ.map groundTy

def groundVar : {Γ : Ctx} → {σ : Ty} → Var Γ σ → Var (groundCtx Γ) (groundTy σ)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (groundVar v)

theorem groundCtx_closed (Γ : Ctx) : ∀ σ ∈ groundCtx Γ, σ.Closed := by
  intro σ h
  obtain ⟨τ, _, rfl⟩ := List.mem_map.mp h
  exact groundTy_closed τ

theorem groundRTy_ofArgs (Γ : Ctx) :
    groundRTy (RTy.ofArgs Γ) = RTy.ofArgs (groundCtx Γ) := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
      change groundTy σ ⇒ groundRTy (RTy.ofArgs Γ) =
        groundTy σ ⇒ RTy.ofArgs (groundCtx Γ)
      rw [ih]

/-- The same finite tuple before and after grounding its type labels. -/
def groundEnv {D : Ty → Type} : {Γ : Ctx} →
    IEnv (fun σ => D (groundTy σ)) Γ → IEnv D (groundCtx Γ)
  | _, .nil => .nil
  | _, .cons x xs => .cons x (groundEnv xs)

def ungroundEnv {D : Ty → Type} : (Γ : Ctx) →
    IEnv D (groundCtx Γ) → IEnv (fun σ => D (groundTy σ)) Γ
  | [], .nil => .nil
  | _ :: Γ, .cons x xs => .cons x (ungroundEnv Γ xs)

theorem unground_groundEnv {D : Ty → Type} {Γ : Ctx}
    (xs : IEnv (fun σ => D (groundTy σ)) Γ) :
    ungroundEnv Γ (groundEnv xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      exact congrArg (fun ys : IEnv (fun σ => D (groundTy σ)) _ =>
        @IEnv.cons (fun σ => D (groundTy σ)) _ _ x ys) ih

theorem ground_ungroundEnv {D : Ty → Type} (Γ : Ctx)
    (xs : IEnv D (groundCtx Γ)) : groundEnv (ungroundEnv Γ xs) = xs := by
  induction Γ with
  | nil => cases xs; rfl
  | cons σ Γ ih =>
      cases xs with
      | cons x xs => exact congrArg (fun ys : IEnv D _ => IEnv.cons x ys) (ih xs)

theorem groundEnv_get {D : Ty → Type} {Γ : Ctx}
    (xs : IEnv (fun σ => D (groundTy σ)) Γ) {σ : Ty} (v : Var Γ σ) :
    (groundEnv xs).get (groundVar v) = xs.get v := by
  induction v with
  | zero => cases xs; rfl
  | succ v ih => cases xs with | cons x xs => exact ih xs

theorem groundEnv_surjective {D : Ty → Type} (Γ : Ctx) :
    Function.Surjective (@groundEnv D Γ) :=
  fun xs => ⟨ungroundEnv Γ xs, ground_ungroundEnv Γ xs⟩

/-- Retype the actual infinitary grammar. Arbitrary parameter assignments
are mapped explicitly, and the index sets of infinitary connectives are
unchanged. No extra type instances are postulated in the input model. -/
def groundTerm {Param Param' : Ty → Type u}
    (mapParam : ∀ {σ}, Param σ → Param' (groundTy σ)) :
    {Γ : Ctx} → {σ : Ty} → Term Param Γ σ →
      Term Param' (groundCtx Γ) (groundTy σ)
  | _, _, .var v => .var (groundVar v)
  | _, _, .param p => .param (mapParam p)
  | _, _, .app f a => .app (groundTerm mapParam f) (groundTerm mapParam a)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .neg p => .neg (groundTerm mapParam p)
  | _, _, .conj p q => .conj (groundTerm mapParam p) (groundTerm mapParam q)
  | _, _, .disj p q => .disj (groundTerm mapParam p) (groundTerm mapParam q)
  | _, _, .imp p q => .imp (groundTerm mapParam p) (groundTerm mapParam q)
  | _, _, .iff p q => .iff (groundTerm mapParam p) (groundTerm mapParam q)
  | _, _, .eq a b => .eq (groundTerm mapParam a) (groundTerm mapParam b)
  | _, _, .boxOp => .boxOp
  | _, _, .all p => .all (groundTerm mapParam p)
  | _, _, .ex p => .ex (groundTerm mapParam p)
  | _, _, .iAnd I p => .iAnd I (fun i => groundTerm mapParam (p i))
  | _, _, .iOr I p => .iOr I (fun i => groundTerm mapParam (p i))

theorem groundTerm_box {Param Param' : Ty → Type u}
    (mapParam : ∀ {σ}, Param σ → Param' (groundTy σ))
    {Γ : Ctx} (p : Formula Param Γ) :
    groundTerm mapParam p.box = (groundTerm mapParam p).box := rfl

/-- Compatibility with renaming is expressed pointwise. Grounding may
identify types but never identifies de Bruijn variable positions. -/
theorem groundTerm_rename {Param Param' : Ty → Type u}
    (mapParam : ∀ {σ}, Param σ → Param' (groundTy σ)) :
    ∀ {Γ σ} (p : Term Param Γ σ) {Δ} (r : Ren Γ Δ)
      (s : Ren (groundCtx Γ) (groundCtx Δ)),
      (∀ {τ} (v : Var Γ τ), s (groundVar v) = groundVar (r v)) →
      groundTerm mapParam (p.rename r) = (groundTerm mapParam p).rename s := by
  intro Γ σ p
  induction p with
  | var v => intro Δ r s h; exact congrArg Term.var (h v).symm
  | param p => intros; rfl
  | app f a ihf iha =>
      intro Δ r s h
      simp only [Term.rename, groundTerm, ihf r s h, iha r s h] <;> rfl
  | top => intros; rfl
  | bot => intros; rfl
  | neg p ih =>
      intro Δ r s h
      simp only [Term.rename, groundTerm, ih r s h] <;> rfl
  | conj p q ihp ihq =>
      intro Δ r s h
      simp only [Term.rename, groundTerm, ihp r s h, ihq r s h] <;> rfl
  | disj p q ihp ihq =>
      intro Δ r s h
      simp only [Term.rename, groundTerm, ihp r s h, ihq r s h] <;> rfl
  | imp p q ihp ihq =>
      intro Δ r s h
      simp only [Term.rename, groundTerm, ihp r s h, ihq r s h] <;> rfl
  | iff p q ihp ihq =>
      intro Δ r s h
      simp only [Term.rename, groundTerm, ihp r s h, ihq r s h] <;> rfl
  | eq a b iha ihb =>
      intro Δ r s h
      simp only [Term.rename, groundTerm, iha r s h, ihb r s h] <;> rfl
  | boxOp => intros; rfl
  | all p ih =>
      intro Δ r s h
      apply congrArg Term.all
      apply ih (Ren.lift r) (Ren.lift s)
      intro τ v
      cases v with
      | zero => rfl
      | succ v => exact congrArg Var.succ (h v)
  | ex p ih =>
      intro Δ r s h
      apply congrArg Term.ex
      apply ih (Ren.lift r) (Ren.lift s)
      intro τ v
      cases v with
      | zero => rfl
      | succ v => exact congrArg Var.succ (h v)
  | iAnd I p ih =>
      intro Δ r s h
      exact congrArg (Term.iAnd I) (funext (fun i => ih i r s h))
  | iOr I p ih =>
      intro Δ r s h
      exact congrArg (Term.iOr I) (funext (fun i => ih i r s h))

#print axioms groundTy_closed
#print axioms groundTy_eq_of_closed
#print axioms groundTerm_rename

end Classicism.Research.InfinitaryComprehension.Grounding
