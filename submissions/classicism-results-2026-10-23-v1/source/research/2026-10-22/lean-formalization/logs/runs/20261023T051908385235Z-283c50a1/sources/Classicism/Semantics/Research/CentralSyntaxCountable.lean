import Classicism.Syntax.Term
import Mathlib.Logic.Encodable.Basic

/-!
# Countability of the finitary syntax used by central gluing

Only a syntactic coding result. The raw syntax retains the hidden argument
type at an application, so different typed applications cannot acquire the
same code. No bound on any semantic domain follows from this result.
Uncompiled author draft, 22 October 2026.
-/

namespace Classicism.Meta

namespace CentralSyntax

/- Explicit constructor codes avoid a deriving-tactic dependency. -/
mutual
  def tyCode : Ty → Nat
    | .e => Nat.pair 0 0
    | .rel ρ => Nat.pair 1 (rtyCode ρ)
    | .var n => Nat.pair 2 n
  def rtyCode : RTy → Nat
    | .t => Nat.pair 0 0
    | .arr σ ρ => Nat.pair 1 (Nat.pair (tyCode σ) (rtyCode ρ))
end

mutual
  theorem tyCode_inj : ∀ σ τ : Ty, tyCode σ = tyCode τ → σ = τ
    | .e, .e, _ => rfl
    | .e, .rel _, h => by simp [tyCode, Nat.pair_eq_pair] at h
    | .e, .var _, h => by simp [tyCode, Nat.pair_eq_pair] at h
    | .rel _, .e, h => by simp [tyCode, Nat.pair_eq_pair] at h
    | .rel ρ, .rel υ, h =>
      congrArg Ty.rel (rtyCode_inj ρ υ (Nat.pair_eq_pair.mp h).2)
    | .rel _, .var _, h => by simp [tyCode, Nat.pair_eq_pair] at h
    | .var _, .e, h => by simp [tyCode, Nat.pair_eq_pair] at h
    | .var _, .rel _, h => by simp [tyCode, Nat.pair_eq_pair] at h
    | .var n, .var m, h => congrArg Ty.var (Nat.pair_eq_pair.mp h).2
  theorem rtyCode_inj : ∀ ρ υ : RTy, rtyCode ρ = rtyCode υ → ρ = υ
    | .t, .t, _ => rfl
    | .t, .arr _ _, h => by simp [rtyCode, Nat.pair_eq_pair] at h
    | .arr _ _, .t, h => by simp [rtyCode, Nat.pair_eq_pair] at h
    | .arr σ ρ, .arr τ υ, h => by
      have e := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
      rw [tyCode_inj σ τ e.1, rtyCode_inj ρ υ e.2]
end

@[simp] theorem tyCode_eq (σ τ : Ty) : tyCode σ = tyCode τ ↔ σ = τ :=
  ⟨tyCode_inj σ τ, fun h => congrArg tyCode h⟩
@[simp] theorem rtyCode_eq (ρ υ : RTy) : rtyCode ρ = rtyCode υ ↔ ρ = υ :=
  ⟨rtyCode_inj ρ υ, fun h => congrArg rtyCode h⟩

def varIndex : ∀ {Γ : Ctx} {σ : Ty}, Var Γ σ → Nat
  | _, _, .zero => 0
  | _, _, .succ v => varIndex v + 1

theorem varIndex_injective {Γ : Ctx} {σ : Ty} :
    Function.Injective (@varIndex Γ σ) := by
  intro v
  induction v with
  | zero =>
    intro w h
    cases w with
    | zero => rfl
    | succ w => simp [varIndex] at h
  | succ v ih =>
    intro w h
    cases w with
    | zero => simp [varIndex] at h
    | succ w =>
      have e : varIndex v = varIndex w := Nat.add_right_cancel h
      exact congrArg Var.succ (ih e)

inductive Raw (K : Type) where
  | var (n : Nat)
  | const (c : K)
  | app (σ : Ty) (f a : Raw K)
  | lam (b : Raw K)
  | and | or | not
  | all (σ : Ty) | ex (σ : Ty) | eq (σ : Ty)
  | constR (ρ : RTy) | negR (ρ : RTy) | andR (ρ : RTy)
  | orR (ρ : RTy) | coextR (ρ : RTy) | boxR (ρ : RTy) | inclR (ρ : RTy)


def rawCode {K : Type} [Encodable K] : Raw K → Nat
  | .var n => Nat.pair 0 n
  | .const c => Nat.pair 1 (Encodable.encode c)
  | .app σ f a => Nat.pair 2 (Nat.pair (tyCode σ) (Nat.pair (rawCode f) (rawCode a)))
  | .lam b => Nat.pair 3 (rawCode b)
  | .and => Nat.pair 4 0
  | .or => Nat.pair 5 0
  | .not => Nat.pair 6 0
  | .all σ => Nat.pair 7 (tyCode σ)
  | .ex σ => Nat.pair 8 (tyCode σ)
  | .eq σ => Nat.pair 9 (tyCode σ)
  | .constR ρ => Nat.pair 10 (rtyCode ρ)
  | .negR ρ => Nat.pair 11 (rtyCode ρ)
  | .andR ρ => Nat.pair 12 (rtyCode ρ)
  | .orR ρ => Nat.pair 13 (rtyCode ρ)
  | .coextR ρ => Nat.pair 14 (rtyCode ρ)
  | .boxR ρ => Nat.pair 15 (rtyCode ρ)
  | .inclR ρ => Nat.pair 16 (rtyCode ρ)

theorem rawCode_injective {K : Type} [Encodable K] :
    Function.Injective (@rawCode K _) := by
  intro t
  induction t <;> intro u h <;> cases u <;> simp_all [rawCode, Nat.pair_eq_pair]

instance {K : Type} [Encodable K] : Countable (Raw K) := rawCode_injective.countable

def termRaw {Sig : Signature} : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Raw Sig.Const
  | _, _, .var v => .var (varIndex v)
  | _, _, .const c => .const c
  | _, _, @Term.app _ _ σ _ f a => .app σ (termRaw f) (termRaw a)
  | _, _, .lam b => .lam (termRaw b)
  | _, _, .and => .and
  | _, _, .or => .or
  | _, _, .not => .not
  | _, _, .all σ => .all σ
  | _, _, .ex σ => .ex σ
  | _, _, .eq σ => .eq σ
  | _, _, .constR ρ => .constR ρ
  | _, _, .negR ρ => .negR ρ
  | _, _, .andR ρ => .andR ρ
  | _, _, .orR ρ => .orR ρ
  | _, _, .coextR ρ => .coextR ρ
  | _, _, .boxR ρ => .boxR ρ
  | _, _, .inclR ρ => .inclR ρ

theorem termRaw_injective {Sig : Signature} {Γ : Ctx} {σ : Ty} :
    Function.Injective (@termRaw Sig Γ σ) := by
  intro t
  induction t <;> intro u h <;> cases u <;> simp_all [termRaw]
  all_goals first
    | exact congrArg Term.var (varIndex_injective h)
    | aesop

instance {Sig : Signature} [Encodable Sig.Const] {Γ : Ctx} {σ : Ty} :
    Countable (Term Sig Γ σ) :=
  (termRaw_injective (Sig := Sig) (Γ := Γ) (σ := σ)).countable

end CentralSyntax
end Classicism.Meta
