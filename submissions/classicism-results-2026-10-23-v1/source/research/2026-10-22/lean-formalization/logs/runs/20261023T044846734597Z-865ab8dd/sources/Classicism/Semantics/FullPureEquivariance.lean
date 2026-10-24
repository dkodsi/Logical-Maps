import Classicism.Semantics.Relational
import Classicism.Syntax.Conservativity

/-!
# Pure-term equivariance in the existing full one-world interpretation

Ordinary classical Lean metatheory, using the actual `Term.denote` and full
relational domains of Semantics/Denotation and Semantics/Relational. Every
constructor, including quantifiers, lambda abstraction, equality and the seven
recursive relational operations, is covered. No choice operator is added to
the object language. Permutations need not preserve nonlogical constants.

Source: research/2026-10-22/central-questions-audit.md, "Independence holds",
and notes/homogeneity-amalgamation-lane.md §7 (original research, unpaginated;
direct source misc). This file is a new proof, not an attributed published proof.
-/

namespace Classicism.Meta.FullPure

/-- An external bijection, with both inverse laws explicit. -/
structure Perm (E : Type) where
  toFun : E → E
  invFun : E → E
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x

def Perm.symm {E : Type} (p : Perm E) : Perm E :=
  ⟨p.invFun, p.toFun, p.right_inv, p.left_inv⟩

@[simp] theorem Perm.symm_symm {E : Type} (p : Perm E) : p.symm.symm = p := rfl

mutual
  def moveT {E : Type} (p : Perm E) : ∀ σ : Ty, σ.denote E → σ.denote E
    | .e, x => p.toFun x
    | .var _, x => p.toFun x
    | .rel ρ, x => moveR p ρ x
  def moveR {E : Type} (p : Perm E) : ∀ ρ : RTy, ρ.denote E → ρ.denote E
    | .t, q => q
    | .arr σ ρ, f => fun x => moveR p ρ (f (moveT p.symm σ x))
end

mutual
  @[simp] theorem moveT_left {E : Type} (p : Perm E) :
      ∀ (σ : Ty) (x : σ.denote E), moveT p.symm σ (moveT p σ x) = x
    | .e, x => p.left_inv x
    | .var _, x => p.left_inv x
    | .rel ρ, x => moveR_left p ρ x
  @[simp] theorem moveR_left {E : Type} (p : Perm E) :
      ∀ (ρ : RTy) (x : ρ.denote E), moveR p.symm ρ (moveR p ρ x) = x
    | .t, x => rfl
    | .arr σ ρ, f => by
      funext x
      change moveR p.symm ρ (moveR p ρ (f (moveT p.symm σ (moveT p σ x)))) = f x
      rw [moveT_left, moveR_left]
end

@[simp] theorem moveT_right {E : Type} (p : Perm E) (σ : Ty) (x : σ.denote E) :
    moveT p σ (moveT p.symm σ x) = x := moveT_left p.symm σ x

@[simp] theorem moveR_right {E : Type} (p : Perm E) (ρ : RTy) (x : ρ.denote E) :
    moveR p ρ (moveR p.symm ρ x) = x := moveR_left p.symm ρ x

theorem moveT_injective {E : Type} (p : Perm E) (σ : Ty)
    {x y : σ.denote E} (h : moveT p σ x = moveT p σ y) : x = y := by
  have h' := congrArg (moveT p.symm σ) h
  simpa only [moveT_left] using h'

theorem forall_move {E : Type} (p : Perm E) (σ : Ty) (F : σ.denote E → Prop) :
    (∀ x, F (moveT p σ x)) = (∀ x, F x) := by
  apply propext
  constructor
  · intro h x
    have hx := h (moveT p.symm σ x)
    simpa only [moveT_right] using hx
  · intro h x
    exact h _

theorem exists_move {E : Type} (p : Perm E) (σ : Ty) (F : σ.denote E → Prop) :
    (∃ x, F (moveT p σ x)) = (∃ x, F x) := by
  apply propext
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨moveT p.symm σ x, ?_⟩
    simpa only [moveT_right] using hx

theorem move_const {E : Type} (p : Perm E) : ∀ (ρ : RTy) (q : Prop),
    moveR p ρ (RTy.constD E ρ q) = RTy.constD E ρ q
  | .t, _ => rfl
  | .arr _ ρ, q => by funext x; exact move_const p ρ q

theorem move_neg {E : Type} (p : Perm E) : ∀ (ρ : RTy) (X : ρ.denote E),
    moveR p ρ (RTy.negD E ρ X) = RTy.negD E ρ (moveR p ρ X)
  | .t, _ => rfl
  | .arr _ ρ, X => by funext x; exact move_neg p ρ _

theorem move_and {E : Type} (p : Perm E) : ∀ (ρ : RTy) (X Y : ρ.denote E),
    moveR p ρ (RTy.andD E ρ X Y) = RTy.andD E ρ (moveR p ρ X) (moveR p ρ Y)
  | .t, _, _ => rfl
  | .arr _ ρ, X, Y => by funext x; exact move_and p ρ _ _

theorem move_or {E : Type} (p : Perm E) : ∀ (ρ : RTy) (X Y : ρ.denote E),
    moveR p ρ (RTy.orD E ρ X Y) = RTy.orD E ρ (moveR p ρ X) (moveR p ρ Y)
  | .t, _, _ => rfl
  | .arr _ ρ, X, Y => by funext x; exact move_or p ρ _ _

theorem move_box {E : Type} (p : Perm E) : ∀ (ρ : RTy) (X : ρ.denote E),
    moveR p ρ (RTy.boxD E ρ X) = RTy.boxD E ρ (moveR p ρ X)
  | .t, _ => rfl
  | .arr _ ρ, X => by funext x; exact move_box p ρ _

theorem coext_move {E : Type} (p : Perm E) : ∀ (ρ : RTy) (X Y : ρ.denote E),
    RTy.coextD E ρ (moveR p ρ X) (moveR p ρ Y) = RTy.coextD E ρ X Y
  | .t, _, _ => rfl
  | .arr σ ρ, X, Y => by
    change (∀ x, RTy.coextD E ρ (moveR p ρ (X (moveT p.symm σ x)))
      (moveR p ρ (Y (moveT p.symm σ x)))) = (∀ x, RTy.coextD E ρ (X x) (Y x))
    simp only [coext_move]
    exact forall_move p.symm σ (fun x => RTy.coextD E ρ (X x) (Y x))

theorem incl_move {E : Type} (p : Perm E) : ∀ (ρ : RTy) (X Y : ρ.denote E),
    RTy.inclD E ρ (moveR p ρ X) (moveR p ρ Y) = RTy.inclD E ρ X Y
  | .t, _, _ => rfl
  | .arr σ ρ, X, Y => by
    change (∀ x, RTy.inclD E ρ (moveR p ρ (X (moveT p.symm σ x)))
      (moveR p ρ (Y (moveT p.symm σ x)))) = (∀ x, RTy.inclD E ρ (X x) (Y x))
    simp only [incl_move]
    exact forall_move p.symm σ (fun x => RTy.inclD E ρ (X x) (Y x))

def moveEnv {E : Type} (p : Perm E) : ∀ {Γ : Ctx}, Env E Γ → Env E Γ
  | _, .nil => .nil
  | _, .cons (σ := σ) x env => .cons (moveT p σ x) (moveEnv p env)

theorem var_move {E : Type} (p : Perm E) : ∀ {Γ : Ctx} {σ : Ty}
    (v : Var Γ σ) (env : Env E Γ), v.denote (moveEnv p env) = moveT p σ (v.denote env)
  | _, _, .zero, .cons _ _ => rfl
  | _, _, .succ v, .cons _ env => var_move p v env

/-- Every pure term of the actual syntax is equivariant, at arbitrary environments. -/
theorem denote_pure_move {Sig : Signature} (I : Interp Sig) (p : Perm I.D) :
    ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ), t.pure = true →
      ∀ env : Env I.D Γ,
        t.denote I (moveEnv p env) = moveT p σ (t.denote I env)
  | _, _, .var v, _, env => var_move p v env
  | _, _, .const _, hp, _ => by simp [Term.pure] at hp
  | _, _, .app f t, hp, env => by
    have h := Bool.and_eq_true.mp hp
    change f.denote I (moveEnv p env) (t.denote I (moveEnv p env)) = _
    rw [denote_pure_move I p f h.1, denote_pure_move I p t h.2]
    change moveR p _ (f.denote I env (moveT p.symm _ (moveT p _ (t.denote I env)))) = _
    rw [moveT_left]
  | _, _, .lam b, hp, env => by
    funext x
    have h := denote_pure_move I p b hp (.cons (moveT p.symm _ x) env)
    simpa only [moveEnv, moveT_right, moveT] using h
  | _, _, .and, _, _ | _, _, .or, _, _ | _, _, .not, _, _ => rfl
  | _, _, .all σ, _, _ => by
    funext F
    exact (forall_move p σ F).symm
  | _, _, .ex σ, _, _ => by
    funext F
    exact (exists_move p σ F).symm
  | _, _, .eq σ, _, _ => by
    funext x y
    exact propext ⟨fun h => congrArg (moveT p.symm σ) h,
      fun h => moveT_injective p.symm σ h⟩
  | _, _, .constR ρ, _, _ => by
    funext q
    exact (move_const p ρ q).symm
  | _, _, .negR ρ, _, _ => by
    funext X
    change RTy.negD I.D ρ X = moveR p ρ (RTy.negD I.D ρ (moveR p.symm ρ X))
    rw [move_neg, moveR_right]
  | _, _, .andR ρ, _, _ => by
    funext X Y
    change RTy.andD I.D ρ X Y = moveR p ρ
      (RTy.andD I.D ρ (moveR p.symm ρ X) (moveR p.symm ρ Y))
    rw [move_and, moveR_right, moveR_right]
  | _, _, .orR ρ, _, _ => by
    funext X Y
    change RTy.orD I.D ρ X Y = moveR p ρ
      (RTy.orD I.D ρ (moveR p.symm ρ X) (moveR p.symm ρ Y))
    rw [move_or, moveR_right, moveR_right]
  | _, _, .coextR ρ, _, _ => by
    funext X Y
    exact (coext_move p.symm ρ X Y).symm
  | _, _, .boxR ρ, _, _ => by
    funext X
    change RTy.boxD I.D ρ X = moveR p ρ (RTy.boxD I.D ρ (moveR p.symm ρ X))
    rw [move_box, moveR_right]
  | _, _, .inclR ρ, _, _ => by
    funext X Y
    exact (incl_move p.symm ρ X Y).symm

theorem closed_pure_fixed {Sig : Signature} (I : Interp Sig) (p : Perm I.D)
    {σ : Ty} (t : Term Sig [] σ) (hp : t.pure = true) :
    moveT p σ (t.denote I .nil) = t.denote I .nil :=
  (denote_pure_move I p t hp .nil).symm

/-- A moved predicate cannot be the value of any closed pure term. -/
theorem moved_predicate_not_pure {Sig : Signature} (I : Interp Sig) (p : Perm I.D)
    (A : I.D → Prop) (hm : moveR p (.arr .e .t) A ≠ A)
    (t : Term Sig [] (Ty.e ⇒ RTy.t)) (hp : t.pure = true) : t.denote I .nil ≠ A := by
  intro ht
  have hf := closed_pure_fixed I p t hp
  rw [ht] at hf
  exact hm hf

end Classicism.Meta.FullPure
