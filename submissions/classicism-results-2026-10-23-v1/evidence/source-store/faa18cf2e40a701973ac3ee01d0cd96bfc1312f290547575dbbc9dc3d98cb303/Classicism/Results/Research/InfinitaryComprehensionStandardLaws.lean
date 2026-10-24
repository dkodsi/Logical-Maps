import Classicism.Results.Research.InfinitaryComprehensionFull

/-!
# Intensionality and the modal laws in full standard hierarchies

Direct source: `research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md`, section 4, misc, 23 October 2026, unpaginated.

These are semantic validity theorems about concrete object formulas. They
complement `Term.full_comprehension`; they do not assert a completeness or
representation theorem for arbitrary C5 models. Lean's ordinary extensional
metatheory is used to identify elements of the full function domains.
-/

namespace Classicism.Research.InfinitaryComprehension
open Classicism.Meta

universe u v

/-- Pointwise coextension of the full relational interpretations at a world. -/
def FullCoext (E W : Type v) : (ρ : RTy) →
    FullRel E W ρ → FullRel E W ρ → W → Prop
  | .t, p, q, w => p w ↔ q w
  | .arr σ ρ, X, Y, w => ∀ x : FullTy E W σ, FullCoext E W ρ (X x) (Y x) w

/-- Necessary coextension identifies the entire intension, at every type. -/
theorem full_coext_intensionality (E W : Type v) (ρ : RTy)
    (X Y : FullRel E W ρ) (h : ∀ w, FullCoext E W ρ X Y w) : X = Y := by
  induction ρ using RTy.induction with
  | t =>
      exact funext (fun w => propext (h w))
  | arr σ ρ ih =>
      funext x
      exact ih (X x) (Y x) (fun w => h w x)

namespace Term

variable {Param : Ty → Type u} {E W : Type v}

/-- Coextension is a finite object formula, recursively following its type. -/
def coext {Γ : Ctx} : (ρ : RTy) → Term Param Γ ρ → Term Param Γ ρ → Formula Param Γ
  | .t, p, q => .iff p q
  | .arr σ ρ, X, Y =>
      .all (coext ρ
        (.app (X.rename (fun v => .succ v)) (.var .zero))
        (.app (Y.rename (fun v => .succ v)) (.var .zero)))

theorem eval_coext (η : Assignment Param E W) (ρ : RTy) :
    ∀ {Γ : Ctx} (X Y : Term Param Γ ρ) (env : Env E W Γ) (w : W),
      eval η (coext ρ X Y) env w ↔
        FullCoext E W ρ (eval η X env) (eval η Y env) w := by
  induction ρ using RTy.induction with
  | t => intros; exact Iff.rfl
  | arr σ ρ ih =>
      intro Γ X Y env w
      change (∀ x : FullTy E W σ,
        eval η (coext ρ
          (.app (X.rename (fun v => .succ v)) (.var .zero))
          (.app (Y.rename (fun v => .succ v)) (.var .zero))) (Env.cons x env) w) ↔ _
      have hx (x : FullTy E W σ) :
          eval η (X.rename (fun v => .succ v)) (Env.cons x env) = eval η X env :=
        eval_rename η X (fun v => .succ v) env (Env.cons x env) (fun _ => rfl)
      have hy (x : FullTy E W σ) :
          eval η (Y.rename (fun v => .succ v)) (Env.cons x env) = eval η Y env :=
        eval_rename η Y (fun v => .succ v) env (Env.cons x env) (fun _ => rfl)
      constructor
      · intro h x
        have hi := (ih _ _ (Env.cons x env) w).1 (h x)
        simpa only [eval, hx x, hy x, Env.cons] using hi
      · intro h x
        apply (ih _ _ (Env.cons x env) w).2
        simpa only [eval, hx x, hy x, Env.cons] using h x

/-- The actual all-relational Intensionality instance. -/
theorem eval_intensionality (η : Assignment Param E W) {Γ : Ctx}
    (ρ : RTy) (X Y : Term Param Γ ρ) (env : Env E W Γ) (w : W) :
    eval η (.imp (.box (coext ρ X Y)) (.eq X Y)) env w := by
  change (∀ v, eval η (coext ρ X Y) env v) → eval η X env = eval η Y env
  intro h
  exact full_coext_intensionality E W ρ _ _ (fun v => (eval_coext η ρ X Y env v).1 (h v))

theorem eval_K (η : Assignment Param E W) {Γ : Ctx}
    (p q : Formula Param Γ) (env : Env E W Γ) (w : W) :
    eval η (.imp (.box (.imp p q)) (.imp p.box q.box)) env w := by
  change (∀ v, eval η p env v → eval η q env v) →
    (∀ v, eval η p env v) → ∀ v, eval η q env v
  exact fun h hp v => h v (hp v)

theorem eval_T (η : Assignment Param E W) {Γ : Ctx}
    (p : Formula Param Γ) (env : Env E W Γ) (w : W) :
    eval η (.imp p.box p) env w := by
  change (∀ v, eval η p env v) → eval η p env w
  exact fun h => h w

theorem eval_four (η : Assignment Param E W) {Γ : Ctx}
    (p : Formula Param Γ) (env : Env E W Γ) (w : W) :
    eval η (.imp p.box p.box.box) env w := by
  change (∀ v, eval η p env v) → ∀ _v, ∀ z, eval η p env z
  exact fun h _ z => h z

/-- Global validity, rather than truth under a local premise, is necessitated. -/
theorem eval_necessitation (η : Assignment Param E W) {Γ : Ctx}
    (p : Formula Param Γ) (env : Env E W Γ)
    (h : ∀ w, eval η p env w) (w : W) : eval η p.box env w := h

/-- The closed-in-x,y instance of Necessity of Distinctness. -/
def necessaryDistinctness (σ : Ty) {Γ : Ctx} : Formula Param Γ :=
  .all (σ := σ) (.all (σ := σ)
    (.imp (.neg (.eq (.var (.succ .zero)) (.var .zero)))
      (.box (.neg (.eq (.var (.succ .zero)) (.var .zero))))))

/-- C5 is boxed ND, not merely ND at the designated world. -/
theorem eval_C5 (η : Assignment Param E W) {Γ : Ctx}
    (σ : Ty) (env : Env E W Γ) (w : W) :
    eval η (.box (necessaryDistinctness (Param := Param) σ)) env w := by
  change ∀ _v : W, ∀ x y : FullTy E W σ, x ≠ y → ∀ _z : W, x ≠ y
  exact fun _ _ _ h _ => h

/-- The defining modal equation is valid with literal propositional identity. -/
theorem eval_box_eq_top (η : Assignment Param E W) {Γ : Ctx}
    (p : Formula Param Γ) (env : Env E W Γ) (w : W) :
    eval η (.iff p.box (.eq p .top)) env w := by
  change (∀ v, eval η p env v) ↔ (eval η p env = fun _ => True)
  constructor
  · intro h
    exact funext (fun v => propext ⟨fun _ => trivial, fun _ => h v⟩)
  · intro h v
    have hv := congrFun h v
    exact Eq.mpr hv trivial

end Term

#print axioms full_coext_intensionality
#print axioms Term.eval_intensionality
#print axioms Term.eval_C5
#print axioms Term.eval_box_eq_top

end Classicism.Research.InfinitaryComprehension
