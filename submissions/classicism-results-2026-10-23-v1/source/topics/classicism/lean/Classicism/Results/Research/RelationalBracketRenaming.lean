import Classicism.Results.Research.RelationalBracketAbstraction

/-!
# Renaming and fresh-argument beta for relational bracket abstraction

Original research, misc, 23 October 2026. Renaming preserves the algorithm's
variable cases, so this is a literal syntax identity. Arbitrary substitution
does not have that property and is deliberately not asserted here.
-/

namespace Classicism.Research.RelationalBracketAbstraction
open Classicism.Meta (Ty RTy Ctx Var Ren)

namespace Term
variable {Const : Ty → Type}

theorem bracket_rename : {Γ Δ : Ctx} → {σ : Ty} → {ρ : RTy} →
    (r : Ren Γ Δ) → (M : Term Const (σ :: Γ) ρ) →
    (M.rename (Classicism.Meta.Ren.lift r)).bracket = M.bracket.rename r
  | _, _, _, _, _, .var .zero => by
      simp only [rename, Classicism.Meta.Ren.lift, bracket]
  | _, _, _, _, _, .var (.succ _) => by
      simp only [rename, Classicism.Meta.Ren.lift, bracket]
  | _, _, _, _, _, .const _ => by
      simp only [rename, bracket]
  | _, _, _, _, r, @Term.app _ _ (.rel _) _ f a => by
      simp only [rename, bracket, bracket_rename r f, bracket_rename r a]
  | _, _, _, _, r, @Term.app _ _ .e _ f (.var .zero) => by
      simp only [rename, Classicism.Meta.Ren.lift, bracket, bracket_rename r f]
  | _, _, _, _, r, @Term.app _ _ .e _ f (.var (.succ _)) => by
      simp only [rename, Classicism.Meta.Ren.lift, bracket, bracket_rename r f]
  | _, _, _, _, r, @Term.app _ _ .e _ f (.const _) => by
      simp only [rename, bracket, bracket_rename r f]
  | _, _, _, _, r, @Term.app _ _ (.var _) _ f (.var .zero) => by
      simp only [rename, Classicism.Meta.Ren.lift, bracket, bracket_rename r f]
  | _, _, _, _, r, @Term.app _ _ (.var _) _ f (.var (.succ _)) => by
      simp only [rename, Classicism.Meta.Ren.lift, bracket, bracket_rename r f]
  | _, _, _, _, r, @Term.app _ _ (.var _) _ f (.const _) => by
      simp only [rename, bracket, bracket_rename r f]

theorem instantiate_at_fresh {Γ σ τ} (M : Term Const (σ :: Γ) τ) :
    (M.rename (Classicism.Meta.Ren.lift
      (Classicism.Meta.Ren.shift (σ := σ)))).inst (.var .zero) = M := by
  rw [inst, subst_rename]
  have hs :
      (fun υ (v : Var (σ :: Γ) υ) =>
        Sub.cons (.var (.zero : Var (σ :: Γ) σ)) Sub.id υ
          (Classicism.Meta.Ren.lift Classicism.Meta.Ren.shift υ v)) =
        (Sub.id : Sub Const (σ :: Γ) (σ :: Γ)) := by
    funext υ v
    cases v <;> rfl
  rw [hs, subst_id]

/-- The implemented abstraction, weakened to a fresh argument, has exactly
the original open body as its beta value. -/
theorem bracket_fresh_beta {Γ σ} {ρ : RTy} (M : Term Const (σ :: Γ) ρ) :
    Equal Const (.app M.bracket.wk (.var .zero)) M := by
  have h := bracket_beta
    (M.rename (Classicism.Meta.Ren.lift
      (Classicism.Meta.Ren.shift (σ := σ)))) (.var .zero)
  simpa only [bracket_rename, instantiate_at_fresh, wk] using h

end Term

#print axioms Term.bracket_rename
#print axioms Term.bracket_fresh_beta

end Classicism.Research.RelationalBracketAbstraction
