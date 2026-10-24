import Classicism.Results.Research.InfinitaryComprehensionSupport

/-!
# Infinitary Comprehension and fullness on canonical presentations

Direct source: `research/2026-10-23/infinitary-comprehension/
infinitary-comprehension.md`, section 4, misc, 23 October 2026, unpaginated.

All fullness properties below are conclusions, not fields of the model.
The representation assumptions of `Henkin.Model`, `Faithful`, and
`WorldSeparated` remain explicit. This does not supply the separate
abstract-C5-to-canonical-presentation theorem.
-/

namespace Classicism.Research.InfinitaryComprehension.Henkin
open Classicism.Meta

universe u
variable (M : Model.{u})

/-- Every set of world--tuple points is represented by an admitted relation. -/
def FullProfiles : Prop :=
  ∀ (Γ : Ctx) (U : M.World × Env M Γ → Prop),
    ∃ R : M.Dom (RTy.ofArgs Γ), ∀ (xs : Env M Γ) (v : M.World),
      M.truth (uncurry M Γ R xs) v ↔ U (v, xs)

/-- The reverse implication interprets each actual matrix; it needs no
faithfulness or separation premise. -/
theorem comp_of_full_profiles (h : FullProfiles M) (w : M.World) : Comp M w := by
  intro Param η Γ A
  apply (eval_comprehension_iff M η A w).2
  exact h Γ (fun z => M.truth (eval M η A z.2) z.1)

theorem comp_iff_full_profiles (w : M.World) (hf : Faithful M)
    (hs : WorldSeparated M) : Comp M w ↔ FullProfiles M :=
  ⟨fun hc Γ U => full_profiles M hc hf hs Γ U,
    fun h => comp_of_full_profiles M h w⟩

/-- Full profiles supply every external function into a relational domain. -/
theorem full_functions_flat (h : FullProfiles M) (hf : Faithful M)
    (σ : Ty) (Γ : Ctx) (f : M.Dom σ → M.Dom (RTy.ofArgs Γ)) :
    ∃ R : M.Dom (σ ⇒ RTy.ofArgs Γ), ∀ x, M.app R x = f x := by
  obtain ⟨R, hR⟩ := h (σ :: Γ)
    (fun z => M.truth (uncurry M Γ (f (z.2 .zero)) (Env.tail z.2)) z.1)
  refine ⟨R, ?_⟩
  intro x
  apply hf Γ
  intro xs v
  exact hR (Env.cons x xs) v

/-- Faithfulness also gives uniqueness, so application is an actual full
function-space representation, not merely a surjective selection. -/
theorem application_injective_flat (hf : Faithful M) (σ : Ty) (Γ : Ctx)
    (R S : M.Dom (σ ⇒ RTy.ofArgs Γ))
    (h : ∀ x, M.app R x = M.app S x) : R = S := by
  apply hf (σ :: Γ)
  intro xs v
  change M.truth (uncurry M Γ (M.app R (xs .zero)) (Env.tail xs)) v ↔
    M.truth (uncurry M Γ (M.app S (xs .zero)) (Env.tail xs)) v
  rw [h (xs .zero)]

/-- All and only the allowed arrows are covered: their codomain is relational. -/
theorem functions_of_full_profiles (h : FullProfiles M) (hf : Faithful M)
    (σ : Ty) (ρ : RTy) :
    ∀ f : M.Dom σ → M.Dom ρ,
      ∃ R : M.Dom (σ ⇒ ρ), ∀ x, M.app R x = f x := by
  exact Eq.mp
    (congrArg (fun r : RTy => ∀ f : M.Dom σ → M.Dom r,
      ∃ R : M.Dom (σ ⇒ r), ∀ x, M.app R x = f x) (RTy.ofArgs_args ρ))
    (full_functions_flat M h hf σ ρ.args)

theorem application_injective (hf : Faithful M) (σ : Ty) (ρ : RTy) :
    ∀ R S : M.Dom (σ ⇒ ρ), (∀ x, M.app R x = M.app S x) → R = S := by
  exact Eq.mp
    (congrArg (fun r : RTy => ∀ R S : M.Dom (σ ⇒ r),
      (∀ x, M.app R x = M.app S x) → R = S) (RTy.ofArgs_args ρ))
    (application_injective_flat M hf σ ρ.args)

/-- The main full-arrow endpoint, with no fullness premise. -/
theorem comprehension_full_functions {w : M.World} (hc : Comp M w)
    (hf : Faithful M) (hs : WorldSeparated M) (σ : Ty) (ρ : RTy)
    (f : M.Dom σ → M.Dom ρ) :
    ∃ R : M.Dom (σ ⇒ ρ),
      (∀ x, M.app R x = f x) ∧
      ∀ S : M.Dom (σ ⇒ ρ), (∀ x, M.app S x = f x) → S = R := by
  have hp : FullProfiles M := (comp_iff_full_profiles M w hf hs).1 hc
  obtain ⟨R, hR⟩ := functions_of_full_profiles M hp hf σ ρ f
  refine ⟨R, hR, ?_⟩
  intro S hS
  exact application_injective M hf σ ρ S R (fun x => (hS x).trans (hR x).symm)

#print axioms comp_iff_full_profiles
#print axioms comprehension_full_functions

end Classicism.Research.InfinitaryComprehension.Henkin
