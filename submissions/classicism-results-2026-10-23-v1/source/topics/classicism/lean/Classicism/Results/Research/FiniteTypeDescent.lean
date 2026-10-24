import Classicism.Results.Research.FiniteTypePropagation

/-!
# Finiteness descends through admitted operation types

Direct source: research/2026-10-22/proof-refinements/finite-type-propagation.md,
§6 and its argument-deletion refinement, unpaginated original research (misc).
Inhabitation remains explicit; no Functionality or choice is used below.
-/
namespace Classicism.Research.FiniteTypeDescent
open Classicism.Research.FregeFiniteSets
open Classicism.Research.FiniteFunctionFields
open Classicism.Research.FiniteTypePropagation

theorem finite_output_of_arrow {σ ρ : Type} [Ty σ] [Rel ρ] :
    Classicism.P.Existence σ → FiniteDomain (σ → ρ) → FiniteDomain ρ := by
  rintro ⟨a, _⟩ hf
  exact finite_output_of_finite_functions a hf

theorem finite_input_of_predicate {σ : Type} [Ty σ] :
    FiniteDomain (σ → Prop) → FiniteDomain σ :=
  finite_input_of_finite_predicates

theorem finite_delete_output_argument {σ τ ρ : Type} [Ty σ] [Ty τ] [Rel ρ] :
    Classicism.P.Existence τ → FiniteDomain (σ → τ → ρ) →
      FiniteDomain (σ → ρ) := by
  rintro ⟨a, _⟩ hf
  apply finite_injection_domain (fun _ : σ → ρ => True)
    (fun _ : σ → τ → ρ => True)
    (fun f h => h = (fun x _ => f x)) hf
  · intro f _
    exact ⟨(fun x _ => f x), True.intro, rfl⟩
  · intro f g h _ _ hF hG
    have he := congrArg (fun (k : σ → τ → ρ) x => k x a) (hF.symm.trans hG)
    exact he

end Classicism.Research.FiniteTypeDescent
