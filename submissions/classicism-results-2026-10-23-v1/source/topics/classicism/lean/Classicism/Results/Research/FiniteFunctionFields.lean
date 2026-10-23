import Classicism.Results.Research.FiniteRigidPowers
import Classicism.Results.Records.Coarse

/-!
# Actual finite function fields and the precise Functionality premise

Direct sources: research/2026-10-22/notes/finite-c5-profile-cells-20261022.md,
§3 (finite application tables); relational-coding-recursion-20261022.md §27.1–2
(internal finite pattern separation), unpaginated original research, misc.
The proof below upgrades the finite-table step to quantified Frege finiteness.
It counts admitted operations by their value identities. Current Functionality
is explicitly required to identify operations agreeing on every input.
An input witness is explicit where evaluation of a constant operation needs it.
-/
namespace Classicism.Research.FiniteFunctionFields
open Classicism.Paper Classicism.P
open Classicism.Research.FregeFiniteSets
open Classicism.Research.FiniteRigidPowers

variable {σ : Type} [Ty σ] {τ : Type} [Rel τ]

theorem finite_function_family (A : σ → Prop) (B : τ → Prop)
    (H : (σ → τ) → Prop) (hA : Finite A) (hB : Finite B)
    (hvalues : ∀ f, H f → ∀ x, A x → B (f x))
    (hsep : ∀ f g, H f → H g → (∀ x, A x → f x = g x) → f = g) :
    Finite H := by
  apply finite_separated_family (PairCodes A B) H
    (fun c f => PairRead c (fun x y => f x = y)) (finite_pairCodes A B hA hB)
  intro f g hf hg he
  apply hsep f g hf hg
  intro x hx
  have hcode : PairCodes A B (PairCode x (f x)) :=
    ⟨x, hx, f x, hvalues f hf x hx, rfl⟩
  have h := (he (PairCode x (f x)) hcode).1
    (show PairRead (PairCode x (f x)) (fun u y => f u = y) from ⟨x, f x, rfl, rfl⟩)
  exact ((pairRead_value x (f x) (fun u y => g u = y)).1 h).symm

theorem finite_functions_of_finite_domains (hf : Functionality σ τ)
    (hσ : Finite (fun _ : σ => True)) (hτ : Finite (fun _ : τ => True)) :
    Finite (fun _ : σ → τ => True) :=
  finite_function_family (fun _ => True) (fun _ => True) (fun _ => True) hσ hτ
    (fun _ _ _ _ => True.intro)
    (fun f g _ _ he => hf f g (fun x => he x True.intro))

theorem finite_functions_of_barcan (bf : Barcan σ)
    (hσ : Finite (fun _ : σ => True)) (hτ : Finite (fun _ : τ => True)) :
    Finite (fun _ : σ → τ => True) :=
  finite_functions_of_finite_domains (Proofs.barcan_r_implies_functionality_r bf) hσ hτ

theorem finite_output_of_finite_functions (a : σ)
    (hf : Finite (fun _ : σ → τ => True)) : Finite (fun _ : τ => True) := by
  apply finite_injection_domain (fun _ => True) (fun _ : σ → τ => True)
    (fun y f => f = (fun _ : σ => y)) hf
  · intro y _
    exact ⟨(fun _ => y), True.intro, rfl⟩
  · intro y z f _ _ hy hz
    exact congrFun (hy.symm.trans hz) a

theorem finite_input_of_finite_predicates
    (hf : Finite (fun _ : σ → Prop => True)) : Finite (fun _ : σ => True) := by
  apply finite_injection_domain (fun _ => True) (fun _ : σ → Prop => True)
    (fun a X => X = (fun x => x = a)) hf
  · intro a _
    exact ⟨(fun x => x = a), True.intro, rfl⟩
  · intro a b X _ _ ha hb
    exact Eq.mp (congrFun (ha.symm.trans hb) a) rfl

theorem finite_predicates_iff (a : σ) (bf : Barcan σ) :
    Finite (fun _ : σ → Prop => True) ↔
      Finite (fun _ : σ => True) ∧ Finite (fun _ : Prop => True) :=
  ⟨fun hf => ⟨finite_input_of_finite_predicates hf, finite_output_of_finite_functions a hf⟩,
   fun h => finite_functions_of_barcan bf h.1 h.2⟩

theorem infinity_functions_of_infinity_output (a : σ) (hi : AxiomOfInfinity τ) :
    AxiomOfInfinity (σ → τ) :=
  fun hf => hi (finite_output_of_finite_functions a hf)

theorem infinity_predicates_of_infinity_input (hi : AxiomOfInfinity σ) :
    AxiomOfInfinity (σ → Prop) :=
  fun hf => hi (finite_input_of_finite_predicates hf)

theorem infinity_predicates_iff (a : σ) (bf : Barcan σ) :
    AxiomOfInfinity (σ → Prop) ↔ AxiomOfInfinity σ ∨ AxiomOfInfinity Prop := by
  constructor
  · intro hi
    exact (em (Finite (fun _ : σ => True))).elim
      (fun hσ => Or.inr (fun ht => hi (finite_functions_of_barcan bf hσ ht))) Or.inl
  · intro hi
    exact hi.elim infinity_predicates_of_infinity_input
      (infinity_functions_of_infinity_output a)

end Classicism.Research.FiniteFunctionFields
