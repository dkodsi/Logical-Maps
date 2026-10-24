import Classicism.Results.Research.FiniteFunctionFields
import Classicism.Results.Research.C5Frege

/-!
# Actual domain finiteness and its arrow step

Direct source: research/2026-10-22/proof-refinements/finite-type-propagation.md,
§§1–3, unpaginated original research (misc). Optional Functionality or Barcan
stays explicit. The companion schema module inducts on closed type codes;
these definitions introduce no object-language quantifier over types.
-/
namespace Classicism.Research.FiniteTypePropagation
open Classicism.Research.FregeFiniteSets
open Classicism.Research.FiniteFunctionFields
open Classicism.Paper

def FiniteDomain (σ : Type) [Ty σ] : Prop := Finite (fun _ : σ => True)

def FiniteRelDomain (ρ : Type) [Rel ρ] : Prop := FiniteDomain ρ

def NecessaryFiniteDomain (σ : Type) [Ty σ] : Prop := □ (FiniteDomain σ)

theorem finite_domain_necessary_c5 {σ : Type} [Ty σ] :
    Classicism.P.NecNecessityOfDistinctnessT → FiniteDomain σ →
      NecessaryFiniteDomain σ := by
  intro c5 hf
  obtain ⟨n, hn, htop⟩ := hf
  have hnbox := frege_number_persistent n hn
  have htopbox := (C5Frege.persistent_count_settled c5 n hn (fun _ => True)
    C5Frege.top_persistent).1 htop
  exact modal_K _ _ (modal_K _ _
    (nec% (fun (hN : FiniteCardinality n) (hX : n (fun _ => True)) =>
      (show FiniteDomain σ from ⟨n, hN, hX⟩))) hnbox) htopbox

theorem finite_domain_of_necessary {σ : Type} [Ty σ] :
    NecessaryFiniteDomain σ → FiniteDomain σ := modal_T _

theorem finite_arrow_of_functionality {σ ρ : Type} [Ty σ] [Rel ρ] :
    Classicism.P.Functionality σ ρ → FiniteDomain σ → FiniteDomain ρ →
      FiniteDomain (σ → ρ) :=
  finite_functions_of_finite_domains

theorem finite_arrow_of_barcan {σ ρ : Type} [Ty σ] [Rel ρ] :
    Classicism.P.Barcan σ → FiniteDomain σ → FiniteDomain ρ →
      FiniteDomain (σ → ρ) :=
  finite_functions_of_barcan

theorem finite_arrow_of_c5 {σ ρ : Type} [Ty σ] [Rel ρ] :
    Classicism.P.NecNecessityOfDistinctnessT → FiniteDomain σ → FiniteDomain ρ →
      FiniteDomain (σ → ρ) :=
  fun c5 => finite_functions_of_barcan (Classicism.Proofs.bf_of_box_nd_t c5)

theorem finite_base_of_finite_predicates {σ : Type} [Ty σ] :
    FiniteRelDomain (σ → Prop) → FiniteDomain σ :=
  finite_input_of_finite_predicates

theorem finite_rel_domain {ρ : Type} [Rel ρ] :
    FiniteDomain ρ → FiniteRelDomain ρ := fun h => h

theorem finite_domain_of_rel {ρ : Type} [Rel ρ] :
    FiniteRelDomain ρ → FiniteDomain ρ := fun h => h

end Classicism.Research.FiniteTypePropagation
