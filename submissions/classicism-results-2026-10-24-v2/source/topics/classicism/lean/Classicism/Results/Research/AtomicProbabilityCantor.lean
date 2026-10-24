import Classicism.Results.Research.ActualityCoreGraphs

/-!
# A represented Cantor diagonal in the actual supported core

This is the actual fixed-type C diagonal needed at the end of the finite-fibre
Cantor/type-ceiling proof. The predicate domain is the represented supported
interval Domain w D. No full external powerset, external Nat, Choice, injective
selection operation, or previously assumed Cantor theorem occurs.

Only current truth of w is needed; ActualWorld w supplies it in applications.
This does not yet prove that finite-fibre labelling of the predicate domain
produces an injection. That earlier finite-block/rank step remains separate.

Source: proof-refinements/choice-free-probability-type-ceiling.md, section 1.
-/

namespace Classicism.Research.ProbabilityCantor
open Classicism.Paper Classicism.P
open Classicism.Research.ActualityCore

variable {σ : Type} [Ty σ]

def diagonal (w : Prop) (D : σ → Prop) (G : (σ → Prop) → σ → Prop) : σ → Prop :=
  fun a => w ∧ D a ∧ ¬ ∃ P, Domain w D P ∧ G P a ∧ P a

theorem diagonal_below (w : Prop) (D : σ → Prop) (G : (σ → Prop) → σ → Prop) :
    diagonal w D G ≤ D :=
  le_of_box_incl (nec% (fun (a : σ) (h : diagonal w D G a) => h.2.1))

/-- No represented relation can inject every admitted supported predicate into D.
The relation need not be single-valued in the forward direction. -/
theorem no_predicate_injection (w : Prop) (hw : w) (D : σ → Prop)
    (G : (σ → Prop) → σ → Prop)
    (ht : ∀ P, Domain w D P → ∃ a, D a ∧ G P a)
    (hi : ∀ P Q a, Domain w D P → Domain w D Q → D a →
      G P a → G Q a → P = Q) : False := by
  have hdelta : Domain w D (diagonal w D G) := ⟨hw, diagonal_below w D G⟩
  obtain ⟨a, ha, hGa⟩ := ht (diagonal w D G) hdelta
  have hn : ¬ diagonal w D G a := by
    intro h
    exact h.2.2 ⟨diagonal w D G, hdelta, hGa, h⟩
  apply hn
  refine ⟨hw, ha, ?_⟩
  intro hex
  obtain ⟨P, hP, hPa, hval⟩ := hex
  have he : P = diagonal w D G := hi P (diagonal w D G) a hP hdelta ha hPa hGa
  exact hn (he ▸ hval)

/-- The same obstruction in the shared graph vocabulary. -/
theorem no_serial_injective_predicate_graph (w : Prop) (hw : w) (D : σ → Prop)
    (G : (σ → Prop) → σ → Prop) :
    ¬ (SerialOn (Domain w D) D G ∧ InjectiveOn (Domain w D) D G) := by
  intro h
  exact no_predicate_injection w hw D G h.1 h.2

end Classicism.Research.ProbabilityCantor
