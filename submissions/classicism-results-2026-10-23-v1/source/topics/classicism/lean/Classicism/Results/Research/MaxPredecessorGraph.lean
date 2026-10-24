import Classicism.Results.Research.MaxPredecessor

/-! Direct source: relational-coding-recursion-20261022.md §38, misc.
The graph exists by comprehension; uniqueness needs arithmetic noncollapse.
The companion model certificate supplies that condition from pure Max at e. -/

namespace Classicism.Research.MaxPredecessorGraph
open Classicism.Research.FregeNoncollapse Classicism.Research.MaxPredecessor

variable {σ : Type} [Ty σ]

def Peano (σ : Type) [Ty σ] : Prop := IStar σ

def GraphClaim (σ : Type) [Ty σ] : Prop :=
  P.Functional (PredGraph (σ := σ)) ∧
    ¬ ∃ f : ((σ → Prop) → Prop) → (σ → Prop) → Prop,
      ∀ x, PredGraph x (f x)

theorem infinity_to_peano (h : P.AxiomOfInfinity σ) : Peano σ :=
  istar_iff_noncollapse.2 (infinity_implies_noncollapse h)

theorem graph_claim_of_I (hi : ArithmeticI σ) (hn : ¬ PredOp σ) : GraphClaim σ := by
  refine ⟨graph_functional hi, ?_⟩
  intro hf
  obtain ⟨f, hf⟩ := hf
  apply hn
  refine ⟨f, fun n hn => ?_⟩
  exact graph_single_valued (istar_iff_noncollapse.1 (arithmeticI_iff_istar.1 hi))
    (SucCard n) (f (SucCard n)) n (hf (SucCard n)) (graph_successor n hn)

theorem possible_peano_gives_graph (hi : ◇ (Peano σ)) (hn : ¬ PredOp σ) : GraphClaim σ :=
  graph_claim_of_I hi hn

theorem possible_peano_refutes_plenitude (hi : ◇ (Peano σ)) (hn : ¬ PredOp σ) :
    ¬ P.Plenitude ((σ → Prop) → Prop) ((σ → Prop) → Prop) :=
  fun hp => hn (plenitude_supplies_predecessor hp hi)

end Classicism.Research.MaxPredecessorGraph
