import Classicism.Results.Research.FiniteProfiles
import Classicism.Principles.Base

/-!
# The unrestricted relational-input boundary for raw world representation

Direct source: research/2026-10-22/notes/world-cardinality-ucp-20261022.md §12,
unpaginated original research, misc. The unary proof has an explicit argument
witness. The companion schema assembly supplies all tuple witnesses from C's
actual Existence theorem and vectorizes this proof over every finite argument
list, including the empty list. No Ty marker is treated as inhabitation.
-/
namespace Classicism.Research.RawWorldRepresentationBoundary
open Classicism.Research.FiniteProfiles

def NoRawWRRelational (τ : Type) [Rel τ] : Prop :=
  ∀ V : τ → Prop, ¬ RawWR V

theorem existence_implies_no_raw_wr_unary {σ : Type} [Ty σ] :
    Classicism.P.Existence σ → NoRawWRRelational (σ → Prop) := by
  intro he V
  obtain ⟨a, _⟩ := he
  exact no_raw_wr_unary a V

end Classicism.Research.RawWorldRepresentationBoundary
