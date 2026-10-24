import Classicism.Results.Research.FullLogicalObserversAtomic
import Classicism.Results.Research.FullLogicalObserversAtomicConverse

/-!
# The exact atomicity characterization over C5 and Actuality

Direct source: `research/2026-10-23/operator-characterizations/positive-operator-representation.txt`,
section 3, display (B) (misc, original research, 23 October 2026, unpaginated).

The type-t qualification uses full identities of the Boolean and universal and
existential composite operations. Current Actuality suffices. The necessary
separation implication uses the proved stability theorem; it does not box an
optional premise. This file joins the two independently constructed directions.
-/

namespace Classicism.Research.FullLogicalObservers
open Classicism.P Classicism.Paper

theorem c5_actuality_atomicity_iff_full_separation
    (c5 : NecNecessityOfDistinctness Prop) (act : Actuality) :
    Atomicity Prop ↔ SeparationFull Prop :=
  ⟨fun hat => c5_atomicity_full_separation hat c5,
    c5_actuality_full_separation_atomicity c5 act⟩

theorem c5_actuality_atomicity_iff_necessary_full_separation
    (c5 : NecNecessityOfDistinctness Prop) (act : Actuality) :
    Atomicity Prop ↔ □ (SeparationFull Prop) :=
  ⟨fun hat => c5_atomicity_necessary_full_separation hat c5,
    fun hs => c5_actuality_full_separation_atomicity c5 act (box_elim hs)⟩

theorem c5_actuality_full_separation_iff_necessary
    (c5 : NecNecessityOfDistinctness Prop) (act : Actuality) :
    SeparationFull Prop ↔ □ (SeparationFull Prop) :=
  ⟨fun hs => c5_atomicity_necessary_full_separation
      (c5_actuality_full_separation_atomicity c5 act hs) c5,
    box_elim⟩

/-- Once the type-t test class separates, every fixed admitted type separates. -/
theorem c5_actuality_full_separation_at {σ : Type} [Ty σ]
    (c5 : NecNecessityOfDistinctness Prop) (act : Actuality)
    (hs : SeparationFull Prop) : SeparationFull σ :=
  c5_atomicity_full_separation (c5_actuality_full_separation_atomicity c5 act hs) c5

theorem c5_actuality_necessary_full_separation_at {σ : Type} [Ty σ]
    (c5 : NecNecessityOfDistinctness Prop) (act : Actuality)
    (hs : SeparationFull Prop) : □ (SeparationFull σ) :=
  c5_atomicity_necessary_full_separation
    (c5_actuality_full_separation_atomicity c5 act hs) c5

end Classicism.Research.FullLogicalObservers
