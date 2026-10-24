import Classicism.Results.Research.MaxAtomicityJechShelahCylinders
import Classicism.Results.Research.MaxAtomicitySlalomInvariance
import Classicism.Results.Research.MaxAtomicityRigidTransport

/-!
# The exact algebraic end of the Jech--Shelah rigidity proof

Direct source: Jech--Shelah, Journal of Algebra 182 (1996), pp. 752--754,
with the density argument recast in terms of the explicit Boolean slalom value.

This module isolates two substantive forcing obligations: the branch witness
is not captured under p, and outside p the invariant can be refuted densely.
Given those statements, it proves the invariant is exactly p's Boolean value,
and derives rigidity from the already-proved automorphism invariance. These
obligations remain explicit inputs here. This is not a certificate that the
concrete forcing has already been proved rigid.
Source awaits the designated serial compiler.
-/

namespace Classicism.Meta.Research.MaxAtomicityJechShelahRigidityCriterion

set_option backward.isDefEq.respectTransparency false

open MaxAtomicityRegularCompletion MaxAtomicityJechShelahTrees
open MaxAtomicityJechShelahCylinders MaxAtomicitySlalomInvariance
open MaxAtomicityRigidTransport

noncomputable section

/-- The fixed ground set of indices of a condition's nodes. -/
def nodeIndices (T : Condition) : Set ℕ :=
  {k | ∃ s : List ℕ, s ∈ T.tree ∧ index s = k}

def marker (T : Condition) : B :=
  invariant growthN growthP (nodeIndices T) B

theorem marker_fixed (e : B ≃o B) (T : Condition) : e (marker T) = marker T :=
  automorphism_fixes_invariant e growthN growthP (nodeIndices T)

/-- The two concrete estimates needed from the forcing construction. -/
structure SlalomSeparation : Prop where
  branch : ∀ T : Condition, condition Condition T ≤ marker T
  local_separate : ∀ T Q : Condition, ¬ Q ≤ T →
    ∃ R : Condition, R ≤ Q ∧ condition Condition R ≤ (marker T)ᶜ

/-- The estimates identify the marker, rather than merely finding two
unspecified regions on which it behaves differently. -/
theorem marker_eq_condition (h : SlalomSeparation) (T : Condition) :
    marker T = condition Condition T := by
  apply le_antisymm
  · apply le_of_condition_tests
    intro Q hQ
    apply condition_mono
    classical
    by_contra hnot
    obtain ⟨R, hRQ, hR⟩ := h.local_separate T Q hnot
    apply condition_ne_bot R
    apply le_bot_iff.mp
    calc
      condition Condition R ≤ marker T ⊓ (marker T)ᶜ :=
        le_inf ((condition_mono hRQ).trans hQ) hR
      _ = ⊥ := inf_compl_eq_bot
  · exact h.branch T

theorem automorphism_fixes_conditions (h : SlalomSeparation) (e : B ≃o B)
    (T : Condition) : e (condition Condition T) = condition Condition T := by
  rw [← marker_eq_condition h T, marker_fixed]

/-- Density of the actual forcing propagates fixedness from conditions to
every element of the complete Boolean algebra. -/
theorem rigid_of_slalomSeparation (h : SlalomSeparation) : Rigid B := by
  intro e
  apply OrderIso.ext
  funext b
  change e b = b
  apply le_antisymm
  · apply le_of_condition_tests
    intro T hT
    have hfix : e.symm (condition Condition T) = condition Condition T := by
      apply e.injective
      rw [e.apply_symm_apply, automorphism_fixes_conditions h e T]
    have h' := e.symm.monotone hT
    simpa only [hfix, e.symm_apply_apply] using h'
  · apply le_of_condition_tests
    intro T hT
    have h' := e.monotone hT
    simpa only [automorphism_fixes_conditions h e T] using h'

end

end Classicism.Meta.Research.MaxAtomicityJechShelahRigidityCriterion

#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahRigidityCriterion.marker_fixed
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahRigidityCriterion.marker_eq_condition
#print axioms Classicism.Meta.Research.MaxAtomicityJechShelahRigidityCriterion.rigid_of_slalomSeparation
