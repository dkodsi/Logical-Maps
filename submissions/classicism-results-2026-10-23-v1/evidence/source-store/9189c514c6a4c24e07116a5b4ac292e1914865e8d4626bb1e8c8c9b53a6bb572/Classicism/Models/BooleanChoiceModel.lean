import Classicism.Models.BooleanChoiceFamily
import Classicism.Models.BooleanRecoveredModel

/-!
# The concrete ordinary model at each finite Choice cutoff

Original formalization (misc), 23 October 2026, of
`research/2026-10-23/boolean-valued-finite-choice.md` sections 7--8
(unpaginated). Each natural number specifies the actual regular cardinal,
partial-column Boolean algebra, supported hierarchy over Nat, and countable
witness-chain quotient. The displayed first-order axiom theory proves
modelhood. The same model receives every value-one/zero small sentence.

The specific Choice and selector values are supplied by their separate
translation modules. This construction takes no model-existence or
finite-fragment-gap hypothesis.
-/

noncomputable section

namespace Classicism.Meta.ChoiceBoolean.ChoiceModel

open ChoiceFirstOrder ColumnAlgebra ChoiceCutoff
open SmallFormulaSemantics

theorem top_nonzero (m : Nat) : (⊤ : Values (cutoff m)) ≠ ⊥ := by
  letI := ColumnAlgebra.nontrivial (cutoff_regular m).aleph0_le
  exact top_ne_bot

def typedStructure (m : Nat) : ChoiceFirstOrder.Structure :=
  RecoveredModel.typedStructure (action (cutoff m)) Nat ⟨0⟩ ⊤ (top_nonzero m)

def model (m : Nat) : Intensional.Premodel Signature.pure ChoiceFirstOrder.World :=
  (typedStructure m).model

theorem isModel (m : Nat) : (model m).IsModel :=
  RecoveredModel.isModel (action (cutoff m)) Nat ⟨0⟩ ⊤ (top_nonzero m)

theorem small_comprehension (m : Nat) : SmallComprehension (typedStructure m) :=
  RecoveredModel.small_comprehension (action (cutoff m)) Nat ⟨0⟩ ⊤ (top_nonzero m)

theorem small_transfer_one (m : Nat) (φ : SmallFormula [])
    (hφ : smallValue (action (cutoff m)) Nat φ .nil = ⊤) :
    φ.Realize (typedStructure m) .nil :=
  RecoveredModel.small_transfer_one (action (cutoff m)) Nat ⟨0⟩
    ⊤ (top_nonzero m) φ hφ

theorem small_failure_zero (m : Nat) (φ : SmallFormula [])
    (hφ : smallValue (action (cutoff m)) Nat φ .nil = ⊥) :
    ¬ φ.Realize (typedStructure m) .nil :=
  RecoveredModel.small_failure_zero (action (cutoff m)) Nat ⟨0⟩
    ⊤ (top_nonzero m) φ hφ

end Classicism.Meta.ChoiceBoolean.ChoiceModel
