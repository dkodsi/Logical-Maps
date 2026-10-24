import Classicism.Models.BooleanChoiceCutoff
import Classicism.Models.BooleanSupportedSelection
import Classicism.Models.BooleanSelectorObstruction
import Classicism.Models.BooleanRecoveredModel

/-! Audit of the actual Boolean construction and countable model extraction.
The final finite-Choice theorem has a separate driver. This file has no
model-existence, comprehension or Choice-verdict assumption. -/

open Classicism.Meta.ChoiceBoolean

#check ColumnConditions.small_chain_lower_bound
#check ColumnDistributivity.binary_distributivity
#check TypedHierarchy.app_eqv
#check TypedTermSemantics.term_comprehension
#check SmallFormulaSemantics.small_comprehension
#check GroundChecks.check_eqv
#check ProtectedCoverage.ground_coverage
#check ChoiceCutoff.exists_regular_cutoff
#check SupportedSelection.row_equation
#check IndexedProfiles.columns_eqv_zero
#check SelectorObstruction.selector_existence_value_zero
#check TaggedFirstOrder.sentence_value
#check ModelExtraction.realize_iff_secured
#check BooleanAxiomTheory.axioms_value_one
#check RecoveredModel.isModel
#check RecoveredModel.small_transfer_one
#check RecoveredModel.small_failure_zero

#print axioms ColumnConditions.small_chain_lower_bound
#print axioms ColumnDistributivity.binary_distributivity
#print axioms TypedTermSemantics.term_comprehension
#print axioms SmallFormulaSemantics.small_comprehension
#print axioms ProtectedCoverage.ground_coverage
#print axioms ChoiceCutoff.exists_regular_cutoff
#print axioms SupportedSelection.row_equation
#print axioms IndexedProfiles.columns_eqv_zero
#print axioms SelectorObstruction.selector_existence_value_zero
#print axioms TaggedFirstOrder.sentence_value
#print axioms ModelExtraction.realize_iff_secured
#print axioms BooleanAxiomTheory.axioms_value_one
#print axioms RecoveredModel.isModel
#print axioms RecoveredModel.small_transfer_one
#print axioms RecoveredModel.small_failure_zero
