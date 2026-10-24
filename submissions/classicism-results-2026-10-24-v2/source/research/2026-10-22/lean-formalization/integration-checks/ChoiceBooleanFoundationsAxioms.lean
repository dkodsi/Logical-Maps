import Classicism.Models.BooleanConditionAutomorphisms
import Classicism.Models.BooleanColumnConditions
import Classicism.Models.BooleanSupportedPredicates
import Classicism.Models.BooleanFirstOrderSemantics

/-! Kernel and axiom audit of concrete Boolean construction components.
This driver does not assert a complete typed countermodel or negative
finite-Choice certificate. -/

open Classicism.Meta.ChoiceBoolean

#check EqualitySpace
#check predicateSpace
#check eval_subst
#check Predicate.forallRight
#check Predicate.existsRight
#check ConditionCompletion.regularCompleteBooleanAlgebra
#check ConditionCompletion.dense_cone
#check ConditionCompletion.cone_compatible_iff
#check ConditionCompletion.map_cone
#check ColumnConditions.Condition
#check ColumnConditions.permutationOrderIso
#check ColumnConditions.fresh_amalgam_avoiding
#check supportedPredicateSpace
#check supportedSectionLeft_congr
#check supportedEvaluation
#check FirstOrderSemantics.value_congr
#check FirstOrderSemantics.exists_positive_witness

#print axioms predicateSpace
#print axioms eval_subst
#print axioms ConditionCompletion.dense_cone
#print axioms ConditionCompletion.cone_compatible_iff
#print axioms ConditionCompletion.map_cone
#print axioms ColumnConditions.permutationOrderIso
#print axioms ColumnConditions.fresh_amalgam_avoiding
#print axioms supportedPredicateSpace
#print axioms supportedSectionLeft_congr
#print axioms supportedEvaluation
#print axioms FirstOrderSemantics.value_congr
#print axioms FirstOrderSemantics.exists_positive_witness
