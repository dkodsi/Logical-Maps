import Classicism.Models.BooleanFiniteChoice

/-! End-to-end audit of the constructed finite-fragment separators.
The principal statements have no model-existence or finite-fragment-gap
premise. A source file is not a certificate: this driver must compile and
its printed axiom dependencies must exclude sorryAx. -/

open Classicism.Meta.ChoiceBoolean

#check ChoiceModel.isModel
#check FiniteChoice.holds_boxed_functionalChoice
#check FiniteChoice.fails_boxed_selector
#check FiniteChoice.finite_boxed_countermodel
#check FiniteChoice.finite_unboxed_countermodel
#check FiniteChoice.boxed_finite_fragment_gap
#check FiniteChoice.unboxed_finite_fragment_gap
#check FiniteChoice.boxed_not_finitely_axiomatizable
#check FiniteChoice.unboxed_not_finitely_axiomatizable
#check FiniteChoice.selector_stage_strict
#check FiniteChoice.adjacent_selector_countermodel

#print axioms ChoiceModel.isModel
#print axioms FiniteChoice.holds_boxed_functionalChoice
#print axioms FiniteChoice.fails_boxed_selector
#print axioms FiniteChoice.finite_boxed_countermodel
#print axioms FiniteChoice.finite_unboxed_countermodel
#print axioms FiniteChoice.boxed_finite_fragment_gap
#print axioms FiniteChoice.unboxed_finite_fragment_gap
#print axioms FiniteChoice.boxed_not_finitely_axiomatizable
#print axioms FiniteChoice.unboxed_not_finitely_axiomatizable
#print axioms FiniteChoice.selector_stage_strict
#print axioms FiniteChoice.adjacent_selector_countermodel
