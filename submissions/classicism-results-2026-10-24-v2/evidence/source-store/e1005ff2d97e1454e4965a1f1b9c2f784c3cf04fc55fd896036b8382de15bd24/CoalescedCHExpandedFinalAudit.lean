import ClassicismZFC
import Classicism.Results.Research.CoalescedCHFirstOrder

/-!
# Expanded CH: final endpoint and semantic-bridge axiom audit

This file only imports existing sources and prints dependencies. It proves no
new theorem. The ambient construction and the conditional first-order transfer
are distinct. No finitistic Con(ZFC) reduction is claimed. The inconsistency
endpoints concern Maximalism plus CH noncontingency, never Maximalism alone.
-/

-- ambient component endpoints.
#print axioms ClassicismZFC.OppositeCHComponents.positive_component
#print axioms ClassicismZFC.OppositeCHComponents.negative_component
#print axioms ClassicismZFC.OppositeCHComponents.opposite_components
#print axioms ClassicismZFC.OppositeCHComponents.coalesced_countermodel
#print axioms ClassicismZFC.OppositeCHComponents.consistent_opposite_witnesses
#print axioms ClassicismZFC.OppositeCHComponents.maximalism_with_CH_noncontingency_inconsistent
#print axioms ClassicismZFC.OppositeCHComponents.maximalism_with_CH_noncontingency_schema_inconsistent

-- conditional first order endpoints.
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.component_of_model
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.component_of_satisfiable
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.consistent_of_model
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.consistent_of_satisfiable
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.countermodel_of_models
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.countermodel_of_satisfiable
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_inconsistent_of_models
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_inconsistent_of_satisfiable
#print axioms Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer.maximalism_schema_inconsistent_of_satisfiable

-- semantic bridge checkpoints.
#print axioms ClassicismZFC.SelectedFieldForcing.positive_real_witnesses
#print axioms ClassicismZFC.CodedFieldForcing.negative_cardinal_witnesses
#print axioms ClassicismZFC.InternalHierarchy.component_isModel
#print axioms ClassicismZFC.TypedReal.component_hasReal
#print axioms ClassicismZFC.TypedCHTransport.naturalCode_eq
#print axioms ClassicismZFC.TypedCHTransport.structuralCH_iff
#print axioms ClassicismZFC.TypedCHTransport.component_hasRealCH
#print axioms ClassicismZFC.TypedCHTransport.component_hasRealNotCH
