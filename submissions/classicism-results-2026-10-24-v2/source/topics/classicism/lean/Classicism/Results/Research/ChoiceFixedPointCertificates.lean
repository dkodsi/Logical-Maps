import Classicism.Results.Research.ChoiceFixedPoint
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Requested finitary C certificates; pending sole-owner compilation. -/

#classicism_audit Classicism.Results.Research.ChoiceFixedPoint
#classicism_types_audit Classicism.Results.Research.ChoiceFixedPoint

#classicism_derive Classicism.Research.Choice.supStep_coext
  Classicism.Research.Choice.domain_graph_fixedpoint
  Classicism.Research.Choice.domain_operation_fixedpoint

#print axioms Classicism.Research.Choice.domain_graph_fixedpoint.derivable
#print axioms Classicism.Research.Choice.domain_operation_fixedpoint.derivable
