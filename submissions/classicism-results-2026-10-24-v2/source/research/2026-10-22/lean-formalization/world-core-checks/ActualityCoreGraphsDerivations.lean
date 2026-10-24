import Classicism.Results.Research.ActualityCoreGraphs
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

#classicism_audit Classicism.Results.Research.ActualityCoreGraphs
#classicism_types_audit Classicism.Results.Research.ActualityCoreGraphs
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.ActualityCoreGraphs
#print axioms Classicism.Research.ActualityCore.compose_assoc.derivable
#print axioms Classicism.Research.ActualityCore.realize_selected.derivable
#print axioms Classicism.Research.ActualityCore.represented_wellFounded_transfer.derivable
