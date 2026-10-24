import Classicism.Results.Research.ActualityCoreGraphs
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Separate serial checking is required. Tuple rules must really be present. -/
#classicism_audit Classicism.Results.Research.ActualityCoreGraphs
#classicism_types_audit Classicism.Results.Research.ActualityCoreGraphs
#classicism_schema Classicism.Research.ActualityCore.GraphNormalization
  Classicism.Research.ActualityCore.GraphRealization
  Classicism.Research.ActualityCore.PredicateTransfer
#classicism_certify Classicism.Research.ActualityCore.graph_normalization_law
  Classicism.Research.ActualityCore.graph_realization_law
  Classicism.Research.ActualityCore.predicate_transfer_law
#check Classicism.Research.ActualityCore.graph_normalization_law.listRule
#check Classicism.Research.ActualityCore.graph_realization_law.listRule
#check Classicism.Research.ActualityCore.predicate_transfer_law.listRule
#print axioms Classicism.Research.ActualityCore.graph_normalization_law.listRule
#print axioms Classicism.Research.ActualityCore.graph_realization_law.listRule
#print axioms Classicism.Research.ActualityCore.predicate_transfer_law.listRule
