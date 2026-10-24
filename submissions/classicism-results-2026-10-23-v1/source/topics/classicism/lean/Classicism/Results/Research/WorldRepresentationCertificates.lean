import Classicism.Results.Research.WorldRepresentation
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! The schema theorem requests a genuine tuple derivation. Missing `.listRule`
is deliberately a check failure. This source is not itself a successful run. -/
#classicism_audit Classicism.Results.Research.WorldRepresentation
#classicism_types_audit Classicism.Results.Research.WorldRepresentation
#classicism_schema Classicism.Research.WorldRepresentation.Representation
#classicism_certify Classicism.Research.WorldRepresentation.necessary_plenitude_representation
#check Classicism.Research.WorldRepresentation.necessary_plenitude_representation.rule
#check Classicism.Research.WorldRepresentation.necessary_plenitude_representation.listRule
#print axioms Classicism.Research.WorldRepresentation.necessary_plenitude_representation.listRule
