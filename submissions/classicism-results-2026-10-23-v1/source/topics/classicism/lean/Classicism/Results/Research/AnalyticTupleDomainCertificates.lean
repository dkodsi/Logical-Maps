import Classicism.Results.Research.AnalyticTupleDomains
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

#classicism_audit Classicism.Results.Research.AnalyticTupleDomains
#classicism_types_audit Classicism.Results.Research.AnalyticTupleDomains
#classicism_derive
  Classicism.Research.Analytic.empty_domain_persistent
  Classicism.Research.Analytic.append_coordinate_persistent

#print axioms Classicism.Research.Analytic.empty_domain_persistent.derivable
#print axioms Classicism.Research.Analytic.append_coordinate_persistent.derivable
