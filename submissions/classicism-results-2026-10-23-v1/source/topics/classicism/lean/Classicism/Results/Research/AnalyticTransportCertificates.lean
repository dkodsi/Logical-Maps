import Classicism.Results.Research.AnalyticSettlementCertificates

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

#classicism_derive
  Classicism.Research.Analytic.all_necessary_of_rigid_instances
  Classicism.Research.Analytic.complete_nonempty_necessary
  Classicism.Research.Analytic.least_inductive_necessary

#print axioms Classicism.Research.Analytic.all_necessary_of_rigid_instances.derivable
#print axioms Classicism.Research.Analytic.complete_nonempty_necessary.derivable
#print axioms Classicism.Research.Analytic.least_inductive_necessary.derivable
