import Classicism.Results.Research.AnalyticRealCertificates

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

#classicism_derive
  Classicism.Research.Analytic.rigidify_exists
  Classicism.Research.Analytic.rigid_real_of_possible

#print axioms Classicism.Research.Analytic.rigidify_exists.derivable
#print axioms Classicism.Research.Analytic.rigid_real_of_possible.derivable
