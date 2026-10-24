import Classicism.Results.Research.AnalyticTransportCertificates
import Classicism.Results.Research.AnalyticFieldCertificates

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

#classicism_derive
  Classicism.Research.Analytic.real_necessary
  Classicism.Research.Analytic.rigidify_actual

#print axioms Classicism.Research.Analytic.real_necessary.derivable
#print axioms Classicism.Research.Analytic.rigidify_actual.derivable
