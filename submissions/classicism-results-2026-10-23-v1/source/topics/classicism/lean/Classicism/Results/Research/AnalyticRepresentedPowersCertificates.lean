import Classicism.Results.Research.AnalyticRepresentedPowers
import Classicism.Results.Research.AnalyticRigidificationCertificates

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

#classicism_audit Classicism.Results.Research.AnalyticRepresentedPowers
#classicism_types_audit Classicism.Results.Research.AnalyticRepresentedPowers
#classicism_derive
  Classicism.Research.Analytic.agree_on_one_iff
  Classicism.Research.Analytic.agree_on_two_iff
  Classicism.Research.Analytic.agree_on_three_iff
  Classicism.Research.Analytic.represented_power
  Classicism.Research.Analytic.domain2_persistent
  Classicism.Research.Analytic.domain3_persistent
  Classicism.Research.Analytic.analytic_necessitism_three

#print axioms Classicism.Research.Analytic.represented_power.derivable
#print axioms Classicism.Research.Analytic.domain2_persistent.derivable
#print axioms Classicism.Research.Analytic.domain3_persistent.derivable
#print axioms Classicism.Research.Analytic.analytic_necessitism_three.derivable
