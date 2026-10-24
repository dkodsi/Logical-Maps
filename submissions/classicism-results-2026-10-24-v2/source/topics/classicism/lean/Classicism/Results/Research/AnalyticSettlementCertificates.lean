import Classicism.Results.Research.AnalyticRigidification
import Classicism.Results.Research.AnalyticStructuresCertificates

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

#classicism_derive
  Classicism.Research.Analytic.settled_of_box_persistence
  Classicism.Research.Analytic.settled_not
  Classicism.Research.Analytic.settled_and
  Classicism.Research.Analytic.settled_imp
  Classicism.Research.Analytic.settled_or
  Classicism.Research.Analytic.settled_all
  Classicism.Research.Analytic.settled_exists
  Classicism.Research.Analytic.settled_eq
  Classicism.Research.Analytic.rigid_settled
  Classicism.Research.Analytic.membership_settled
  Classicism.Research.Analytic.membership2_settled
  Classicism.Research.Analytic.membership3_settled

#print axioms Classicism.Research.Analytic.settled_all.derivable
#print axioms Classicism.Research.Analytic.settled_eq.derivable
#print axioms Classicism.Research.Analytic.membership3_settled.derivable
