import Classicism.Results.Research.AnalyticPossibleCertificates

-- Translate only dependencies actually used by these theorems, rather than
-- rebuilding the unrelated database-wide certificate collection.
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4

#classicism_audit Classicism.Results.Research.AnalyticRigidification
#classicism_types_audit Classicism.Results.Research.AnalyticRigidification
#classicism_derive
  Classicism.Research.Analytic.rigidify_possible

#print axioms Classicism.Research.Analytic.complete_nonempty_necessary.derivable
#print axioms Classicism.Research.Analytic.least_inductive_necessary.derivable
#print axioms Classicism.Research.Analytic.real_necessary.derivable
#print axioms Classicism.Research.Analytic.rigidify_possible.derivable
