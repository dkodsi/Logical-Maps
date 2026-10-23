import Classicism.Results.Research.CanonicalEvaluator
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

#classicism_audit Classicism.Results.Research.CanonicalEvaluator
#classicism_types_audit Classicism.Results.Research.CanonicalEvaluator
#classicism_derive Classicism.Research.actualEvaluator_kernel_possible
  Classicism.Research.worldEvaluator_actual
  Classicism.Research.canonicalEvaluator_actual
  Classicism.Research.canonicalEvaluator_unique
  Classicism.Research.canonicalEvaluator_idempotent
  Classicism.Research.worldEvaluator_all
  Classicism.Research.canonicalEvaluator_all
  Classicism.Research.worldEvaluator_exists
  Classicism.Research.canonicalEvaluator_exists
#print axioms Classicism.Research.canonicalEvaluator_all.derivable
#print axioms Classicism.Research.canonicalEvaluator_exists.derivable
