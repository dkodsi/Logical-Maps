import Classicism.Results.Research.AtomicProbabilityFractionOrder
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

#classicism_audit Classicism.Results.Research.AtomicProbabilityFractionOrder
#classicism_types_audit Classicism.Results.Research.AtomicProbabilityFractionOrder

#classicism_derive Classicism.Research.ProbabilityFractions.qle_refl
  Classicism.Research.ProbabilityFractions.qle_zero
  Classicism.Research.ProbabilityFractions.qle_total
  Classicism.Research.ProbabilityFractions.qle_trans
  Classicism.Research.ProbabilityFractions.qle_antisymm
  Classicism.Research.ProbabilityFractions.qle_add_right
  Classicism.Research.ProbabilityFractions.qle_mul_right
  Classicism.Research.ProbabilityFractions.qlt_mul_right
  Classicism.Research.ProbabilityFractions.qlt_of_le_of_lt
  Classicism.Research.ProbabilityFractions.qtimes_right_comm
  Classicism.Research.ProbabilityFractions.qinverse_antitone
  Classicism.Research.ProbabilityFractions.qinverse_strict_antitone

#print axioms Classicism.Research.ProbabilityFractions.qinverse_strict_antitone.derivable
