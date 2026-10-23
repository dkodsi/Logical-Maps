import Classicism.Results.Research.AtomicProbabilityNaturalOrder
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

#classicism_audit Classicism.Results.Research.AtomicProbabilityNaturalOrder
#classicism_types_audit Classicism.Results.Research.AtomicProbabilityNaturalOrder

#classicism_derive Classicism.Research.ProbabilityNaturalOrder.add_zero_left
  Classicism.Research.ProbabilityNaturalOrder.add_suc_left
  Classicism.Research.ProbabilityNaturalOrder.add_comm
  Classicism.Research.ProbabilityNaturalOrder.add_assoc_forward
  Classicism.Research.ProbabilityNaturalOrder.add_assoc_reverse
  Classicism.Research.ProbabilityNaturalOrder.add_cancel_right
  Classicism.Research.ProbabilityNaturalOrder.add_cancel_left
  Classicism.Research.ProbabilityNaturalOrder.add_eq_zero
  Classicism.Research.ProbabilityNaturalOrder.number_cases
  Classicism.Research.ProbabilityNaturalOrder.le_refl
  Classicism.Research.ProbabilityNaturalOrder.zero_le
  Classicism.Research.ProbabilityNaturalOrder.le_fields
  Classicism.Research.ProbabilityNaturalOrder.le_zero
  Classicism.Research.ProbabilityNaturalOrder.le_suc
  Classicism.Research.ProbabilityNaturalOrder.le_of_suc_le
  Classicism.Research.ProbabilityNaturalOrder.le_trans
  Classicism.Research.ProbabilityNaturalOrder.le_total
  Classicism.Research.ProbabilityNaturalOrder.le_antisymm
  Classicism.Research.ProbabilityNaturalOrder.not_suc_le_self

#print axioms Classicism.Research.ProbabilityNaturalOrder.add_comm.derivable
#print axioms Classicism.Research.ProbabilityNaturalOrder.le_total.derivable
#print axioms Classicism.Research.ProbabilityNaturalOrder.le_antisymm.derivable
