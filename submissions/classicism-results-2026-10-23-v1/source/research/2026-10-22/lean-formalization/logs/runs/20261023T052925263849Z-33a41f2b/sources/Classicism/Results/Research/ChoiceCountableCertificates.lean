import Classicism.Results.Research.ChoiceChainsCertificates
import Classicism.Results.Research.ChoiceCountable
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Requested gate/type and object-language C certificates for CBC + CCC. -/
#classicism_audit Classicism.Results.Research.ChoiceBoolean
  Classicism.Results.Research.ChoiceCountable
#classicism_types_audit Classicism.Results.Research.ChoiceBoolean
  Classicism.Results.Research.ChoiceCountable
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.ChoiceBoolean
  Classicism.Results.Research.ChoiceCountable
#print axioms Classicism.Research.Choice.choice_countable_ccc_completeness.derivable
