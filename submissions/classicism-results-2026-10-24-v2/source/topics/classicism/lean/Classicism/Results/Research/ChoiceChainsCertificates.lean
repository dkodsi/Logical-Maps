import Classicism.Results.Research.ChoiceFixedPointCertificates
import Classicism.Results.Research.ChoiceChains
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Requested object-language C checks for the canonical-chain foundation. -/
#classicism_audit Classicism.Results.Research.ChoiceChains
#classicism_types_audit Classicism.Results.Research.ChoiceChains
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.ChoiceChains
#print axioms Classicism.Research.Choice.canonical_fixedpoint_of_supremum.derivable
