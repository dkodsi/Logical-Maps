import Classicism.Results.Research.ChoiceCountableCertificates
import Classicism.Results.Research.ChoiceTransversal
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Requested exact type-local C certificates; no Actuality dependency. -/
#classicism_audit Classicism.Results.Research.ChoiceTransversal
#classicism_types_audit Classicism.Results.Research.ChoiceTransversal
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.ChoiceTransversal
#print axioms Classicism.Research.Choice.local_choice_completeness_transversal.derivable
#print axioms Classicism.Research.Choice.local_choice_countable_ccc_transversal.derivable
