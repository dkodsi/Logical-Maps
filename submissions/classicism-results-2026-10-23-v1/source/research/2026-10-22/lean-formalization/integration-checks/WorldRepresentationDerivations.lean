import Classicism.Results.Research.WorldRepresentation
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

#classicism_audit Classicism.Results.Research.WorldRepresentation
#classicism_types_audit Classicism.Results.Research.WorldRepresentation
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.WorldRepresentation

#print axioms Classicism.Research.WorldRepresentation.encode_decode.derivable
#print axioms Classicism.Research.WorldRepresentation.decode_encode.derivable
