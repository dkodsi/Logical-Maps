import Classicism.Results.Research.QuantifierObservers
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Gate, relational-type and object-derivation checks for the quantifier-observer
characterization. Direct source: operator-separation-new-results.txt, section 2,
Theorem 2 (misc, unpaginated). A source file alone is not a successful certificate. -/

#classicism_audit Classicism.Results.Research.QuantifierObservers
#classicism_types_audit Classicism.Results.Research.QuantifierObservers
#classicism_derive Classicism.Research.QuantifierObservers.separation_iff_barcan
  Classicism.Research.QuantifierObservers.weak_separation_iff_barcan
  Classicism.Research.QuantifierObservers.literal_separation_barcan
  Classicism.Research.QuantifierObservers.boxed_barcan_literal_separation

#print axioms Classicism.Research.QuantifierObservers.separation_iff_barcan.derivable
#print axioms Classicism.Research.QuantifierObservers.weak_separation_iff_barcan.derivable
#print axioms Classicism.Research.QuantifierObservers.literal_separation_barcan.derivable
#print axioms Classicism.Research.QuantifierObservers.boxed_barcan_literal_separation.derivable
