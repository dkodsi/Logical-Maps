import Classicism.Results.Research.FullLogicalObserversAtomic
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Gate/type audits and object-language derivations. A source file alone
is not a successful certificate. Direct source: positive-operator-representation.txt
sections 2--3 (misc, 23 October 2026, unpaginated). -/

#classicism_audit Classicism.Results.Research.FullLogicalObservers
#classicism_types_audit Classicism.Results.Research.FullLogicalObservers
#classicism_audit Classicism.Results.Research.FullLogicalObserversAtomic
#classicism_types_audit Classicism.Results.Research.FullLogicalObserversAtomic

#classicism_derive Classicism.Research.FullLogicalObservers.patched_principal_imp
  Classicism.Research.FullLogicalObservers.patched_boolFull
  Classicism.Research.FullLogicalObservers.patched_forall_full
  Classicism.Research.FullLogicalObservers.patched_quantifierFull
  Classicism.Research.FullLogicalObservers.atomicity_separation_by
  Classicism.Research.FullLogicalObservers.atomicity_full_separation
  Classicism.Research.FullLogicalObservers.c5_atomicity_full_separation
  Classicism.Research.FullLogicalObservers.c5_atomicity_necessary_full_separation

#print axioms Classicism.Research.FullLogicalObservers.patched_principal_imp.derivable
#print axioms Classicism.Research.FullLogicalObservers.patched_boolFull.derivable
#print axioms Classicism.Research.FullLogicalObservers.patched_forall_full.derivable
#print axioms Classicism.Research.FullLogicalObservers.patched_quantifierFull.derivable
#print axioms Classicism.Research.FullLogicalObservers.atomicity_separation_by.derivable
#print axioms Classicism.Research.FullLogicalObservers.atomicity_full_separation.derivable
#print axioms Classicism.Research.FullLogicalObservers.c5_atomicity_full_separation.derivable
#print axioms Classicism.Research.FullLogicalObservers.c5_atomicity_necessary_full_separation.derivable
