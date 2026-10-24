import Classicism.Results.Research.ChoiceOrbitAveraging
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Exact requested certificates for the orbit-averaging construction.
No database verification flag is set by this module. -/
#classicism_audit Classicism.Results.Research.ChoiceOrbitAveraging
#classicism_types_audit Classicism.Results.Research.ChoiceOrbitAveraging
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.ChoiceOrbitAveraging

#print axioms Classicism.Research.OrbitAveraging.orbit_step_eq.derivable
#print axioms Classicism.Research.OrbitAveraging.average_step_eq.derivable
#print axioms Classicism.Research.OrbitAveraging.average_eq_of_orbit.derivable
#print axioms Classicism.Research.OrbitAveraging.average_coext_of_fiber.derivable
#print axioms Classicism.Research.OrbitAveraging.averageT_step_eq.derivable
#print axioms Classicism.Research.OrbitAveraging.averageT_eq_of_orbit.derivable
#print axioms Classicism.Research.OrbitAveraging.averageT_coext_of_fiber.derivable
#print axioms Classicism.Research.OrbitAveraging.averageT_coext_of_preserves.derivable
