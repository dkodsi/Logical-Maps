import Classicism.Models.NominalOrbitClassification
import Classicism.Models.NominalAtomChoice

/-!
# Audit targets for the focused nominal-classification extension

Classical semantic metatheorems. The arbitrary-atom orbit equivalence and
all-type atom-world IC use no extra object-language axioms. This driver must
compile and report exactly these targets without sorryAx before certification.
-/

#print axioms Classicism.Meta.Nominal.finite_orbit_representatives
#print axioms Classicism.Meta.Nominal.infinite_orbit_quotient_dedekind
#print axioms Classicism.Meta.Nominal.FiniteSupportOrbits.extend_finite_pattern
#print axioms Classicism.Meta.Nominal.FiniteSupportOrbits.finite_representatives_in_orbit
#print axioms Classicism.Meta.Nominal.finite_stabilizer_orbits_of_global_representatives
#print axioms Classicism.Meta.Nominal.finite_proposition_strata_of_finite_orbit_quotient
#print axioms Classicism.Meta.Nominal.dedekind_iff_infinite_orbit_quotient
#print axioms Classicism.Meta.Nominal.Hierarchy.dedInfT_iff_infinite_orbit_quotient
#print axioms Classicism.Meta.Nominal.Hierarchy.not_dedInfT_iff_finite_orbit_quotient
#print axioms Classicism.Meta.Nominal.Hierarchy.boxed_dedInfT_iff_infinite_orbit_quotient
#print axioms Classicism.Meta.Nominal.Hierarchy.boxed_not_dedInfT_iff_finite_orbit_quotient
#print axioms Classicism.Meta.Nominal.Examples.finite_atoms_ic
#print axioms Classicism.Meta.Nominal.Examples.finite_atoms_intensionalChoice_quoted
#print axioms Classicism.Meta.Nominal.Examples.finite_atoms_boxed_intensionalChoice_quoted
#print axioms Classicism.Meta.Nominal.Examples.finite_atoms_boxed_ic_and_not_dedInfT
