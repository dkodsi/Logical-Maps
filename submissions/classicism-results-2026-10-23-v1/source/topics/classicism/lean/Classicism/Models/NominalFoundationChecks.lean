import Classicism.Models.NominalWorldExamples
import Classicism.Models.NominalStabilizerCriterion
import Classicism.Models.NominalC5
import Classicism.Models.NominalFiniteOrbitStrata

/-!
# Compiler-owner audit targets for the nominal foundation batch

This driver performs no shallow-C translation: these are classical semantic
metatheorems about actual typed syntax. A successful check must show no
sorryAx or new mathematical axioms. This driver has not been run by its author.
The remaining classification obligations are tracked in model-foundations-status.md.
-/

#print axioms Classicism.Meta.Nominal.Hierarchy.denote_supported
#print axioms Classicism.Meta.Nominal.Hierarchy.denote_equivariant
#print axioms Classicism.Meta.Nominal.Hierarchy.denote_subst
#print axioms Classicism.Meta.Nominal.Hierarchy.conv_denote
#print axioms Classicism.Meta.Nominal.Hierarchy.sound
#print axioms Classicism.Meta.Nominal.Hierarchy.C_sound
#print axioms Classicism.Meta.Nominal.Hierarchy.C_consistent
#print axioms Classicism.Meta.Nominal.Hierarchy.C5_quoted
#print axioms Classicism.Meta.Nominal.Hierarchy.intensionalChoice_quoted_iff
#print axioms Classicism.Meta.Nominal.Hierarchy.individuals_boxed_intensionalChoice_quoted
#print axioms Classicism.Meta.Nominal.Hierarchy.trivial_intensionalChoice_quoted
#print axioms Classicism.Meta.Nominal.unique_witness_fixed
#print axioms Classicism.Meta.Nominal.selector_iff_stabilizers
#print axioms Classicism.Meta.Nominal.ic_iff_stabilizers
#print axioms Classicism.Meta.Nominal.orbit_sequence_dedekind
#print axioms Classicism.Meta.Nominal.Hierarchy.orbit_sequence_boxed_dedInfT
#print axioms Classicism.Meta.Nominal.no_dedekind_of_finite_strata
#print axioms Classicism.Meta.Nominal.Examples.tagged_boxed_dedInfT
#print axioms Classicism.Meta.Nominal.Examples.trivial_natural_all_IC
#print axioms Classicism.Meta.Nominal.Examples.countable_atoms_individual_boxed_IC
#print axioms Classicism.Meta.Nominal.finite_proposition_stratum_of_representatives
#print axioms Classicism.Meta.Nominal.Examples.finite_atom_proposition_strata
#print axioms Classicism.Meta.Nominal.Examples.finite_atoms_not_dedInfT
#print axioms Classicism.Meta.Nominal.Examples.finite_atoms_boxed_not_dedInfT
