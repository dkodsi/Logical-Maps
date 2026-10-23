import Classicism.Results.Research.ChoiceCompletenessCertificates
import Classicism.Results.Research.ChoiceTransversalCertificates
import Classicism.Results.Research.ChoiceJoinTruthCertificates
import Classicism.Results.Research.SectionsRetractionsSchemas
import Classicism.Results.Research.SectionsRetractionsBoxedSchemas
import Classicism.Results.Research.SectionsRetractionsPersistenceSchemas
import Classicism.Results.Research.SectionsRetractionsInvolutionsSchemas
import Classicism.Results.Research.SectionsRetractionsIdempotenceSchemas
import Classicism.Results.Research.SectionsRetractionsInvolutivePersistenceSchemas
import Classicism.Results.Research.SectionsRetractionsModalWitnessCertificates
import Classicism.Results.Research.SectionsRetractionsRigidityCertificates

/-!
# Choice and splitting: delivery check

This imports the exact certificate modules and full-schema assemblies together.
Source proof links, checked-source manifests and explicit residual obligations
are in `research/2026-10-22/lean-formalization/sections-retractions-contributions.md`.
Presence of this file is not a successful check and changes no database flags.
-/

#print axioms Classicism.Research.Choice.choice_completeness_actuality_sharp.derivable
#print axioms Classicism.Research.Choice.choice_completeness_transversal_sharp.derivable
#print axioms Classicism.Research.Choice.local_choice_completeness_transversal.derivable
#print axioms Classicism.Research.Choice.local_choice_countable_ccc_transversal.derivable
#print axioms Classicism.Research.Choice.actuality_iff_join_truth.derivable
#print axioms Classicism.Meta.Research.Splitting.functional_choice_equivalence
#print axioms Classicism.Meta.Research.Splitting.plenitude_equivalence
#print axioms Classicism.Meta.Research.Splitting.necessary_choice_equivalence
#print axioms Classicism.Meta.Research.Splitting.necessary_plenitude_equivalence
#print axioms Classicism.Meta.Research.Splitting.persistence_surjectivity_equivalence
#print axioms Classicism.Meta.Research.Splitting.strong_sections_equivalence
#print axioms Classicism.Meta.Research.Splitting.pairing_representation_equivalence
#print axioms Classicism.Meta.Research.Splitting.idempotence_persistence_equivalence
#print axioms Classicism.Meta.Research.Splitting.involutivity_persistence_equivalence
#print axioms Classicism.Research.Splitting.necessary_injection_splitting.listRule
#print axioms Classicism.Research.Splitting.c5_strong_retractions.listRule
#print axioms Classicism.Research.Splitting.necessary_unique_witness_iff_extensionality.derivable
#print axioms Classicism.Research.Splitting.nd_rigid_sections.listRule
#print axioms Classicism.Research.Splitting.rigid_point_sections_iff_nd.derivable
