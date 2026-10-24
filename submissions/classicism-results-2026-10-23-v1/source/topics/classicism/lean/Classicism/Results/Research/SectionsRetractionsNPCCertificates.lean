import Classicism.Results.Research.SectionsRetractionsBoxedCertificates
import Classicism.Results.Research.SectionsRetractionsMasksCertificates
import Classicism.Results.Research.SectionsRetractionsNPC

/-! Exact C gate, type, translated derivation, and schema certificates for
the strong-section consumer. Mathematical source: functional-choice-by-sections,
section 4 (research/2026-10-22/notes; misc, unpaginated). -/

#classicism_audit Classicism.Results.Research.SectionsRetractionsNPC
#classicism_types_audit Classicism.Results.Research.SectionsRetractionsNPC
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.SectionsRetractionsNPC
#classicism_certify Classicism.Research.Splitting.npc_necessary_actuality_actuality
  Classicism.Research.Splitting.npc_strong_sections_sections
  Classicism.Research.Splitting.npc_choice_strong_sections_c5
  Classicism.Research.Splitting.npc_c5_necessary_actuality_atomicity
  Classicism.Research.Splitting.npc_c5_necessary_retractions
#classicism_entails Classicism.Research.Splitting.npc_necessary_actuality_actuality
  Classicism.Research.Splitting.npc_strong_sections_sections
  Classicism.Research.Splitting.npc_choice_strong_sections_c5
  Classicism.Research.Splitting.npc_c5_necessary_actuality_atomicity
  Classicism.Research.Splitting.npc_c5_necessary_retractions

#print axioms Classicism.Research.Splitting.npc_choice_strong_sections_c5.derivable
#print axioms Classicism.Research.Splitting.npc_c5_necessary_actuality_atomicity.derivable
#print axioms Classicism.Research.Splitting.npc_c5_necessary_retractions.listEntails
