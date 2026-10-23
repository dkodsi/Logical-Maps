import Classicism.Results.Research.SectionsRetractionsCertificates
import Classicism.Results.Research.SectionsRetractionsStrong

/-! Full source audit, per-map equations, and the tuple rule for every relational output. -/
#classicism_audit Classicism.Results.Research.SectionsRetractionsStrong
#classicism_types_audit Classicism.Results.Research.SectionsRetractionsStrong
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Research.SectionsRetractionsStrong

#classicism_certify Classicism.Research.Splitting.necessary_injection_splitting
  Classicism.Research.Splitting.c5_injectivity_persists
  Classicism.Research.Splitting.persistent_injections_strong_retractions
  Classicism.Research.Splitting.c5_strong_retractions
  Classicism.Research.Splitting.c5_strong_retractions_t
  Classicism.Research.Splitting.truth_retractions_modal_b
  Classicism.Research.Splitting.truth_retractions_nd

#check Classicism.Research.Splitting.necessary_injection_splitting.listRule
#check Classicism.Research.Splitting.c5_strong_retractions.listRule
#print axioms Classicism.Research.Splitting.necessary_injection_splitting.listRule
#print axioms Classicism.Research.Splitting.necessary_injection_iff_retraction.derivable
#print axioms Classicism.Research.Splitting.necessary_injection_iff_retraction_t.derivable
#print axioms Classicism.Research.Splitting.truth_retractions_modal_b.rule
