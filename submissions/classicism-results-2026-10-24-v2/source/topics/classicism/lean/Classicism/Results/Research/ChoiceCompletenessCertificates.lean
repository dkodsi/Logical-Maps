import Classicism.Results.Research.ChoiceCompleteness
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-!
Research certificates requested for the finitary completeness lemmas. This file
is prepared for the sole compiler owner; its presence is not a successful check.
No map/YAML or generated-statement status is changed.
-/

#classicism_audit Classicism.Results.Research.ChoiceCompleteness
#classicism_types_audit Classicism.Results.Research.ChoiceCompleteness

#classicism_derive Classicism.Research.Choice.evaluation_adjunction
  Classicism.Research.Choice.evaluation_lub
  Classicism.Research.Choice.evaluation_image_lub
  Classicism.Research.Choice.completeness_tt_to_t
  Classicism.Research.Choice.lub_pair_closed
  Classicism.Research.Choice.haec_join_value
  Classicism.Research.Choice.haec_join_closed
  Classicism.Research.Choice.false_disjoint_lub_false
  Classicism.Research.Choice.disjoint_lub_truth
  Classicism.Research.Choice.truth_meet_actuality
  Classicism.Research.Choice.truth_meet_false_eq_bot
  Classicism.Research.Choice.false_part_of_not_actuality

#print axioms Classicism.Research.Choice.false_disjoint_lub_false.derivable
#print axioms Classicism.Research.Choice.completeness_tt_to_t.derivable
