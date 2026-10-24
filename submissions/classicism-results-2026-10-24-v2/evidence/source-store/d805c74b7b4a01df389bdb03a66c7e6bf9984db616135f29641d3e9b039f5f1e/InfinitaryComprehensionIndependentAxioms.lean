import Classicism.Results.Research.InfinitaryComprehensionFiniteBridge
import Classicism.Results.Research.InfinitaryComprehensionNominalStrictness
import Classicism.Results.Research.InfinitaryComprehensionStrictnessModel

/-! Independent principal audit within the infinitary development.
The finite embedding and two strictness constructions are imported without
requiring the unfinished representation bridge. This audit adds no theorem,
model, premise or derivation. Check all printed axiom reports against the
companion checklist; successful imports alone do not certify absence of sorryAx. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Infinitary independent audit: begin 26 reports"
  out.flush : IO Unit)

#print axioms Classicism.Research.InfinitaryComprehension.FiniteBridge.embed_rename
#print axioms Classicism.Research.InfinitaryComprehension.FiniteBridge.embed_subst
#print axioms Classicism.Research.InfinitaryComprehension.FiniteBridge.embed_inst
#print axioms Classicism.Research.InfinitaryComprehension.FiniteBridge.eval_embed
#print axioms Classicism.Research.InfinitaryComprehension.FiniteBridge.finite_comprehension
#print axioms Classicism.Research.InfinitaryComprehension.FiniteBridge.sequent_at_iff
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.assignment_supported
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.bounded_comprehension
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.colour_not_supported
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.colour_comprehension_false
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.fixed_bound_strictness
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.comprehension_of_occurrence_bound
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.finite_occurrence_comprehension
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.finite_branching_comprehension
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.RegularBound.occurrence_fixed_bound_strictness
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.Expansion.model
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.Expansion.faithful
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.Expansion.relation_atomicity
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.Expansion.profile_atomic
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.Expansion.c_theorem_holds
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.Expansion.not_comp
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.reduct_certificate
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.exists_strictness_certificate
#print axioms Classicism.Research.InfinitaryComprehension.Strictness.exists_atomic_modal_collapse_not_comp
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.eval_parameter_congr
#print axioms Classicism.Research.InfinitaryComprehension.Nominal.Hierarchy.comprehension_of_supported_evaluation

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Infinitary independent audit: 26 reports complete"
  out.flush : IO Unit)
