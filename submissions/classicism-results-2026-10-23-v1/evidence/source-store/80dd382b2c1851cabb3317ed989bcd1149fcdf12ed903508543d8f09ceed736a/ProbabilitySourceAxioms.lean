import Classicism.Results.Research.AtomicProbabilityCutCrossing
import Classicism.Results.Research.AtomicProbabilityRationalNegation
import Classicism.Results.Research.AtomicProbabilityConcreteRealInverse

/-!
# Axiom audit of the 23 accepted probability source declarations

This imports the three existing source targets accepted in run
20261024T034221831704Z-b1f369ae and prints every theorem declared in those
files: 8 cut-crossing lemmas, 4 rational-negation lemmas, and 11 concrete-real
inverse lemmas. All names are explicit; no proof or theorem is introduced here.

These are source-layer declarations, not their object-C translations.
The existing source-only receipt remains historical; this driver is not itself
accepted until its current-source compilation and 23 axiom reports are audited.
-/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability source axioms [mono_ms={now}]: begin Classicism.Results.Research.AtomicProbabilityCutCrossing"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityCutCrossing.represented_adjacent_exit
#print axioms Classicism.Research.ProbabilityCutCrossing.natural_multiple_exceeds_fraction
#print axioms Classicism.Research.ProbabilityCutCrossing.stepTerm_in_field
#print axioms Classicism.Research.ProbabilityCutCrossing.stepTerm_zero
#print axioms Classicism.Research.ProbabilityCutCrossing.stepTerm_suc
#print axioms Classicism.Research.ProbabilityCutCrossing.cut_step_eventually_outside
#print axioms Classicism.Research.ProbabilityCutCrossing.cut_has_adjacent_step
#print axioms Classicism.Research.ProbabilityCutCrossing.cut_has_small_gap

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability source axioms [mono_ms={now}]: begin Classicism.Results.Research.AtomicProbabilityRationalNegation"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityRationals.rneg_zero
#print axioms Classicism.Research.ProbabilityRationals.rneg_reverses
#print axioms Classicism.Research.ProbabilityRationals.rneg_sub
#print axioms Classicism.Research.ProbabilityRationals.rsub_sub_self

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability source axioms [mono_ms={now}]: begin Classicism.Results.Research.AtomicProbabilityConcreteRealInverse"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityConcreteReals.realNeg_below
#print axioms Classicism.Research.ProbabilityConcreteReals.realNeg_supported
#print axioms Classicism.Research.ProbabilityConcreteReals.negative_member_not_neg
#print axioms Classicism.Research.ProbabilityConcreteReals.realNeg_in_field
#print axioms Classicism.Research.ProbabilityConcreteReals.realNeg_antitone
#print axioms Classicism.Research.ProbabilityConcreteReals.realNeg_involution
#print axioms Classicism.Research.ProbabilityConcreteReals.realAdd_neg
#print axioms Classicism.Research.ProbabilityConcreteReals.realSub_in_field
#print axioms Classicism.Research.ProbabilityConcreteReals.realSub_self
#print axioms Classicism.Research.ProbabilityConcreteReals.realAdd_cancel_right
#print axioms Classicism.Research.ProbabilityConcreteReals.realAdd_le_iff_le_sub

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability source axioms [mono_ms={now}]: all 23 print commands complete"
  out.flush : IO Unit)
