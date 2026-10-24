import Classicism.Results.Research.AtomicProbabilityNumericAdditionCertificatesRightCancellationAndZero

set_option pp.maxSteps 10
set_option stderrAsMessages false
set_option Elab.async false

/-! Stable public facade for the four serial NumericAddition certificate checkpoints.
The Basic checkpoint retains the source gate and relational-type audits.
The complete eight-principal audit remains in AtomicProbabilityRemainingFullAxioms. -/

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.plus_cancel_right.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.plus_cancel_right.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.plus_cancel_right.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.plus_eq_zero.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.plus_eq_zero.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.plus_eq_zero.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: all commands complete; frontend finalization remains"
  out.flush : IO Unit)
