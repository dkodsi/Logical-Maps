import Classicism.Results.Research.AtomicProbabilityNumericAdditionCertificatesBasic

/-! Independent three-principal audit of the existing Addition Basic checkpoint.
This driver imports accepted certificates and requests Lean's standard axiom
reports. It adds no theorem or mathematical premise. Successful compilation
and three clean reports are required; source preparation is not acceptance. -/

set_option pp.maxSteps 10
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition Basic [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.plus_zero_left.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.plus_zero_left.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition Basic [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.plus_zero_left.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition Basic [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.plus_suc_left.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.plus_suc_left.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition Basic [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.plus_suc_left.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition Basic [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.plus_comm.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.plus_comm.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition Basic [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.plus_comm.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition Basic audit [mono_ms={now}]: all three reports complete; frontend finalization remains"
  out.flush : IO Unit)
