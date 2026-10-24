import Classicism.Results.Research.AtomicProbabilityNumericAdditionCertificatesAssociativity

set_option pp.maxSteps 10
set_option stderrAsMessages false
set_option Elab.async false

/-! Serial checkpoint for the existing NumericAddition certificates: LeftCancellation.
Public derivation names and shallow proof statements are unchanged.
A stage marker alone is not acceptance; require successful module completion. -/

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.plus_cancel_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_cancel_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.plus_cancel_left"
  out.flush : IO Unit)

