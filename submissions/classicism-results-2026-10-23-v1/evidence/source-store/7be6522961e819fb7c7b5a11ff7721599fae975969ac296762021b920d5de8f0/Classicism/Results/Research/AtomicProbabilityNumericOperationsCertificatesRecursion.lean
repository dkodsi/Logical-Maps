import Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificatesInduction

/-! Serial certificate checkpoint for the existing NumericOperations theorems.
The original facade retains the public import path and principal axiom reports. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Recursion: begin classicism_derive: plus_zero_right"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_zero_right

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Recursion: begin classicism_derive: plus_suc_right"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_suc_right

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Recursion: begin classicism_derive: times_zero_right"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_zero_right

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Recursion: complete"
  out.flush : IO Unit)
