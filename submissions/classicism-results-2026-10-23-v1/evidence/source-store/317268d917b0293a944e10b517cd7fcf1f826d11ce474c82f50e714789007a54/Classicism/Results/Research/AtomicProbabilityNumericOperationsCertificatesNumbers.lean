import Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificatesGraphs

/-! Serial certificate checkpoint for the existing NumericOperations theorems.
The original facade retains the public import path and principal axiom reports. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Numbers: begin classicism_derive: plus_numbers"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_numbers

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Numbers: begin classicism_derive: times_numbers"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_numbers

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Numbers: complete"
  out.flush : IO Unit)
