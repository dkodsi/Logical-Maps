import Classicism.Results.Research.AtomicProbabilityNumericEquationsFromBasis

/-! Serial certificate checkpoint for the existing NumericOperations theorems.
The original facade retains the public import path and principal axiom reports. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Equations: begin classicism_derive: plus_eq"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_eq

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Equations: begin classicism_derive: times_eq"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_eq

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Equations: complete"
  out.flush : IO Unit)
