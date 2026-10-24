import Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificatesNumbers

/-! Serial certificate checkpoint for the existing NumericOperations theorems.
The original facade retains the public import path and principal axiom reports. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Induction: begin classicism_derive: number_induction"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.number_induction

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Induction: begin classicism_derive: number_cases"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.number_cases

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Induction: complete"
  out.flush : IO Unit)
