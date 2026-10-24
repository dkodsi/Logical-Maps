import Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificatesRecursion

/-! Serial certificate checkpoint for the existing NumericOperations theorems.
The original facade retains the public import path and principal axiom reports. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations TimesSuccessor: begin classicism_derive: times_suc_right"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_suc_right

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations TimesSuccessor: complete"
  out.flush : IO Unit)
