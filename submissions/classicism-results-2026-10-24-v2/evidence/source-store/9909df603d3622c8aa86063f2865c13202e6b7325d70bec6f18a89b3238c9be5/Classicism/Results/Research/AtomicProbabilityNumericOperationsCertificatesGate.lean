import Classicism.Results.Research.AtomicProbabilityNumericOperations
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

/-! Serial certificate checkpoint for the existing NumericOperations theorems.
The original facade retains the public import path and principal axiom reports. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Gate: begin classicism_audit: AtomicProbabilityNumericOperations"
  out.flush : IO Unit)

#classicism_audit Classicism.Results.Research.AtomicProbabilityNumericOperations

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Gate: begin classicism_types_audit: AtomicProbabilityNumericOperations"
  out.flush : IO Unit)

#classicism_types_audit Classicism.Results.Research.AtomicProbabilityNumericOperations

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Gate: complete"
  out.flush : IO Unit)
