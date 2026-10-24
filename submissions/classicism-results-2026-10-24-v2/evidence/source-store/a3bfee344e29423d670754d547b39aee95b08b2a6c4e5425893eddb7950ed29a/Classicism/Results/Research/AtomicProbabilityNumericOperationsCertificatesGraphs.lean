import Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificatesEquations

/-! Serial certificate checkpoint for the existing NumericOperations theorems.
The original facade retains the public import path and principal axiom reports. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Graphs: begin classicism_derive: plus_graph"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_graph

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Graphs: begin classicism_derive: times_graph"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_graph

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations Graphs: complete"
  out.flush : IO Unit)
