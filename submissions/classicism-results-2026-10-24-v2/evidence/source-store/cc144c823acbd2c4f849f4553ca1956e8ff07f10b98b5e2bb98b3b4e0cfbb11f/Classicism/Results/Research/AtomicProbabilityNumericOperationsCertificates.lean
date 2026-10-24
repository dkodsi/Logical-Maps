import Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificatesTimesSuccessor

/-! Public facade for the original twelve NumericOperations certificates.
The import chain preserves their exact derivation order and splits compilation
into serial checkpoints; theorem statements and derivations are unchanged. -/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations: all twelve derivations imported; begin principal axiom reports"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.times_zero_right.derivable
#print axioms Classicism.Research.ProbabilityNumericOperations.times_suc_right.derivable

#eval (do
  let out ← IO.getStderr
  out.putStrLn "Probability NumericOperations: complete"
  out.flush : IO Unit)
