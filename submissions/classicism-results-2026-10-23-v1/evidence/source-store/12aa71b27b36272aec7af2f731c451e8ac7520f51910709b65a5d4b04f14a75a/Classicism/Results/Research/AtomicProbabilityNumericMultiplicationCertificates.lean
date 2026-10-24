import Classicism.Results.Research.AtomicProbabilityNumericMultiplication
import Classicism.Results.Research.AtomicProbabilityNumericAdditionCertificates
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: imports complete"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin gate audit"
  out.flush : IO Unit)

#classicism_audit Classicism.Results.Research.AtomicProbabilityNumericMultiplication

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: gate audit returned"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin type-system audit"
  out.flush : IO Unit)

#classicism_types_audit Classicism.Results.Research.AtomicProbabilityNumericMultiplication

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: type-system audit returned"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_zero_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_zero_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_zero_left"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_suc_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_suc_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_suc_left"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_comm"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_comm

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_comm"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_add"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_add

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_add"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.add_times"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.add_times

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.add_times"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_assoc"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_assoc

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_assoc"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.one_numbers"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.one_numbers

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.one_numbers"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.one_ne_zero"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.one_ne_zero

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.one_ne_zero"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_one_right"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_one_right

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_one_right"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_one_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_one_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_one_left"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_eq_zero"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_eq_zero

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_eq_zero"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_ne_zero"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_ne_zero

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_ne_zero"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_cancel_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_cancel_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_cancel_left"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.times_cancel_right"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.times_cancel_right

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.times_cancel_right"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.times_cancel_left.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.times_cancel_left.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.times_cancel_left.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.times_cancel_right.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.times_cancel_right.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.times_cancel_right.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericMultiplication [mono_ms={now}]: all commands complete; frontend finalization remains"
  out.flush : IO Unit)
