import Classicism.Results.Research.AtomicProbabilityNumericAddition
import Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificates
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

set_option pp.maxSteps 10
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: imports complete"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: begin gate audit"
  out.flush : IO Unit)

#classicism_audit Classicism.Results.Research.AtomicProbabilityNumericAddition

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: gate audit returned"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: begin type-system audit"
  out.flush : IO Unit)

#classicism_types_audit Classicism.Results.Research.AtomicProbabilityNumericAddition

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: type-system audit returned"
  out.flush : IO Unit)

/-! Serial checkpoint for the existing NumericAddition certificates: Basic.
Public derivation names and shallow proof statements are unchanged.
A stage marker alone is not acceptance; require successful module completion. -/

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.plus_zero_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_zero_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.plus_zero_left"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.plus_suc_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_suc_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.plus_suc_left"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityNumericOperations.plus_comm"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityNumericOperations.plus_comm

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityNumericOperations.plus_comm"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability NumericAddition Basic [mono_ms={now}]: all commands complete; frontend finalization remains"
  out.flush : IO Unit)

