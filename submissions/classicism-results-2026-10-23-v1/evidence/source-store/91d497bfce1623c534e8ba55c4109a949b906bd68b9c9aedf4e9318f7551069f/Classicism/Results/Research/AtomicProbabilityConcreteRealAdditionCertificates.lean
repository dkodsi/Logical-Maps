import Classicism.Results.Research.AtomicProbabilityConcreteRealAddition
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: imports complete"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin gate audit"
  out.flush : IO Unit)

#classicism_audit Classicism.Results.Research.AtomicProbabilityConcreteRealAddition

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: gate audit returned"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin type-system audit"
  out.flush : IO Unit)

#classicism_types_audit Classicism.Results.Research.AtomicProbabilityConcreteRealAddition

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: type-system audit returned"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_below"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_below

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_below"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_supported"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_supported

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_supported"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.member_below_nonmember"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.member_below_nonmember

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.member_below_nonmember"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_in_field"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_in_field

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_in_field"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_comm"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_comm

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_comm"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_assoc"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_assoc

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_assoc"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_mono"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_mono

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_mono"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_zero_right"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_zero_right

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_zero_right"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_zero_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_zero_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_zero_left"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin derive Classicism.Research.ProbabilityConcreteReals.realAdd_sup_left"
  out.flush : IO Unit)

#classicism_derive Classicism.Research.ProbabilityConcreteReals.realAdd_sup_left

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: derive returned Classicism.Research.ProbabilityConcreteReals.realAdd_sup_left"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityConcreteReals.realAdd_sup_left.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityConcreteReals.realAdd_sup_left.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityConcreteReals.realAdd_sup_left.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability ConcreteRealAddition [mono_ms={now}]: all commands complete; frontend finalization remains"
  out.flush : IO Unit)
