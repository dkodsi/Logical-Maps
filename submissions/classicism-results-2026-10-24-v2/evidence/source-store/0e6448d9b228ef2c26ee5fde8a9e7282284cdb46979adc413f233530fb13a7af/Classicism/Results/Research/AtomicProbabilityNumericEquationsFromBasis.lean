import Classicism.Results.Research.AtomicProbabilityNumericArithmeticBasis

/-!
# Numerical equations from imported basis

These are the original `plus_eq` and `times_eq` theorem names, with their original
statements, premises, and translations. The only proof-organization difference
is that their four direct generic theorem dependencies are imported from the
two preceding certificate checkpoints. No operation is replaced or postulated.

This is a source-backed response to run 20261024T041357823183Z-612ad618:
both checked-kernel theorem barriers completed by 94.24 seconds, but the first
axiom-report phase did not return before the 180-second timeout. Lean computes
local axiom summaries again at module export, including when there is no
explicit `#print axioms` command; imported summaries avoid crossing the module
boundary. The proposed reduction remains unverified until the coordinator runs
it, and is not claimed to eliminate traversal of the equations' own bodies.

Prepared diagnostic/certificate source, not accepted until the ordinary serial
check exits successfully and its current-source artifact and axiom reports pass.
-/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: Numerical equations from imported basis: imports complete"
  out.flush : IO Unit)

#probability_derive_silent Classicism.Research.ProbabilityNumericOperations.plus_eq
  Classicism.Research.ProbabilityNumericOperations.times_eq

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.plus_eq.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.plus_eq.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.plus_eq.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: begin axiom report Classicism.Research.ProbabilityNumericOperations.times_eq.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ProbabilityNumericOperations.times_eq.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: axiom report returned Classicism.Research.ProbabilityNumericOperations.times_eq.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: Numerical equations from imported basis: commands complete; frontend finalization remains"
  out.flush : IO Unit)
