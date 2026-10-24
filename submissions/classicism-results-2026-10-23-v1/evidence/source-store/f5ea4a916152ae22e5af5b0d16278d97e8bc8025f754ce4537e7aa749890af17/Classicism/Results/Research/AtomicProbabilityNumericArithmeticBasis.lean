import Classicism.Results.Research.AtomicProbabilityNumericMultiplicationBasis

/-!
# Shared numerical uniqueness basis: stable facade

The same `core_add_functional.derivable` and `core_mul_functional.derivable`
declarations are now imported through additive and multiplicative checkpoints.
The latter imports the former, preserving reuse of the additive dependencies.
Original mathematical sources and the translator are unchanged.

The previous combined run completed both checked-kernel barriers and both axiom
report commands, but timed out during frontend finalization. Separate module
boundaries amortize the measured local axiom traversal/export work and supply
imported axiom summaries to the original equation diagnostic.

This facade keeps its original import path. Source preparation does not by
itself confer acceptance; the coordinator must check the new modules and facade.
-/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#print axioms Classicism.Research.ActualityCoreArithmetic.core_add_functional.derivable
#print axioms Classicism.Research.ActualityCoreArithmetic.core_mul_functional.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: Shared numerical uniqueness facade: imported reports complete"
  out.flush : IO Unit)
