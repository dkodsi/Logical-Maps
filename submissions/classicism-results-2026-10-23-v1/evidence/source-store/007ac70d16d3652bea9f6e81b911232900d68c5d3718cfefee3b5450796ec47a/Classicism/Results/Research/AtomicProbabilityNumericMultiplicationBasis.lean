import Classicism.Results.Research.AtomicProbabilityNumericAdditionBasis

/-!
# Multiplicative uniqueness checkpoint

The original numerical uniqueness theorem is translated without changing its
statement, proof, premises, or generated declaration name. This checkpoint
separates already measured translation, axiom-report, and export work; it adds
no mathematical result and does not increase any runner resource limit.
The silent command retains the checked-kernel theorem barrier.
-/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: Multiplicative uniqueness checkpoint: imports complete"
  out.flush : IO Unit)

#probability_derive_silent Classicism.Research.ActualityCoreArithmetic.core_mul_functional

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: begin axiom report Classicism.Research.ActualityCoreArithmetic.core_mul_functional.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ActualityCoreArithmetic.core_mul_functional.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: axiom report returned Classicism.Research.ActualityCoreArithmetic.core_mul_functional.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: Multiplicative uniqueness checkpoint: commands complete; frontend finalization remains"
  out.flush : IO Unit)
