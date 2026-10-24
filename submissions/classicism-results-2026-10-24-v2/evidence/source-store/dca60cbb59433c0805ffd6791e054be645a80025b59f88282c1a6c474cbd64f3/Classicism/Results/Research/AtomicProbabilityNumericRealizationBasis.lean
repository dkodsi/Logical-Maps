import Classicism.Results.Research.AtomicProbabilityNumericCertificateSupport

/-!
# Shared realization basis

The existing equation proofs are direct instances of `realize_selected`, using
`domain_supported` for the common property field
(`AtomicProbabilityNumericOperations.lean:37-46`). This checkpoint exports those
unchanged generic translations and their axiom summaries before numerical
specialization. No new mathematical lemma is introduced.

Prepared diagnostic/certificate source, not accepted until the ordinary serial
check exits successfully and its current-source artifact and axiom reports pass.
-/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: Shared realization basis: imports complete"
  out.flush : IO Unit)

#probability_derive_silent Classicism.Research.ActualityCore.realize_selected
  Classicism.Research.ActualityCore.domain_supported

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: begin axiom report Classicism.Research.ActualityCore.realize_selected.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ActualityCore.realize_selected.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: axiom report returned Classicism.Research.ActualityCore.realize_selected.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: begin axiom report Classicism.Research.ActualityCore.domain_supported.derivable"
  out.flush : IO Unit)

#print axioms Classicism.Research.ActualityCore.domain_supported.derivable

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: axiom report returned Classicism.Research.ActualityCore.domain_supported.derivable"
  out.flush : IO Unit)

#eval (do
  let now ← IO.monoMsNow
  let out ← IO.getStderr
  out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}]: Shared realization basis: commands complete; frontend finalization remains"
  out.flush : IO Unit)
