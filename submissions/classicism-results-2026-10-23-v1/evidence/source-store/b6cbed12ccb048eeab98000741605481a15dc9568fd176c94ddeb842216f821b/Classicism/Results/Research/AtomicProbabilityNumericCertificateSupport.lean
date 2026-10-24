import Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificatesGate

/-!
# Silent diagnostics around the unchanged derivation command

This command follows `Classicism/Tools/Translate.lean:1798-1810` exactly for
name resolution, the existing-declaration guard, the existing scoped heartbeat
option, `Translate.derive`, generated-name selection, type/theory lookup, and
error reporting. It omits the large-type `logInfo` and adds timed, uncaptured
stderr markers plus an explicit checked-kernel theorem barrier. It changes no
translation rule, theorem statement, premise, or runner resource limit.

`Lean/Environment.lean:648-650` defines `toKernelEnv` as `env.checked.get`.
The exact compiler sources are the installed Lean 4.33.1 sources.
-/

set_option pp.maxSteps 100
set_option stderrAsMessages false
set_option Elab.async false

open Lean Lean.Elab Lean.Elab.Command

syntax (name := probabilityDeriveSilent) "#probability_derive_silent " ident+ : command

@[command_elab probabilityDeriveSilent]
def elabProbabilityDeriveSilent : CommandElab := fun stx => do
  let start ← IO.monoMsNow
  let report (stage : String) : CommandElabM Unit := do
    let now ← IO.monoMsNow
    let out ← IO.getStderr
    out.putStrLn s!"Probability dependency checkpoint [mono_ms={now}; elapsed_ms={now - start}]: {stage}"
    out.flush
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      report s!"begin derive {n}"
      let env ← getEnv
      unless env.contains (n ++ `derivable) || env.contains (n ++ `derivableC) do
        withScope (fun sc => { sc with opts := maxHeartbeats.set sc.opts 0 })
          (liftTermElabM (Classicism.Meta.Translate.derive n))
      let dn := if (← getEnv).contains (n ++ `derivable) then n ++ `derivable else n ++ `derivableC
      let ty := (← getConstInfo dn).type
      let inC := ty.find? (·.isConstOf ``Classicism.Meta.C.axioms) |>.isSome
      report s!"derive returned {dn}; theory={if inC then "C" else "C-minus"}"
      report s!"begin kernel environment barrier {dn}"
      match (← getEnv).toKernelEnv.find? dn with
      | some (.thmInfo _) => report s!"kernel environment theorem present {dn}"
      | some _ => throwError "silent diagnostic: {dn} is not a kernel theorem declaration"
      | none => throwError "silent diagnostic: {dn} is missing from the checked kernel environment"
    catch ex =>
      report s!"derive failed {n}"
      logError m!"{n}: not derived — {ex.toMessageData}"
