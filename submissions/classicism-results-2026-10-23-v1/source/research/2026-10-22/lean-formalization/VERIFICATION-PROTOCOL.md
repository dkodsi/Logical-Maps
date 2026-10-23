# Lean verification ownership and queue

## Hard stop — 23 October 2026

The user explicitly requires all work to stop by **01:57 a.m. America/New_York (05:57 UTC), 23 October 2026**, with no further token use unless the human resumes the work. Begin final checkpoint/handoff by 01:40 and end all author and child-agent turns by 01:55 for a safety margin. Completed owners remain stopped. Do not schedule post-deadline runs, poll, retry or resume automatically. This instruction overrides previous continuation and exploratory directions. Preserve incomplete status honestly; do not mark an unmet goal complete. Any active autonomous goal must be paused under the user's stop instruction. Do not start a check whose lock wait and bounded runtime can extend past shutdown; stop only your own unfinished processes safely.

## Current delivery scope — 23 October 2026

The user's latest direction is to prepare the existing research for delivery. Do not initiate or continue exploratory attempts to settle open conjectures, including Strong Possibility consistency. This narrows earlier instructions to discover new results or pursue every open mathematical gap.

New Lean formalizations remain authorized and important. Continue implementing existing natural-language arguments, proving supporting lemmas needed for those formalizations, repairing proofs, constructing the exact model certificates promised by existing arguments, and running the required audits. Do not restrict work to sources that already exist or to compilation alone.

When an existing argument exposes a genuinely unresolved mathematical step, preserve and explain the gap, qualify the claim appropriately, and move to another established result. Do not conceal a gap in an added hypothesis or turn it into an open-ended search for a new headline theorem. Retain incomplete and conditional work in the collection with its exact status.

Each owner should finish a coherent delivery handoff: exact statements and scope, full prose-proof links, principal Lean declarations, matching check and axiom evidence, reproduction instructions, corrections, and a concise account of the contribution. The priority is the existing main results and their complete evidence, followed by consolidation. Historical next-action text below is subordinate to this scope. The shared global compiler lock and current edit ownership remain in force.

Each proof family has an author who also owns its diagnostics, repairs and verification loop. The [current queue](verification-queue.json) identifies the exact source scope, next target, evidence and unresolved mathematics. The core integrator owns shared infrastructure, dependency maintenance and final cross-family audits. A completed source submission is no longer a reason for its author to wait indefinitely.

## One compiler slot

All checks use `check_module.py`, `check_with_mathlib.py`, or the existing SP wrappers that invoke the same runner. The process-global lock is independent of log directories and caches. Separate output directories do not authorize simultaneous Lean processes. Never bypass a busy lock with raw Lean, Lake, another script or another cache.

Use one substantive target or a small dependency-ordered batch per invocation. On a busy response, leave the lock in place, prepare independent source work and retry after the active job finishes. Do not run rapid retry loops. Core alone manages the pinned toolchain and precompiled libraries; dependency maintenance must hold the same lock and must not modify a library while it is being checked.

During rollout, existing invocations finish before new checks are activated. The coordinator sends the ready message after the runner safeguards have been tested and the old unprotected processes have ended.

## Repair ownership

The queue distinguishes author, current repair owner and verification state. A file has one repair owner. Authors receiving files back must read the current filesystem and latest diagnostics: the integrator may have fixed their earlier drafts. Successful source files remain stable unless a specific correction is needed.

Each owner follows this loop:

1. Identify the next actual theorem or model certificate and its first failing dependency.
2. Run the locked checker and inspect the saved diagnostics.
3. Repair files within the assigned scope. Request a handoff for a shared dependency owned elsewhere.
4. Repeat the relevant check until it passes or exposes a genuine mathematical gap.
5. Save the principal declarations, exact premises and type/signature scope, source hashes, manifest and remaining obligations. Continue to the next assigned result.

Do not stop merely because the first compilation failed or because an old handoff said to await integration. A missing mathematical bridge must remain explicit; it must not become a new hypothesis disguised as completion. Authors with such a blocker can continue another independent assigned result.

## Evidence

The checker compiles captured source bytes, records provenance and publishes cache outputs only after successful checks. Cache reuse requires matching input fingerprints and output integrity metadata. Legacy cache stamps alone do not satisfy this rule; some local modules will need a one-time recheck. The pinned precompiled Mathlib library is not rebuilt by this transition.

Ordinary Lean compilation, Classicism gate/type audits, translated object-language derivations, and complete countermodel certificates are different milestones. Preserve the distinction in every report. In particular, a helper theorem or conditional reduction does not verify the principal claim. Keep the applicable no-hole/axiom audit and exact statement coverage with the certificate.

The historical submission notes remain intact. Current manifests and source/dependency matches control verification; the queue controls ownership and next action. Neither the queue nor this protocol changes database `lean` flags or mathematical verdicts.

After a substantive check, each owner writes its own `status_update_path` from the queue. Record `lane`, `updated_at_utc`, `state`, `checked_target`, `manifest`, `principal_declarations`, `source_hashes`, `next_target` and `mathematical_gaps`. Use explicit states such as `repairing`, `ready_to_check`, `waiting_for_compiler`, `checked_main_target` or `mathematical_gap`. Link existing full proof and handoff notes rather than copying them. Root owns the shared queue structure; separate update files avoid concurrent overwrites and feed the final collection.

## Resource limits

Keep logs on disk and responses compact. No previews, large rendered artifacts or broad Mathlib rebuilds are needed. A single compiler slot limits build memory while authors work on independent repairs. The coordinator reviews stalled jobs and ownership conflicts rather than becoming the sole person who can fix every proof.
