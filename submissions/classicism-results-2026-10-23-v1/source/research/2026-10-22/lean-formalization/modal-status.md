# Modal propagation formalization handoff

**READY FOR INTEGRATION.** Both source modules and the fourteen certificate
drivers are frozen. Ownership passes to the sole compiler task
`01a1664d-7c13-7701-b52c-2070ee16eb06`, which may repair them directly. This
author has executed no Lean, Lake, installation, or dependency download.

These are **uncompiled drafts**: gate, type, translation and schema certification
are all pending. The repository validator passed with 132 principles, 447
results and 162 models. That validator does not check Lean proofs.

## Sources and fingerprints

| Module under `topics/classicism/lean/Classicism/Results/Research/` | Theorem declarations | Source SHA-256 |
| --- | ---: | --- |
| `SealedWorldCover.lean` | 32 | `e51c691a52cd1d6e5b3df8c7c95dd5d895ca7a39565a40b8ebb9cf6c5c110901` |
| `ModalPropagation.lean` | 31 | `cf77a123eb9e5e99c074043b77d122a10fad8487c690441a417756cdfb59ff8e` |

`modal-manifest.json` records every source and driver fingerprint, target and
check status. Declaration counts include helpers and are not counts of
independent results or completed certificates.

Direct mathematical sources are `research/2026-10-22/strong-leibniz-rigid-bottom-cut.md`,
§§1–6, and `research/2026-10-22/followup/modal-propagation.md`, §§1–6. The new
proofs are not attributed to a published source. Existing research notes,
human/source proofs, YAML flags and generated `Statements.lean` are unchanged.

## Exact intended results

All formulas use the original finitary C. Here `RC` means Rigid Comprehension,
`RP` means Rigid Power, and juxtaposition with `t` means a predicate type.

- Uniform relational cut lemma: if `A` is rigid, `□A⊥`, and
  `□∀W(AW → ∀Y(W≤Y ∨ W≤¬Y))`, then `λW(AW ∧ W≤Y)` is rigid.
  It uses no future comprehension, ND, Tame Rigidity, or BF.
- At `ρ=t` and separately `ρ=σt`, local `SL_ρ + RC_(ρt)` yields `□SL_ρ`.
- At the same types, local `SL_ρ + RC_(ρt) + RP_(ρt)` yields `□BF_ρ`.
  The power predicate and the representation are sealed before using a future
  universally quantified predicate. No root universal premise is silently
  transported into a box.
- `WeaklyRigid(λx.⊤) ↔ BF_σ` and `Rigid(λx.⊤) ↔ □BF_σ`.
  Local `RC_(σt) + BF_σ` therefore yields `□BF_σ`.
- A rigid property of haecceity codes whose image is necessarily coded pulls
  back to a rigid property. Current codedness is sufficient because weak
  inextensibility seals it. Consequently `RC_((σt)t) → RC_(σt)` without BF,
  including `σ=e`. The empty tuple has a separate singleton-code proof
  `RC_tt → RC_t`; it does not introduce a unit type into C.
- `SL_t + RC_tt + RC_((σt)t) + BF_(σt) + BF_((σt)t)` yields both
  `□RC_(σt)` and `□BC_(σt)`. Both BF instances are relational, even for `σ=e`.
- The explicit empty-tuple consequences use
  `SL_t + RC_tt + BF_t + BF_tt` to obtain `□RC_t` and `□BC_t`.

These are finite typed implication statements, not a quantifier over all
types. The generic cut proof has `Rel`, `Order`, and `Pointwise` parameters.
The main join and propagation proofs are unary plus separately proved
propositional cases. A polyadic claim still requires the generated list rule
and the corresponding schema composition; no tuple certificate is presumed.

## Remaining composition for the full all-schema conclusion

The drafts retain an explicit local RP instance in the boxed-BF theorem so
that the shallow source imports only the existing record layer. The recorded
eliminator already exists as `Classicism.atom_rc_rigid_power` in
`Classicism/Results/Arity.lean`:

```
Atomicity_(ρtt) + RC_(ρt) + RC_(ρtt) → RP_(ρt).
```

Combine it with `Proofs.strong_leibniz_r_implies_atomicity_r` at `ρtt`.
Thus the exact four-instance antecedent for boxed BF is
`SL_ρ + SL_(ρtt) + RC_(ρt) + RC_(ρtt)`.
For the propagation theorem at `σt`, use this once at `ρ=σt` and once at
`ρ=(σt)t`, then apply T to the boxed BF conclusions. Add the displayed
`SL_t` and `RC_tt` instances. This supplies the mathematical all-schema
`SL + RC → □RC + □BC` route without BF_e.

The final `Entails` composition and list-rule assembly are **not yet supplied**
by this handoff. They must cite actual translated certificates after these
new proofs pass; an imported shallow proof alone is insufficient. The Arity
module's existing certification infrastructure is intentionally not imported
into both low-dependency drafts merely to assemble these final implications.

## Serial checks for the integration owner

First compile the source modules, which contain both audit directives:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.SealedWorldCover --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ModalPropagation --timeout 180
```

Then run each path in `modal-manifest.json`'s `certificate_drivers` separately:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/modal-checks/ModalCutRigidity.lean --timeout 180
```

Use the same command with each subsequent driver path. There is one target
per process to bound translation memory. The drivers import `Tools.Schema`
and `Certified.Schemas`; the latter avoids rebuilding the shallow mirror
in each translator process. The current checking script rejects unresolved
external dependencies, so the core owner's dependency-aware certification
runtime must be ready before these drivers can run. No worker should fetch
or build a second dependency tree. Preserve per-check logs and fingerprints.

For `#classicism_certify` targets, verify the produced `.rule` and, where
applicable, `.listRule`, not just a successful ordinary compilation. The
two object-parameter helper targets use `#classicism_derive` explicitly.
After any repairs, run:

```sh
/tmp/classicism-followup-venv/bin/python3 scripts/pmap.py validate
```

## Model coverage and actual blockers

No conditional model existence assumption has been added as a Lean axiom.
The following remain research-model obligations, not certified separators:

- `central-map.md` and `central-map-complete-gluing.md`: the support-restricted
  Henkin domains, their lambda/quantifier closure, the central-map action,
  and the actual local/boxed satisfaction calculations must be constructed.
- `choice-support-obstruction.md`: formalize stabilizer-to-pinned-support,
  the `P(K × Eq(N))` fixed-support algebra, its actual atom, and the unique
  witness contradiction. These require concrete symmetry/support semantics;
  a theorem assuming the fixed-point lemma would not certify the separator.
- `propagation-without-barcan-countermodel.md`: formalize the forcing-name
  quotient and equality decisions, invariant-name closure, full future
  quantifier domains, all coalesced transition maps, and the new-subset
  failure of future RC/BC. The finite-terminal and group-loop variants have
  different BF/BC profiles and must not share unverified verdicts.

The source notes still determine each proposal's audit status. This handoff
does not upgrade any model, resolve Strong Possibility consistency, or claim
the finitary/infinitary distinction has disappeared.

## Communication update

At the user's direct request, the permission to extend the language with
natural resources such as infinitary conjunction, and to save useful files,
was delivered successfully to all eleven other Classicism project chats.
The notice included low RAM use, compact file output, preservation of the
single compiler owner, and explicit labeling of any language extension.
This permission does not change the finitary scope of the present drafts.
