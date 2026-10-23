# Universal core and disjunction verification

Ownership accepted by OpenAI Codex task `/root/sp_semantic_audit`, 23 October 2026.

Only `StrongPossibilityConsequencesUniversalCore.lean`, `StrongPossibilityConsequencesDisjunction.lean`, and this isolated verification directory are writable by this lane. The exact mathematical statements and assumptions are retained. The compiler cache is `/tmp/classicism-sp-universal-cache`, seeded by copying the existing certificate cache with symlinks preserved. The shared check helper is imported with its output directory overridden; it is not edited.

Current status: **Both UniversalCore and Disjunction passed** the shared locked runner. The final 69-module dependency snapshot matches the current sources. There is no remaining assigned compiler target, and both accepted source files are frozen.

UniversalCore source SHA-256: `b986bf950f38d0b359c22c9cde1b0ab02dbb6b8b8f8db79ac41996671a566288`. Dependency fingerprint: `5899be473914d817c9abe704c42e978307e4bf979fb3c81c165610cc6a0ecd25`. Finalized manifest: [20261023T043010003441Z-33fa960f.json](checks/20261023T043010003441Z-33fa960f.json). All seven public axiom reports exclude `sorryAx`; their only metatheoretic axioms are `propext` and `Quot.sound`, with `fixedCore_closed` using only `propext`. These are actual C derivation and schema-entailment results. Exact theorem statements and assumptions were preserved.

Machine-readable sublane update: [status.json](status.json). The parent owns the shared `verification-updates/strong_possibility.json` aggregation.

Disjunction source SHA-256: `df4c167dd99accceb555f9a8aaa89d0a8b5e9beac6d86c1cdc8c4fbf20fa566e`. Dependency fingerprint: `938ab76bb19794e13ba94aa7f7c448dbe13430e2843141dfe82acace3007b23e`. Finalized manifest: [20261023T044336274999Z-6b5c1cb4.json](checks/20261023T044336274999Z-6b5c1cb4.json). This run reused the accepted UniversalCore result and freshly checked Reflection and Disjunction.

Disjunction's five public axiom reports all exclude `sorryAx`. `consistent_add_iff_not_neg` and `core_consistent_of_restricted_disjunction` use only `propext` and `Quot.sound`. The other three results additionally use `Classical.choice` in ordinary metalogical reasoning. These are proofs about the actual `Derivable` relation; no new axiom was added to C. The exact printed declarations and axiom lists are saved in [status.json](status.json) and the [accepted Disjunction log](logs/runs/20261023T044336274999Z-6b5c1cb4/StrongPossibilityConsequencesDisjunction.log).

## Contribution and scope

The accepted UniversalCore proof constructs C reflection by induction on an explicit finite universal/Boolean-identity grammar, then proves both schema entailments and the exact consistency equivalence with SP. Disjunction proves the finite-proof-support characterization in both directions. Its equivalence with SP consistency retains the explicit original-Max consistency hypothesis. Neither the global restricted disjunction property nor SP consistency is proved.

The repairs were syntactic and elaborational: explicit substitution identity and conversion through lifted-renaming composition, an explicit metalogical contradiction term, and an explicitly typed conjunction axiom witness. No theorem statement, signature scope, closed-type restriction, or consistency premise was changed.

Full ordinary arguments: [universal core note](../../notes/reflection-universal-core-20261022.md), [disjunction note, section 17](../../notes/sp-failed-disjunction-20261022.md#17-exact-normalization-to-a-strong-modal-disjunction-property), and the parent's [proof summary](../sp-verification/proof-summary.md). Overall remaining research obligations are retained in [sp-family-status.md](../sp-family-status.md).

## Reproduction

From the bundle root, use the existing toolchain and global locked helper through the no-copy wrapper:

```sh
python3 research/2026-10-22/lean-formalization/sp-universal-verification/check_isolated.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesUniversalCore.lean --timeout 180 --lock-wait 300
python3 research/2026-10-22/lean-formalization/sp-universal-verification/check_isolated.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesDisjunction.lean --timeout 180 --lock-wait 300
```

The existing isolated cache is `/tmp/classicism-sp-universal-cache`; the wrapper deliberately does not create or seed caches. Compiler busy exit 75 is scheduling, not failure of a proof. Parent reproduction details: [reproduction.md](../sp-verification/reproduction.md).

## Repair history

Initial isolated checks reduced the UniversalCore failure to the explicit syntactic equality between two equivalent compositions of lifted variable shifts in the universal-prefix step. The repair using `Ren.lift_comp` passed the subsequent complete check. Earlier failed-run logs are retained as history and are superseded by the accepted manifests linked above.

Disjunction's unavailable `by_contra` tactic was replaced with `Classical.byContradiction`; its conjunction witness received an explicit theorem type. Its mathematical statement is unchanged. Public axiom reports were added in both owned modules.

The coordinator's shared-runner lock pause ended before the successful check above. The isolated wrapper no longer seeds or copies caches before invoking the runner. All source/report edit batches have passed `pmap.py validate` (132 principles, 447 results, 162 models).
