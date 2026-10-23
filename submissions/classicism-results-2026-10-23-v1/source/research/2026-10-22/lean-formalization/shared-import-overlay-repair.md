# Shared precompiled-import repair — ready

Verified at 2026-10-23T04:42:53.651587+00:00. No pinned library files were changed or downloaded.

The old runner omitted `.ir.sig` companions when constructing its merged import tree. In pinned Lean 4.33.1, `Lean/Environment.lean`, `readIRPartsOfMod` (lines 2093–2105), returns no IR parts if the `.ir.sig` file is absent, even when `.ir` exists. This accounts for missing IR/data and interpreter initialization failures in the affected imports.

`check_module.py` now preserves and hashes `.ir.sig` and `.ir.sig.hash` companions in the pinned overlay and includes them in local artifact integrity/publication checks. The regression suite additionally checks overlay inclusion and signature-artifact tampering; fake compiler tests use an isolated shared test lock so they do not contend with real Lean checks. The production global compiler lock is unchanged.

Evidence:
- All 10 runner regression tests pass (`/tmp/classicism-checker-regressions.log`).
- Real Lean import regression passes for `Mathlib.Order.CompleteBooleanAlgebra`, `Aesop.Script.Util`, and `ImportGraph.Lean.Environment`: `checks/20261023T044120026462Z-e23dab5a.json`.
- Manifest is complete with current captured sources matching; the test is infrastructure evidence, not a mathematical certificate.
- Database validation passes: 132 principles, 447 results, 162 models.

## Rollout to waiting owners

Invocations started before this repair may already hold the old runner code in memory while waiting on the lock. Restart only your own still-waiting invocation safely so it loads the current helper. If already compiling, let it finish; rerun with the current helper only if a relevant infrastructure error occurs. Never terminate another lane, release or unlink its lock, or launch raw Lean/Lake.

Affected mathematical proof ownership remains with the existing authors. Their targets must be rerun through `check_with_mathlib.py`; the passing import smoke test does not itself certify those targets.

## Reproduction

From the bundle root:

```sh
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/test_check_module.py
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_with_mathlib.py --lock-wait 300 --timeout 180 research/2026-10-22/lean-formalization/integration-checks/PrecompiledImportSmoke.lean
```
