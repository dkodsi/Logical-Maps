# Reproducing the recorded checks

## 1. Check the delivered bytes

Run `python3 verify_package.py`. Python's standard library is sufficient. This hashes the delivered files and does not execute Lean or any archived script. The adjacent `.zip.sha256` file supplies the outer archive hash.

## 2. Prerequisites

The preserved `source/topics/classicism/lean/lean-toolchain` pins Lean 4.33.1. `lake-manifest.json` pins Mathlib to commit `0df444a360eaa60ab8c11dca51a86af692955474` and records the exact remaining package commits. Use those revisions on the recipient's platform. The toolchain and full dependency binaries are prerequisites, not included distributions; this release has performed no downloads. The `dependencies/` subset preserves the exact matching external sources used in selected checks, with their licenses and hash inventory.

Do not use a whole-library default build as evidence for a specific result: the tree intentionally includes draft modules. Reproduce only the relevant exact target and its dependencies. The existing globally serial runner is preserved, including its lock and bounded timeout behavior. Never remove another process's compiler lock.

## 3. Portable source-map reproduction

`reproduce_certificate.py` relocates a selected saved manifest, uses only matching supplied source bytes, and delegates to the original serial checker. It prints a plan by default. Supply an existing matching Lean executable, the required compiled dependency roots from your pinned installation, and a fresh writable output cache:

```sh
python3 reproduce_certificate.py   --manifest 20261023T054730505817Z-9a834f08.json   --lean /your/lean-4.33.1/bin/lean   --precompiled-root /your/mathlib/.lake/build/lib/lean   --precompiled-root /your/mathlib/.lake/packages/batteries/.lake/build/lib/lean   --cache /your/writable/check-cache
```

Add the other compiled dependency roots required by the target, as recorded in its manifest. Review the plan, then append `--run` to compile. The helper supplies the five explicit Mathlib roots required by the documented public-meta-import parser omission for the final Max target. It does not silently rewrite the original checker. Run in a separate working copy if you want to keep the verified package directory unchanged: new compiler logs/cache reports will otherwise be written under its source tree and will no longer match the delivered SHA256SUMS inventory.

Legacy-format reports do not contain the newer per-file source map. The helper refuses to pretend otherwise. For modal propagation, use the included actual axiom driver and original successful manifest; the coordinating historical fingerprint review is preserved in the research reports. No clean-environment Lean rebuild was performed as part of packaging, so these portable commands are a reproduction procedure, not a report that a second machine has passed them.

## 4. Expected result and scope

Require a completed successful manifest, matching captured sources and the exact target declaration. Inspect its printed axioms. A timeout, busy lock, changed-source report or skipped target is not success. A helper lemma, semantic framework or conditional reduction cannot be substituted for a principal theorem. Distinguish shallow C inference rules such as Classicism.em from the axioms of their translated derivations. Supporting sources can intentionally contain unverified work; the accepted declaration and successful manifest determine scope.

Repository validation is independent: install the source project's small Python requirements if necessary, then run `python3 scripts/pmap.py validate` from `source/`. The package's saved validation log records the packaging run; it is not a Lean certificate.
