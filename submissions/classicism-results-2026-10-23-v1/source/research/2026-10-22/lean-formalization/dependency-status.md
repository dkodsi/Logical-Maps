# Pinned model-semantics dependencies

22 October 2026, America/New_York. Setup completed by the sole compiler owner.

- Compiler remains Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
- Mathlib source is the exact project pin 0df444a360eaa60ab8c11dca51a86af692955474,
  extracted from its official GitHub archive into `/tmp/classicism-mathlib`.
  All eight transitive source pins match the project's unchanged manifest.
- Only the eleven modules of Mathlib's cache utility were compiled, serially.
  No Mathlib library source build, Lake update, toolchain change or project
  manifest edit was performed.
- The source-hashed official cache fetched the imports of
  `Mathlib.Order.CompleteBooleanAlgebra` and `Mathlib.Data.Set.Finite.Basic`:
  650 cached modules, all downloaded and decompressed successfully. The log is
  `logs/mathlib-narrow-cache.log`. Download/decompression concurrency was
  constrained by `RAYON_NUM_THREADS=1` where honored by the decompressor.
- `mathlib-dependencies.json` records the exact source revisions/archive hashes
  and eight precompiled library roots. `check_with_mathlib.py` invokes the usual
  serial checker with those roots. It hashes the compiled library artifacts
  before cache reuse; missing roots or missing imports are rejected. Default
  `check_module.py` still refuses unavailable external libraries.

From the bundle root:

```
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_with_mathlib.py --timeout 180 Classicism.Semantics.BooleanValuedChecks
```

This resolves the installation blocker. It does not establish soundness or any
model verdict: the individual compiler manifests determine proof status.

The named old/new model required 22 direct Mathlib imports from its exact local
dependency closure (`old-new-mathlib-roots.json`). The same pinned cache utility
fetched 378 additional cached modules, for 1,028 in total. No Mathlib source
library rebuild occurred. The additional successful run is preserved in
`logs/mathlib-old-new-cache.log`; the dependency manifest now records all roots.
