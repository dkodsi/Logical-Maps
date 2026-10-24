# Certificate verification

A certificate identifies the exact theorem, assumptions, language, type scope, source hashes and successful compiler evidence. Source compilation, gate/type checks, translated object-language derivations and full model certificates establish different claims.

Use the pinned toolchain and dependency versions. The supplied checker captures its source inputs, verifies cache integrity, and records compiler and dependency fingerprints. A failed or skipped check does not certify a target. A successful target in a larger failed batch is usable only when its complete dependency closure and principal axiom report are identified separately.

Principal theorem reports must contain no `sorryAx`. Conditional theorems retain their hypotheses; helper lemmas do not certify the full result. Preserve unresolved mathematical or translation obligations explicitly.

See the [package reproduction instructions](../../../../REPRODUCING.md) and [certificate index](../../../../evidence/CERTIFICATES.json) for the retained evidence and portable commands.
