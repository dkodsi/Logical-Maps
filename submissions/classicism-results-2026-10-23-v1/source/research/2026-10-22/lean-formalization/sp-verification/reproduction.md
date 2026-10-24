# Reproducing the SP/Max checks

Run from the bundle root. The existing local environment uses Lean 4.33.1 and
the Mathlib revision and dependency roots recorded in
[mathlib-dependencies.json](../mathlib-dependencies.json). The compiler path and
SHA-256, each captured source hash, dependency fingerprints and archived output
are recorded in the [JSON ledger](verification-status.json) and its manifests.
The `/tmp` toolchain and dependency paths are environment prerequisites; the
reports do not make them portable or download replacements automatically.

The computability module needed eleven sources absent from the precompiled
subset. Their pinned original paths and hashes are recorded in
[mathlib-source-subset.json](mathlib-source-subset.json), and copies are staged
with module-relative paths under `.reproduction/classicism-sp-mathlib-sources`. These
files were compiled from the existing pinned checkout, without downloads.
If that staging directory has been removed, reconstruct it from precisely
those listed originals and verify their hashes before checking. Passing the
entire Mathlib checkout as a source root would unnecessarily rebuild a much
larger closure.

To check all twelve result modules and the adjacent public-axiom audit module
in a fresh, separate output cache:

```sh
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py \
  --lock-wait 300 --timeout 180 \
  --cache .reproduction/classicism-sp-reproduction-cache \
  --source-root .reproduction/classicism-sp-mathlib-sources \
  research/2026-10-22/lean-formalization/StrongPossibilityConsequences*.lean
```

The shared runner serializes compilation, captures the inputs, checks cache
integrity and saves a manifest and logs under `lean-formalization/checks` and
`lean-formalization/logs/runs`. A busy exit (75) means no compiler slot was
obtained. A source-drift exit (3) requires checking the changed source again.
Neither is a proof acceptance. Do not bypass the shared lock with raw Lean or
Lake. The [verification protocol](../VERIFICATION-PROTOCOL.md) controls these
checks.

To refresh the aggregate evidence without launching a compiler:

```sh
python3 research/2026-10-22/lean-formalization/sp-verification/collect_status.py
```

This checks saved success against the current transitive source/dependency
fingerprint, locates printed axiom reports, and rejects any report containing
`sorryAx`. It scans the core and both isolated SP report directories. A new
failed or changed-source check is preserved as such. The prose proof and scope
review remains a separate judgment from compiler acceptance.

Repository validation is separate:

```sh
python3 scripts/pmap.py validate
```

No database `lean: verified` flags were changed by these research checks.
