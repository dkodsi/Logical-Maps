# Reproducing the recorded checks

## 1. Check the delivered bytes

Run `python3 verify_package.py`. Python's standard library is sufficient. This hashes the delivered files and does not execute Lean or any archived script. SHA256SUMS inventories the current package. ARCHIVED-ARTIFACTS.json summarizes the omitted build artefacts and coordination history.

## 2. Prerequisites

The preserved `source/topics/classicism/lean/lean-toolchain` pins Lean 4.33.1. `lake-manifest.json` pins Mathlib to commit `0df444a360eaa60ab8c11dca51a86af692955474` and records the exact remaining package commits. Use those revisions on the recipient's platform. The toolchain and compiled dependencies must be supplied separately. The `dependencies/` subset preserves the exact matching external sources used in selected checks, with their licenses and hash inventory.

Do not use a whole-library default build as evidence for a specific result: the tree intentionally includes draft modules. Reproduce only the relevant exact target and its dependencies. The supplied checker records source fingerprints and principal axiom reports.

## 3. Portable source-map reproduction

`reproduce_certificate.py` relocates a selected saved manifest, uses only matching supplied source bytes, and delegates to the original serial checker. It prints a plan by default. Supply an existing matching Lean executable, the required compiled dependency roots from your pinned installation, and a fresh writable output cache:

```sh
python3 reproduce_certificate.py   --manifest 20261023T054730505817Z-9a834f08.json   --lean /your/lean-4.33.1/bin/lean   --precompiled-root /your/mathlib/.lake/build/lib/lean   --precompiled-root /your/mathlib/.lake/packages/batteries/.lake/build/lib/lean   --cache /your/writable/check-cache
```

Add the other compiled dependency roots required by the target, as recorded in its manifest. Review the plan, then append `--run` to compile. The helper supplies the five explicit Mathlib roots required by the documented public-meta-import parser omission for the final Max target. It does not silently rewrite the original checker. Run in a separate working copy if you want to keep the verified package directory unchanged: new compiler logs/cache reports will otherwise be written under its source tree and will no longer match the delivered SHA256SUMS inventory.

Legacy-format reports do not contain the newer per-file source map. The helper refuses to pretend otherwise. For modal propagation, use the included actual axiom driver and original successful manifest; the exact fingerprints are retained in the saved evidence. No clean-environment Lean rebuild was performed as part of packaging, so these portable commands are a reproduction procedure, not a report that a second machine has passed them.

## 4. Expected result and scope

Require a completed successful check of the exact target declaration, matching captured sources and its printed axiom evidence. A whole batch need not pass if a selected target completed successfully before an unrelated later failure: the receipt must identify the successful target and preserve the batch’s actual outcome. A timeout, busy lock, changed-source report or skipped target is not success. A helper lemma, semantic framework or conditional reduction cannot be substituted for a principal theorem. Distinguish shallow C inference rules such as Classicism.em from the axioms of their translated derivations. Supporting sources can intentionally contain unverified work; the accepted declaration and its successful target check determine scope.

Repository validation is independent: install the source project's small Python requirements if necessary, then run `python3 scripts/pmap.py validate` from `source/`. The package's saved validation log records the packaging run; it is not a Lean certificate.

## 5. Exact source closures

The normalized receipts in [evidence/CERTIFICATES.json](evidence/CERTIFICATES.json) map module names to the exact successful source bytes, reusing existing files where possible. Their original run state is preserved: some selected targets passed before an unrelated later target failed. Only the selected successful targets are claimed.

The three retained generated-algebra component logs have no explicit principal axiom report; their `evidence_kind` and `explicit_principal_axiom_report_present` fields preserve that scope. Current result-level coverage, including the later certificates, is stated in the [evidence index](evidence/RESULT-INDEX.md#arithmetic-foundations).

Run `python3 certificate_sources.py` to verify the indexed receipts, mapped source and retained principal log. To materialize one exact source closure outside the package, run:

```sh
python3 certificate_sources.py --certificate beta-eta --output /your/fresh/beta-eta-sources
```

The output recreates module paths for that selected check. The helper neither compiles nor downloads dependencies. Use the receipt's pinned compiler and Mathlib dependencies to compile the listed target modules in dependency order, using the original serial checker in a separate working copy. A successful byte check or materialization is not a new compiler certificate. Draft translation/model sources are not included as accepted certificate targets.

## 6. Maintaining the summaries

Edit the structured records, then regenerate their views. `MAIN-RESULTS.json` owns each detailed entry’s statement, scope, significance, mathematical status and exact Lean status. Its `overview` supplies the shorter main-page summaries, grouping related entries through `result_refs`; `supplemental_results` identifies entries retained in the full index. Every detailed entry must occur in exactly one of these presentation roles. Notation changes must preserve the statement’s type and modal scope; do not apply blanket substitutions to principle names. `CATALOG.json` preserves all stable keys and supporting evidence; `result_ref` aliases inherit the main entry’s wording, `lean_status_ref` inherits the exact status of a matching main result, and `lean_status_refs` points to narrower aggregate coverage. `CONJECTURES.json` owns the questions, established progress and remaining obligations, and refers to main entries for formalization status. `DATABASE-INTEGRATION.json` owns proposed integration actions and captured database-record states. Its snapshots are historical evidence, not a live mirror. `CANDIDATES_DK.json` owns the isolated explorer proposals, their type and modal scopes, source locators, and evaluation equivalents; the renderer checks their evidence references and generates `CANDIDATES_DK.md` and the marked principle-reference section in `proofs/h-observer-space/GRAPH.md`. Proposed IDs are not active database records. Supplementary assessments enter that same integration source with their exact statements, scopes, existing-record relationships, proof locators, Lean coverage and remaining obligations. Preserve the original intake receipt and its hash; scope receipts can sharpen a row without promoting its database status.

```sh
python3 render_results.py --check
python3 render_results.py --write
```

The first command is read-only and fails on stale generated Markdown, incomplete result or presentation coverage, missing evidence or altered database snapshots. The second updates the summary views and the generated observer-principle reference section; it does not change mathematical or certificate verdicts. Review the diff and validate the relevant database after editing. A research-module certificate does not authorize setting an official `lean: verified` flag by hand.

After reviewing an intentional local package update, regenerate its byte inventory and check it:

```sh
python3 render_results.py --write --refresh-checksums
python3 verify_package.py
python3 certificate_sources.py
```

Refreshing checksums records the new local bytes; it does not authenticate a theorem or supersede a frozen release. These commands invoke no Lean compiler, network service or publication action. Keep source proofs, accepted manifests and exact certificate source maps unchanged; add new evidence with its own provenance.

## Publication metadata

Machine-specific paths and research coordination fields are omitted from the delivered metadata. Normalized compiler manifests retain the original manifest hash as provenance, along with unchanged source hashes, compiler fingerprints and recorded check outcomes. Lean source bytes and principal theorem reports are preserved.
