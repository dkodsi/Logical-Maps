# Strong Possibility formalization status

**Current verification:** see [the 23 October ledger](sp-verification/verification-status.md)
and its source hashes and archived checks. The user explicitly resumed checking
and delegation; the author has now compiled and repaired four modules in an
isolated cache, and the core task has repaired Schemas. The historical handoffs
below retain their original hashes and describe the earlier state.

Scope: original finitary C and its relational types, with one expressly separate
infinitary-numeral fragment. No YAML, generated statement, frozen research note,
or published/human-authored proof is changed. Repository validation is distinct
from Lean verification.

## READY FOR INTEGRATION — C consequence module (frozen)

- Source: `research/2026-10-22/lean-formalization/StrongPossibilityConsequencesC.lean`
- SHA-256: `d2c7c82da467d8436c9ba4dd02e5f4c815094dd2cab8dc702adc00a706edba6d`
- Ownership: handed to the core compiler task, which may repair this frozen file.
  This author will not edit it unless ownership is explicitly returned.
- Dependencies: existing `Classicism.Principles.Schematic`, `Tools.Check`,
  `Tools.TypeSystem`, and `Tools.Translate`; no new research module dependency.
- Proposed results: 31 C lemmas, covering H/D monotonicity, H conjunction and
  existential introduction, Boolean identity-matrix stability, universal-identity
  reflection, monism reflection, one/two-name exhaustion, and the exact universal
  fixed-point/disequality characterization of D.
- The module includes gate checks, type checks, and `#classicism_derive` for every
  proposed shallow theorem. A successful run must produce each `.derivable`
  object-language certificate; shallow elaboration alone is insufficient.

With the listed existing dependencies already built, run serially from
`/Users/danielkodsi/Downloads/classicism-map/topics/classicism/lean`:

```sh
lake env lean -o /Users/danielkodsi/Downloads/classicism-map/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesC.olean /Users/danielkodsi/Downloads/classicism-map/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesC.lean
```

Acceptance checks: no errors in gate/type/derivation commands; no `sorryAx` or
new axiom dependency; inspect generated quoted statements at `Ty.e` for monism
and at admitted relational output types for function-valued identities. The
`DecidesNe` premises on general predicate closure lemmas must remain premises.

## Mathematical/dependency boundary

- The existing result `strong-possibility-and-infinity-e-incompatible` is only
  `lean: stated`. Its C lemma `D E1 -> E1` is included above. Unconditional SP
  monism additionally needs a genuine certificate for `Con(Max + E1)`; no such
  coalesced-model consistency certificate was found in the searched library.
- The full Henkin completion, SP consistency, arithmetic interpretation lemmas,
  Boolean/truth elementarity, and the exact one-way embedding existence claim are
  not promoted to formalized models or C theorems here.
- Additional independent SP modules may be prepared below; frozen module hashes
  describe the handoff versions, and the compiler owner should record any repairs
  and replacement hashes separately.

## READY FOR INTEGRATION — stability/atom module (frozen)

- Source: `research/2026-10-22/lean-formalization/StrongPossibilityConsequencesStability.lean`
- SHA-256: `da0b6017c78b6e541c6e818f075572cdba6dcc4daa9e25972c530943a8ee5fbe`
- Dependency: the checked/repaired C module above. Handed to the core compiler
  task; no further author edits without returned ownership.
- Eight additional proposed C certificates: Boolean iff stability, fixed-matrix
  stability, `D D p -> D p`, algebraic-order stability, atom-matrix stability,
  `D Atom(w) -> Atom(w)`, and two atom/splitting contradiction forms.
- Gate/type/translation commands are included for every theorem.
- This provides the C core of the signature incompatibility argument. It does
  not assert the missing Max-consistency of the specific pure atom sentence or
  silently replace pure Max by signature Max.

After C.olean exists, from the same Lean project directory:

```sh
lake env sh -c 'exec env LEAN_PATH="/Users/danielkodsi/Downloads/classicism-map/research/2026-10-22/lean-formalization:$LEAN_PATH" lean -o /Users/danielkodsi/Downloads/classicism-map/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesStability.olean /Users/danielkodsi/Downloads/classicism-map/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesStability.lean'
```

## READY FOR INTEGRATION — sentence-schema module (frozen)

- Source: `research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSchemas.lean`
- SHA-256: `bbffb2c6cd4128d20ca17f68bf7f3ba3a72e17bf97c4c1df5c04c31d0c6798af`
- Dependencies: the two preceding modules and existing syntax modules. Handed
  to the core compiler task; no further author edits without returned ownership.
- Proposed metalogical proofs: exact SP instance formation, consistency
  transport by a C implication, equivalence of SP with the schema of
  Max-consistent sentences whose D-reflection C proves, and pure monism / no-two
  individuals conditional on the explicitly retained `Con(Max+E1)` fact.
- The general reduction is an entailment between the existing axiom sets and
  uses generated object-language certificates. It is not a semantic model or
  a declaration that all universal formulas have already been syntactically
  classified. The remaining coalesced-model consistency dependency is explicit.

After Stability.olean exists, from the same Lean project directory:

```sh
lake env sh -c 'exec env LEAN_PATH="/Users/danielkodsi/Downloads/classicism-map/research/2026-10-22/lean-formalization:$LEAN_PATH" lean -o /Users/danielkodsi/Downloads/classicism-map/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSchemas.olean /Users/danielkodsi/Downloads/classicism-map/research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSchemas.lean'
```

For this module, inspect the exported `Theorem`/`C.Theorem` conclusions and the
explicit consistency parameter rather than applying shallow gate checks to
metalogic. Confirm no `sorryAx` dependency and no extra assumed C rule. Source
modules have not been compiled by this author.

## Compiler evidence now available

The core integration record and `checks/20261023T020457049464Z.json` report
exit 0 for `StrongPossibilityConsequencesC`. Its log contains all 31 successful
gate/type/derivation checks and its source still matches the handoff hash.
This author has run no Lean/Lake process. The other submissions below remain
unverified until the core records successful source-fingerprinted checks.

## READY FOR INTEGRATION — substantive continuation (three files frozen)

The core compiler task now owns all three files and may repair them. The author
will not edit them without returned ownership. Commands below are for that task
only, serially from the bundle root; no download or broad library build is requested.

| Source in this directory | SHA-256 at handoff | Implemented conclusion |
| --- | --- | --- |
| `StrongPossibilityConsequencesMaxDiagram.lean` | `b6ab084c767730297a0e37b8fef985602186084890dc8d662910e2e92eb7a5ee` | Every consistent extension entailing original Max has exactly C's closed-type identities; recomputing distinctness gives the identical schema; re-maximalizing adds no theorems; structural derivation of the complete finite Boolean identity diagram. No standard model or desired diagram is assumed. |
| `StrongPossibilityConsequencesSignatureSplit.lean` | `293d2571fa6234e8955b082b34c84e7ccc21efd72424b0705390a3452bb559f8` | Constructs two actual singleton extensional interpretations (all relational constants top/bottom), proves C-consistency of both pieces of F and E1, and derives signature Max's not-Atom(F and E1) for every admitted signature. No splitter/model premise is assumed. |
| `StrongPossibilityConsequencesAlgebra.lean` | `ed733dddbcbe2387a77946764aaea459e0685e5219157fbd366f207a1d08ebe6` | Ordinary Boolean algebra: ideal closure and exclusion of newly created fixed points in a specified quotient; numerical retraction/injectivity reductions. The quotient map, arithmetic interpretation, and numerical canonicity inputs remain explicit; no C model is constructed. |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesMaxDiagram.lean --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesSignatureSplit.lean --timeout 180
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesAlgebra.lean --timeout 180
```

The signature module depends on the frozen stability module; the helper must
check that dependency first. Its final C step specializes that module's actual
translated certificate. The semantic consistency proofs use the existing
`Interp`/soundness machinery. Inspect exported axiom lists and exact syntax.

**Still missing for the FULL signature nonconservativity/incompatibility:** the
pure-profile action model, its closure under all terms, its pure Max verdict,
finite extensional pointed completeness, and hence Con(pure Max+Atom(F and E1)).
These are completed ordinary research arguments requiring implementation, not
an open mathematical consistency conjecture. They must not be confused with
the genuinely unresolved consistency of SP itself. The new signature module
discharges the two finite C-model side conditions; it does not discharge the
pure-profile side by taking it as a hidden hypothesis.

Repository validation after this batch: 132 principles, 447 results, 162 models
— OK. This is not Lean verification.

## READY FOR INTEGRATION — finite-proof reflection and SP diagram (frozen)

- Source: `StrongPossibilityConsequencesReflection.lean`
- SHA-256: `80d6921d4f358ce299fdb786c56725e2e84f35f82d6167606d5d5304bb271302`
- Ownership passes to the sole core compiler task; author will not edit it.
- **Unconditional implemented metatheorem:** an actual derivation of p from
  signature-relative Max yields an actual derivation of BoxNe p from that same
  Max. It extracts the finite optional-axiom support using the existing
  `Syntax.FiniteChoiceBasis`, derives its conjunction's possibility-reflection,
  discharges the conjunction, and necessitates only the resulting C theorem.
- Also supplies the negative SP diagram directly from Max non-theoremhood, and
  both exact BoxNe theorem/negative-theorem diagrams under Con(Max) and Con(SP).
  Con(Max) is a known ordinary construction awaiting its formal implementation;
  Con(SP) remains mathematically unresolved. Neither is silently inferred.
- Six new shallow helper certificates carry gate/type/derive commands. Public
  metalogical conclusions carry axiom-print commands. No effective hierarchy,
  standard-arithmetic existence, or complexity theorem is inferred here.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesReflection.lean --timeout 180
```

## READY FOR INTEGRATION — conservativity, actual diagonal programs, and enlarged syntax (frozen)

Ownership of these three files passes to the core compiler task. Author will
not edit them without returned ownership. No compiler/download was run here.

| Source in this directory | SHA-256 at transfer | Exact scope |
| --- | --- | --- |
| `StrongPossibilityConsequencesMaxConservativity.lean` | `3421af96a64f29e775771fd24f7411b5dfa5423de3017eded4b60a76d2a1a4e4` | Both directions of closed-identity conservativity iff consistency with original Max, retaining Con(Max). The converse extracts a finite conjunction of actual Max axioms; it does not assume the desired consistency. One new gate/type/derive certificate. |
| `StrongPossibilityConsequencesComputability.lean` | `0dc399b6e2e56c063b76a069aa3f2c862aef4293808b7f67f0d9b7f65a4bff14` | Ordinary metatheory over Mathlib's actual program codes: the output-0/output-1 halting sets have no computable separator, and no total computable code-indexed prediction avoids every program's output. The self-referential program is constructed with the existing recursion theorem. No C theoremhood/degree classification is asserted. |
| `StrongPossibilityConsequencesInfinitaryNumerals.lean` | `f27b7d8a5e6ca67996cd2c4d9bc531f21e2481ca75988dcf942b7550f5ecedc9` | Explicit enlarged numerical syntax with external countable disjunction, local semantics, and lambda-comprehension beta law. Constructs the standard-range predicate, proves impredicative numberhood equals numeral exhaustion, and proves unique names under the displayed Peano properties. This is explicitly outside finitary C. |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesMaxConservativity.lean --timeout 180
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesComputability.lean --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesInfinitaryNumerals.lean --timeout 180
```

The computability import's cache availability is for the compiler owner to
resolve within its existing dependency policy. This author has not downloaded
it or requested a broad Mathlib build. The infinite-syntax file proves the
local standardness mechanism, not yet the full original-Max incompatibility:
the C interpretation, Sum/Prod induction and incompleteness branches remain.
Neither an external Boolean description nor a new infinitary lambda body is
being silently included among the original finitary SP instances.

## READY FOR INTEGRATION — exact universal grammar and schema equivalence (frozen)

- Source: `StrongPossibilityConsequencesUniversalCore.lean`
- SHA-256: `c1e7a9e22bfec7048bcd9ad478585c01a484bdd6f77a07bc497bd6bb603664aa`
- Ownership transferred to the core compiler task; no further author edits.
- Defines the actual finite Boolean-identity matrix and universal-prefix
  grammar over arbitrary typed C terms. Constructs C derivations of matrix
  stability and universal D-reflection by structural induction, including the
  explicit lambda/beta conversion in the universal case.
- Constructs the fixed-point/disequality universal normal form of D p and
  proves both schema entailments between original SP and individually
  Max-consistent members of that grammar. No assumed reflection certificate,
  consistency fact, semantic model, or infinitary syntax is used in this result.
- The existing `Schemas` file remains useful but is no longer the only
  proposed core reduction: this new file supplies the previously missing
  syntactic classification. All new proofs conclude existing C derivations or
  exact axiom-set entailments; public axiom-print commands are included.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesUniversalCore.lean --timeout 180
```

## READY FOR INTEGRATION — restricted disjunction criterion (frozen)

- Source: `StrongPossibilityConsequencesDisjunction.lean`
- SHA-256: `d8131ed51d0dbccc0365bb1d431ff96c37667b9062ec6c1f181ce6327ce1db91`
- Ownership transferred to the core compiler task; no further author edits.
- Uses the actual universal grammar and finite proof-support theorem to prove
  both directions of the restricted finite-disjunction criterion for SP
  consistency (retaining Con(Max)). The disjunction is precisely spelled
  `not (conjunction L)`, including the empty-list case. It does not assume or
  establish that the disjunction property itself holds globally.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py research/2026-10-22/lean-formalization/StrongPossibilityConsequencesDisjunction.lean --timeout 180
```

## Current compiler snapshot and exhaustive queue reconciliation

The saved manifest `checks/20261023T032657816117Z.json` confirms successful
checks for C and Stability (31+8 shallow lemmas, with generated C certificates).
The Schemas check in that manifest failed at the double-D syntax conversion;
its source has since changed under the compiler owner's repair ownership.
No success is asserted for that repaired version without a matching check.
All later modules remain submissions until their own accepted manifests exist.

`sp-family-status.md` and `sp-family-inventory.json` now retain **all 32** queue
keys currently assigned to this lane in `coverage-and-ownership.json`, including
principles.24 and every assigned effective complexity/degree family. The
machine-readable key sets were reconciled exactly. Each family has its exact
remaining obligation; the shared model, arithmetic, coding, recursion/basis,
and infinitary bridges are identified separately. No main effective hierarchy
or model-capacity family is declared complete from a supporting lemma.

At this snapshot there are 12 submitted SP source modules. Their current hashes
all match the handoff hashes except Schemas, which the compiler owner is
repairing. Repository validation still passes (132/447/162); no compiler or
download was run by this author.
