# Actuality / world-representation formalization

## Current verification — 23 October 2026

Repair/check ownership has returned to this lane. The coordinator activated
the globally locked runner; the historical no-compiler handoff below no longer
controls scheduling. See `VERIFICATION-PROTOCOL.md` and the current update in
`verification-updates/world_actuality_gallin.json`.

The graph and truth-sort bridge certificates **pass** against the captured
current sources, with no source drift:
`checks/20261023T043023549683Z-0cf20b33.json`. This includes the actual tuple
rules for `graph_normalization_law`, `graph_realization_law`, and
`predicate_transfer_law`, and the translated `canonical_truth_bridge`.
Their four source hashes equal the historical hashes below. Earlier
ActualityCore/WorldRepresentation passes remain recorded separately by the
core integrator. Full graph/bridge helper derivation audits are the next
separate targets; the schema certificates do not by themselves certify every
composition and well-foundedness helper.

The continuation adds `ActualityCoreSyntax`, `ActualityCoreInterpretationRules`,
and `ActualityCoreMembership`. These use the existing deep relational type
and term constructors. Recursive supports and domains, bounded quantifiers,
local logical operations, and normalization at every relational output are
explicit syntax. The main new target is `translate_member`: an object-language
derivation of domain membership for every translated term, given the actual
world and membership of its free variables. The source is prepared; its
compiler/axiom status is controlled by the current update, not this paragraph.

That membership target is **not** a completed interpretation. Literal
application preservation, substitution/beta/eta/delta preservation, the
target Henkin structure and its full truth induction, and the higher-type
Gallin comparison still require proofs. No unrestricted extensionality,
external full domain, or unproved normalizer premise has replaced them.

`world-core-coverage-queue.json` preserves all **26** original world-algebra
keys from `inventory.json`, with their source caveats and cross-lane links.
In particular Boolean world-map, subalgebra, retraction and ultrafilter
classifications remain explicit targets. Ordinary functional sections and
retractions stay with their separate owner. General representation helpers
are not counted as certificates for these separate classifications.

## Historical author handoff — 22 October 2026

**READY FOR INTEGRATION — FROZEN.** 22 October 2026, America/New_York.

Eight module/check files and 51 small translation drivers are ready for the
designated serial compiler owner. This worker has run no Lean/Lake/compiler
process, installation, download, or additional agent. The compiler owner may
repair the frozen files. These are prepared proofs, not checked certificates.

## Source hashes at author handoff

| File relative to bundle root | SHA-256 |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ActualityCore.lean` | `4cbf4b0d3d7c28b966015d752d8076d50aae0ecde71f9337dee8ff01c148ac4e` |
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreCertificates.lean` | `cdd86bce5541c51feb8e7704609b6dd18b47e331d2b787ed3bf3310406d5ce1c` |
| `topics/classicism/lean/Classicism/Results/Research/WorldRepresentation.lean` | `1f003c527c1161ee8b2be9101de3dd20cd60b05974f4e17c9d95ceaa339c179e` |
| `topics/classicism/lean/Classicism/Results/Research/WorldRepresentationCertificates.lean` | `007b06bd8f6cd62a9a3a7fe35e95ace25738b5a9cc0b0c9f6375a0a35e584fa6` |
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreGraphs.lean` | `72cd36928026da84423ae6a70145c75736ab2924e49b8ed036a5112a6b79b3e9` |
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreGraphsCertificates.lean` | `e5c00d817fab20981aea02fcd44e5eab229feefa2d369e9f9c6e3f8ac370a8a0` |
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreBridge.lean` | `f12a7c6fd89d8afe03888ea91e246b490812d880ced3019c35b9e93a98b144e2` |
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreBridgeCertificates.lean` | `2972eae6c82f81dfd4db5c28a4a5c87c573a9f1a0dff60a9d49a5e5c3ef9c5ee` |

The manifests `world-core-actuality-manifest.json`,
`world-core-representation-manifest.json`, and `world-core-graphs-manifest.json`
also record every individual driver hash. Hashes identify the author handoff;
later integrator repairs may legitimately differ.

## Prepared mathematical scope

- **ActualityCore:** localization and current-order reflection at arbitrary
  relational types; supported cuts, idempotence, domains and section/beta
  closure; local truth, equality and quantifier operations; represented unary
  interval joins; exact cut kernels and local atoms reusing `AtomCoordinates`.
- **WorldRepresentation:** atom-relative Boolean, quantifier, identity and modal
  truth laws; admitted normalized encoding/decoding, support, rigidity, inverse
  identities and finite Boolean preservation. The closed wrapper assumes only
  `NecPlenitude Prop Prop` and derives C5 and necessary Actuality from existing
  results. No Choice or external-family premise is added.
- **ActualityCoreGraphs:** current graph normalization and its exact kernel;
  preservation/reflection of function, injection and surjection properties;
  composition, associativity and supported identities; literal realization of
  graph-selected relational outputs; represented predicate quantifier transfer
  with explicit extension invariance; represented well-foundedness transfer.
  Individual outputs remain graph-valued.
- **ActualityCoreBridge:** canonical inverse maps on the current truth sort,
  between propositions below the actual world and endpoint truth objects. It
  reuses `ActualEvaluator` and `truthKernel`; existence/global normalization of
  the evaluator remains with the core worker.

## Exact checking plan

`world-core-check-commands.txt` contains every exact command in dependency order,
without placeholders. Run one command/process at a time; no parallel builds.
The commands use the compiler owner’s existing `check_module.py --timeout 180`.

Each one-target driver requests the Classicism gate, relational-type audit,
a genuine translated object-language C derivation, and its axiom report. The
schema files require actual `.listRule` declarations for interval completeness,
local atom coverage, world representation, graph normalization/realization and
predicate transfer. A missing tuple declaration is deliberately a failed check;
no tuple certificate is claimed merely from unary source code.

No generated statements, record YAML, original notes or existing proof files
were changed by this worker. No mathematical axiom, proof hole, external full
powerset, forbidden individual-output function or language extension was added.

## Exact remaining interpretation obligations

1. Define the recursively indexed local and Gallin core domains in the deep
   relational-type syntax, including parameter environments. The supplied
   support and section lemmas are the local induction steps, not that recursion.
2. Prove full term and formula interpretation by induction, with bounded
   higher-domain quantifiers and graph-valued individual substitution. The
   represented predicate transfer theorem requires extension invariance; it
   does not grant it to arbitrary intensional predicates.
3. Import the core owner’s globally bivalent Gallin normalizer and prove the
   higher-type local/Gallin inverse maps and application/quantifier preservation.
   The delivered comparison is the truth-sort base, not the full isomorphism.

These gaps prevent claiming a completed extensional-Henkin/Gallin interpretation.
Current domains are not identified with future domains. The numerical and real
interpretations remain with the assigned Infinity and probability authors.

## Local checks performed

Repository validation passed: 132 principles, 447 results, 162 models.
`world-core-validation.log` records the final check. A noncompiler static scan
found balanced delimiters/comments and no `sorry`, `admit`, or axiom declaration
in the 59 handed-off Lean files. This is not elaboration, gate success or proof
certification.
