# Choice and splitting: delivery contribution summary

23 October 2026. Formalization of existing natural-language research over fixed,
finitary C. The [verification update](verification-updates/choice_sections_retractions.json)
records current targets, exact source hashes, manifests and unresolved obligations.
No mathematical YAML verdict, generated statement or database Lean flag was edited.

**Final delivery check passed.** [Aggregate manifest](checks/20261023T053945495916Z-2d579847.json)
checks all 120 local source modules in the dependency closure, reusing only
matching recorded artifacts where allowed. The live closure was independently
hashed and matched all captured sources. The [aggregate axiom report](logs/runs/20261023T053945495916Z-2d579847/Classicism_Results_Research_ChoiceSectionsRetractionsChecks.log)
prints all 19 requested principal theorem reports, with only `propext` and
`Quot.sound`, and no holes. 

## Checked principal results

- **Functional Choice iff Actuality plus ordinary sections.** At all admitted
  types, every actual surjection between relational types has a pointwise right
  inverse exactly when the splitting component of this characterization holds.
- **Plenitude iff Actuality plus ordinary retractions.** The corresponding
  pointwise left-inverse formulation covers every relational output and every
  original input type, including e.
- **Completely boxed forms of both equivalences.** Both premises, including the
  splitting schema, are boxed. This is distinct from the stronger benchmark with
  unboxed strong sections, whose remaining obligation is below.
- **Necessary injectivity iff a strong retraction**, per operation, including
  truth-valued output. C5 supplies these retractions. Two low-type tests,
  `t -> tt` and `tt -> tt`, give the converse C5 result for strong retractions
  or persistence of injectivity.
- **Relational masks recover Barcan.** Persistence of surjectivity, strong
  sections, or persistence of injectivity at the indicated mask endomorphism
  type gives the matching relational BF instance. The local list certificate
  keeps tuple existence explicit; its discharge belongs to the schema assembly.
- **Full relational Barcan characterizations.** Persistence of surjectivity,
  persistence of idempotence, and persistence of involutivity are each equivalent
  to relational BF. Strong sections are equivalent to ordinary sections plus
  relational BF. Tuple existence is discharged in C, including the empty tuple.
- **Pairing Representation iff Plenitude.** Representation of total,
  single-valued, symmetric relations at relational types already suffices for
  arbitrary admitted-input, relational-output unique-choice representation.
- **Stable unique graph representation.** BF at the input type represents
  stable unique relational outputs by a single necessarily correct operation;
  truth-valued output already gives the converse. The exact stable-witness
  criterion under ordinary Plenitude and BF also passes.
- **Modal unique witnesses.** Necessary unique-witness selection at t is
  equivalent to Extensionality there; the modal Plenitude and modal Functional
  Choice consequences have their exact certificates.
- **Rigidity under sections.** ND at the fixed-parameter type supplies weak and
  strong rigidity of every section, without boxed ND or BF. The converse already
  holds for nullary sections.

All full-schema assemblies use metalogical axiom sets, not type quantifiers in
C. No operation has output type e. Actual inverse equations, necessary inverse
equations, and literal operation-composition identities remain distinct.

## Proof sources

- [Functional Choice by sections](../notes/functional-choice-by-sections.md), §§1–4.
- [Choice and uniformization](../notes/choice-uniformization.md), §§1–2,6,11–12,18–20.
- [Reversible comprehension and algebraic laws](../notes/reversible-comprehension-and-algebraic-laws.md), §§1–2.
- [Rigid Boolean closure](../notes/rigid-boolean-closure.md), §7, only the assigned section component.
- [Relational Choice and completeness imply Actuality](../followup/choice-completeness-actuality.md), with its [audit](../followup/choice-completeness-actuality-audit.md).

These are existing prose arguments. Literature priority remains unconfirmed;
proof verification does not establish priority.

## Evidence and declaration map

All shallow declarations below have prefix `Classicism.Research.Splitting`.
Full-schema declarations have prefix `Classicism.Meta.Research.Splitting`.

| Scope | Principal declaration | Successful manifest |
| --- | --- | --- |
| Strong retraction construction and arbitrary relational output | `necessary_injection_splitting.listRule`, `necessary_injection_iff_retraction.derivable` and separate `_t` theorem | [044838](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| C5 gives strong retractions | `c5_strong_retractions.listRule` | [044838](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Actuality plus sections gives Choice | `actuality_sections_choice.listEntails` | [045645](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Actuality plus retractions gives Plenitude | `actuality_retractions_plenitude.listEntails` | [045645](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Full ordinary splitting characterizations | `functional_choice_equivalence`, `plenitude_equivalence` | [045645](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Relational BF mask, including nullary output | `relational_surjectivity_persistence_barcan.listRule` | [050342](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Stable unique graph representation | `barcan_stable_unique_graphs.listRule`, `uniform_graph_iff_stable_witnesses.derivable` | [050342](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Modal unique-witness collapse | `necessary_unique_witness_iff_extensionality.derivable` | [050342](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Rigidity of sections and exact ND converse | `nd_rigid_sections.listRule`, `rigid_point_sections_iff_nd.derivable`, weak analogues | [050719](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Full completely boxed splitting characterizations | `necessary_choice_equivalence`, `necessary_plenitude_equivalence` | [050719](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Surjectivity persistence and strong sections | `persistence_surjectivity_equivalence`, `strong_sections_equivalence` | [053829](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Pairing Representation iff Plenitude | `pairing_representation_equivalence` | [053829](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| Persistence of elementary algebraic laws | `idempotence_persistence_equivalence`, `involutivity_persistence_equivalence` | [053829](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |

These manifests passed source compilation, the requested Classicism gate and
relational-type audits, translated object-language certificates and requested
list rules. The schema files then assemble those derivations. Captured source
closures matched the live files when inspected. Printed theorem-axiom reports
for the metalogical certificates list `propext` and `Quot.sound`; no `sorryAx`
or new mathematical axiom was added.

The [earlier Choice handoff](choice-status.md) retains evidence for the sharp
`RC_(t,t) + BC_tt -> Actuality`, its correctly boxed form, the stronger local
TC consequence, the direct type-local RC+BC-to-TC proof, CBC+CCC completeness,
and truth reflection of represented joins. The aggregate check refreshed those certificates against the current shared
dependency closure, including the sharp Actuality theorem and JoinTruth.

## Final schema assemblies

The four mathematical assemblies below all passed in
[the final leaf manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2).
Its captured source closure was compared with the live files and matched.
The separate aggregate import also passed in the final manifest linked above:

- `SectionsRetractionsPersistenceSchemas`: persistence of surjectivity iff
  relational BF; strong sections iff ordinary sections plus relational BF.
- `SectionsRetractionsInvolutionsSchemas`: Pairing Representation iff Plenitude.
  Pairings are total, single-valued, symmetric relations on a relational type.
- `SectionsRetractionsIdempotenceSchemas`: persistence of idempotence iff
  relational BF.
- `SectionsRetractionsInvolutivePersistenceSchemas`: persistence of involutivity
  iff relational BF.

`ChoiceSectionsRetractionsChecks` imports all exact certificate families and
schema assemblies together and prints the principal theorem-axiom reports.
Its first attempt refreshed Completeness, FixedPoint, Chains, Countable and
Transversal successfully, then timed out at 120 seconds while translating
ChoiceActualityCertificates. The earlier successful Actuality translation took
156 seconds. The final aggregate retry passed: Actuality took 133.21 seconds,
JoinTruth took 7.22 seconds, and the aggregate target took 0.64 seconds.
The eight-minute outer wall limit was not reached. Evidence is in
`checks/20261023T053945495916Z-2d579847.json`. The initial failed attempt remains preserved.

The mask schema assemblies explicitly derive tuple existence from C using
`SectionsRetractionsExistence`; they do not add it to the optional premises.

## Corrections and precise remaining obligations

The first strong-retraction attempt checked the per-map proofs but omitted the
argument-list certificate. Explicit schema/list declarations repaired this.
The first rigidity attempt exposed a translation mismatch between implication
to false and primitive negation. An explicit Boolean-order step repaired it,
with no statement or premise change. The first persistence schema attempt
pulled in a broad shared record audit that timed out; a small local tuple-
existence derivation replaces that import while retaining the same C proof.

The stronger benchmark `necessary FC iff necessary Actuality + unboxed strong
sections` still needs the separate `C5 + Atomicity_t -> No Pure Contingency`
object-language derivation. Its mathematical database records are proved, but
their Lean status is stated; no callable complete derivation was found in the
current library. The completely boxed characterizations above do not settle
that stronger benchmark. No additional axiom or hidden premise replaces it.

Remaining unimplemented items in this lane are the singleton/Hilbert/atomic
choice normal forms, atomic-selector monotonicity collapse, bijection stability,
and the exact source-model separator certificates. The latter require actual
model verdicts and cannot be replaced by syntactic implications. The original
RC-alone-to-TC question and the prose's unresolved bare categorical-splitting
questions were not reopened as research.

## Reproduction and shutdown

From the bundle root:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceSectionsRetractionsChecks --timeout 180 --lock-wait 600
```

For a smaller repair, replace that target with the exact failed schema or
certificate module. Use the process-global lock; never raw Lean/Lake or a lock
bypass. Busy exit 75 is scheduling; source-drift exit 3 requires a fresh check.
Run `python3 scripts/pmap.py validate` after every edit batch. All validation
batches in this lane passed; the compact log is `.reproduction/classicism-sections-validation.log`.

