# Probability research: delivery map

23 October 2026. This is a status-preserving map of the existing arguments and their formal implementation. The source files and partial constructions are retained. It is not a claim that the full probability equivalences have passed Lean or the Classicism certificate pipeline.

## Mathematical statements and scope

| Existing argument | Exact scope retained | Principal implementation | Current boundary |
|---|---|---|---|
| Canonical atomic envelope and residual decomposition | Supremum of finite atom subsums; exact atom weights before normalization; represented complete additivity | `Probability.FiniteSupportSystem.graph_total_functional`, `value_add`, `value_positive`, `residual_add`, `completely_additive_graph` | Ordinary external algebra with explicit `MassScalar`, `FiniteSupportSystem`, bounded-supremum and finite-cover resources. It has not been instantiated as the full internal C probability theorem. |
| Normalization | A supplied positive additive order isomorphism rescales a faithful state at a specified top | `Probability.FiniteSupportSystem.normalize_atomic_state` | `PositiveScale` and its normalization equation remain explicit; existence of real division by the total is not proved by this helper. Normalization preserves atom-weight ratios, not the original masses. |
| Finite-class averaging | Equalizes weights in each given finite equivalence class, preserves its total, and is idempotent | `Probability.classAverage_total_functional`, `classAverage_preserves_class_sum`, `classAverage_idempotent`, `saturated_envelopes_equal` | External lists and explicit finite division. This is not yet the full represented-permutation invariance theorem. |
| Finite-fibre weights | Supplied label field and budget give a unique weight graph and finite-budget bound | `Probability.fibreWeight_total_functional`, `finiteFibre_finite_budget` | External Nat/List and supplied budget; internal geometric budget, threshold converse and internal finite-family interpretation remain separate. |
| Concrete supported arithmetic and cuts | Current ActualWorld w plus quantified Infinity at the counting type; all output types are admitted relational types | `ProbabilityNumericOperations.*`, `ProbabilityFractions.*`, `ProbabilityRationals.*`, `ProbabilityConcreteReals.concrete_real_supremum` | Source implementations exist; their C gate, type and object-derivation checks remain in the current queue. Completeness is for represented bounded nonempty families. |
| Cut small gap and additive inverses | Current internal natural induction, rational Archimedean bounds and actual supported cut codes | `ProbabilityCutCrossing.cut_has_small_gap`, `ProbabilityConcreteReals.realAdd_neg`, `realNeg_involution`, `realAdd_le_iff_le_sub` | Full source argument and drivers supplied; no check is inferred from source presence. Real multiplication/positive division remain unfinished. |
| Choice-free type ceiling | C + boxed Plenitude + quantified Infinity_e; admitted powersets and finite-fibre labellings | `ProbabilityCantor.no_predicate_injection` is the final diagonal component | The finite-block construction, canonical finite-fibre ranking and its reduction to the diagonal are not certified by the diagonal alone. |

All declaration prefixes in this table begin `Classicism.Research.`. Exact elaborated signatures for the conditional algebra are requested by `AtomicProbabilityDeliveryChecks`; source-only headers do not replace those outputs.

The weaker local propositional probability claim retains **C + Actuality + Atomicity_t + Boolean Completeness_t + quantified Infinity_e**, with graph-valued current states on current propositions in the actual-world core. It does not inherit global rigidity, future validity or the higher-type/type-ceiling conclusions. The global choice-free argument retains **C + boxed Plenitude + quantified Infinity_e**. The represented world-partition symmetry note retains its stated stronger **boxed Functional Choice** background. These packages have not been silently interchanged.

## Full prose proofs

- [Canonical atomic probability](../proof-refinements/canonical-atomic-probability.md), especially the finite-budget construction and the distinction between complete additivity and arbitrary countable additivity.
- [Choice-free faithful probability](../proof-refinements/choice-free-faithful-probability.md), including its internal arithmetic/finite-code obligations.
- [Local propositional probability](../proof-refinements/local-propositional-probability.md), for the weaker current graph interpretation and original-number transfer.
- [Represented world partitions](../proof-refinements/probability-under-world-partitions.md), with the original [world-symmetry note](../notes/probability-and-world-symmetry.md).
- [Choice-free type ceiling](../proof-refinements/choice-free-probability-type-ceiling.md), for the finite-block/rank argument preceding Cantor.
- [Internal cut crossing and additive inverse](probability-cut-crossing-proof.md), detailing the supporting argument implemented during formalization.

## Verification and reproduction

The [verification status](probability-verification-status.md) is the current evidence table. The [live update](verification-updates/probability_internal_constructions.json) supplies exact current targets and remaining obligations. The [manifest](probability-verification-manifest.json) records source hashes, all transitive local dependency matches, principal declarations, logs and historical runs.

Confirmed checkpoints are the constructive finite arguments (043010), repaired external scalar/envelope/fibre/symmetry algebra (044808), conditional complete additivity and normalization (045228), the generic SupportedReals C certificates (045450), and the NaturalOrder C certificates plus ordinary supported number arithmetic (051735). Exact linked manifests and axiom boundaries are in the status table. The broader numeric C-certificate run reached its 180-second per-module limit without diagnostics and was stopped; it supplies no additional C-certificate claim.

After explicit human resumption, reproduce through the shared locked checker from the bundle root, one substantive target or small dependency-ordered batch at a time. Example: `/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityDeliveryChecks --timeout 180 --lock-wait 300`. For C claims, use the matching `Certificates` target and inspect the gate, type, translated derivation and axiom evidence. Ordinary source compilation is a separate milestone. Busy exit 75 means no check started; source-drift exit 3 requires a fresh check. A timeout is incomplete verification, not a mathematical counterexample.

This session's [deadline wrapper](probability_locked_check.py) invokes only that shared runner and must have permission to signal its own process group. Its fixed stop guard is 05:55 UTC on 23 October; it is deliberately unusable after that time. No future run is scheduled. Any later deadline change requires explicit human resumption.

## Corrections and contribution

The external finite-enumeration wrappers use constructor-based witnessed proofs; permutation length uses the direct constructive theorem. Recursive calls in Complete were corrected. Arithmetic theorem binders explicitly retain the original ActualWorld/Infinity context where used. Disjunction elimination uses forms accepted by the C translator. These are source/translation repairs, with the actual evidence recorded per checkpoint.

The cut-crossing and reflected-complement inverse constructions have a [full prose argument](probability-cut-crossing-proof.md), source declarations and certificate drivers, but remain pending their dependency-chain checks. They do not add a small-gap or inverse hypothesis to an otherwise incomplete construction. Real multiplication/positive division and the internal finite-family/type-ceiling obligations remain unfinished.

[Contribution summary](probability-contributions.md). No original research note, published/human proof, YAML verdict, generated statement or shared Frege/Actuality source was changed by this lane.
