# Probability verification and repair

23 October 2026. Current owner scope: `AtomicProbability*` and `ProbabilitySymmetry*`. This page and the [live update](verification-updates/probability_internal_constructions.json) distinguish source compilation from C gate/type/translated-derivation certificates. The [manifest](probability-verification-manifest.json) records current source hashes, transitive local dependency matches, exact declaration names and saved evidence. Older frozen handoffs remain historical.

## Certificate scope

The full internal probability formalization remains incomplete.

Fraction, rational and concrete-cut constructions require their own successful checks; source submission alone is not certification.

## Confirmed evidence

| Layer | Current evidence | Scope |
|---|---|---|
| Constructive finite-list arguments | [043010 check](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1): four principal axiom reports are empty | Ordinary external finite mathematics |
| Scalar, finite envelope, finite fibres and finite-class symmetry | [044808 check](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1): thirteen principal reports, none using `Classical.choice`; twelve empty, finite-budget theorem uses `propext` and `Quot.sound` | Explicit scalar, finite-list and budget resources |
| Complete additivity and normalization | [045228 check](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1): principal signatures printed; three principal axiom reports empty | Supplied finite-support/finite-cover resources and positive rescaling; no internal interpretation or existence of division follows from the helper alone |
| Generic supported-real cuts | [045450 check](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1): C gate and type audits, fourteen translated derivations in C-minus | Current ActualWorld; represented cut base and represented bounded nonempty families; principal certificate reports use metatheoretic `propext`/`Quot.sound` |
| Original internal natural order | [051735 check](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1): 19/19 gate and type audits, nineteen translated derivations in C-minus | Original `FiniteCardinality` domain, quantified Infinity where stated; no assumption of external standardness |
| Supported number operations, addition and multiplication | [051735 check](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-23-v1): all three source modules pass ordinary Lean | Current ActualWorld plus quantified Infinity; C certificate attempt timed out at 180 seconds without diagnostics; no certification inferred |

The manifest is stricter than a source-only timestamp: an earlier successful run is current evidence only when its captured source and all transitive local source hashes still match. A cache hit is not substituted for the directly saved diagnostic log.

The interrupted [052005 runner manifest](checks/20261023T052005207226Z-a0a1f31d.json) retains its raw state; the [owner stop record](logs/probability-owner/20261023T052005151246Z.json) records deliberate termination and independently checked absence of the process group. The certificate timeout is incomplete verification, not a mathematical failure.

## Repairs and supporting source arguments

The external enumeration wrappers now use witnessed constructor-based proofs, avoiding the earlier reported choice dependency. Recursive definitions in Complete use corrected recursive-call syntax. Internal arithmetic theorems explicitly include the original context hypotheses used in their proofs. Natural-order disjunction elimination was rewritten with `Or.elim` to obtain the translated certificate without altering its mathematical statement.

The [cut-crossing and inverse proof](probability-cut-crossing-proof.md) has full source and certificate drivers in `AtomicProbabilityCutCrossing`, `AtomicProbabilityRationalNegation` and `AtomicProbabilityConcreteRealInverse`. It derives adjacent crossing from internal induction, then a small cut gap and the reverse additive-inverse inclusion. These are verification-pending arguments, not extra interface assumptions or certified probability equivalences.

## Outstanding obligations

1. Continue the arithmetic/fraction/rational/concrete-cut source and C-certificate dependency chain. The live update names the first outstanding target and its exact diagnostics.
2. Real multiplication, its ordered laws, and positive division/normalization remain mathematical construction work.
3. Represented internal finite-family operations, geometric budgets, faithful threshold/finite-fibre equivalences and the finite-block/canonical-rank reduction for the type ceiling remain separate obligations.
4. Preserve the global and weaker local probability premises and original-number transfer requirements; no full faithful-probability equivalence is certified by the partial constructions.

## Delivery and stop boundary

The [delivery map](probability-delivery.md) links the full prose, exact principal declarations, scope caveats and reproduction instructions. The [contribution summary](probability-contributions.md) gives the concise account. Repository validation passes for 132 principles, 447 results and 162 models; this is not Lean verification.

