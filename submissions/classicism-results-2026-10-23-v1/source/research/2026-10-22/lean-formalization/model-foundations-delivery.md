# Model foundations: delivery and verification scope

This is the current contribution summary. The historical submissions in
[model-foundations-status.md](model-foundations-status.md) are retained;
their frozen-ownership and pending-check descriptions are historical.
Current ownership and machine-readable progress are in
[the lane update](verification-updates/model_foundations_signature_nominal.json).
Work has stopped for the user's hard deadline. No compiler or continuation is
left running by this author. Resumption requires a new human instruction.

## Statements and evidence

| Package | Exact scope | Evidence |
|---|---|---|
| Finite-sort structures | Exhaustive covers of size 1, 2, or 3; Atomicity, Boolean Completeness, Actuality at t, and relational choice to any admitted output sort, including e. No all-bounds internal proof generator is claimed. | **Fresh gate/type audits and all twelve C-minus translations passed** in [the locked check](checks/20261023T051245030376Z-c1fd79a4.json). [Exact independent-target evidence](model-foundations-existing-certificates-20261023.json). |
| Boolean-valued semantics | Existing typed syntax interpreted over a complete Boolean algebra; substitution, conversion, C soundness, designated-truth soundness and modal value calculations. Generic semantics, without a concrete countermodel claim. | **The complete driver passed again** in [the locked check](checks/20261023T051245030376Z-c1fd79a4.json). Eleven declarations were audited; classical metatheory uses propext, Classical.choice and Quot.sound. |
| Single-predicate full models | Exactly the admitted signature {c:e→t}; full one-world Bool and Nat individual domains; c selects false or zero. Actual Independence and map schemas, complete consistent theories and the twelve central-question targets. Nonentailments refute signature-uniform claims, not every separately prescribed richer signature. | **The full principal driver passed**, with current sources matching, in [the locked check](checks/20261023T051126488606Z-b00090cd.json). [Exact declarations, hashes and axiom dependencies](singlepredicate-verified-20261023.json). |
| Supported nominal hierarchy | All supported elements/functions for finite or countable support ideals; candidate typed evaluator, conversion and soundness; pure syntax and specified globally fixed constants. Arbitrary non-fixed interpretations of constants are outside this evaluator. | **The full driver has not passed.** The exact checked prefix, current sources and next obligation are recorded in [the lane update](verification-updates/model_foundations_signature_nominal.json). This is not a verified nominal classification. |

The principal single-predicate declarations are
`Classicism.Meta.SinglePredicateFull.bool_complete_countermodel` and
`Classicism.Meta.SinglePredicateFull.nat_complete_countermodel`, plus the
twelve explicitly listed declarations in the historical submission.
The driver audits them directly, not just their helpers.
All 27 audited declarations use only propext, Classical.choice and Quot.sound,
or fewer. No sorryAx or new mathematical axiom occurs in those dependencies.
This verifies the external model argument; it does not change database flags.
[The final source-integrity comparison](model-foundations-source-consistency-20261023.json)
confirms the captured local dependency closures still match the live files for
all three successful targets.

For the generic Boolean-valued package, C soundness requires a nonempty
individual domain. Designated-truth soundness additionally designates a
nonzero Boolean atom and requires the optional axioms to hold there. The
distinctness-value theorem assumes a nontrivial Boolean algebra. These
premises are retained in the checked declarations.

The nominal driver includes actual C/C5 and quoted-IC targets, the exact
selector/stabilizer equivalence, full-domain Dedekind operations for distinct
orbit sequences, and concrete world examples. The new
`NominalFiniteOrbitStrata.lean` implements the existing finite-orbit proof:
restriction to finitely many stabilizer-orbit representatives injects the
fixed propositions into a finite function space. For atom worlds, the support
points and at most one fresh atom supply those representatives. Principal
declarations are `Classicism.Meta.Nominal.Examples.finite_atoms_not_dedInfT`
and `finite_atoms_boxed_not_dedInfT`. These have proof bodies and audit targets;
they are not claimed checked before their driver passes.

## Full prose proofs

- [Finite-sort argument](../notes/positive-effective.md), §§23.1–23.3.
- [Concrete one-world models and exact signature qualification](../central-questions-audit.md).
- [Nominal choice and Dedekind classification](../notes/nominal-choice-classification-20261022.md), §§1–8.
- [Countable-support construction](../notes/countable-support-choice-countermodel-20261022.md), §§8–9.
- [Larger-support geometry](../notes/support-bounds-world-geometry-20261022.md), §§1–5.

These are original, unpaginated research notes (direct source category misc).
The source notes' prose conclusions and the narrower Lean coverage must remain
distinct. No new headline conjecture or strengthened premise is introduced by
this delivery work.

## Remaining Lean coverage

The current nominal SupportCore, LogicalOperations, TypedHierarchy and
Substitution modules pass in
[the last substantive nominal check](checks/20261023T053031030293Z-15212e27.json).
These are infrastructure checks, not a nominal model or classification
certificate. NominalConversion then left six reflexive goals. The source
repairs are saved, but [the final attempt](model-foundations-final-attempt.log)
exited busy before compilation. The next obligation on explicit resumption is
to check `Classicism.Models.NominalConversion`, then continue the full driver.
Soundness and the downstream nominal verdicts have not been checked.

The general nominal classification still lacks its finite-support
intersection/least-support and orbit-decomposition proofs, the nontrivial IC
reservoir and explicit failure constructions, the general two-sided orbit
classification, fresh-pair FC/RC failures, all-type Atomicity and standard
number/core/Frege-infinity verdicts, and the larger-support cardinal cases.
The atom-world finite-strata proof does not discharge these other obligations.
The exact finite-strata theorem remains explicitly conditional for arbitrary
world actions until the appropriate orbit theorem is supplied.

## Reproduction and corrections

Run from the bundle root using the pinned dependencies and the global lock:

```sh
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py Classicism.Models.SinglePredicateCountermodelChecks --timeout 300 --lock-wait 300
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py Classicism.Models.NominalFoundationChecks --timeout 300 --lock-wait 300
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py Classicism.Results.Research.FiniteSortStructureCertificates --timeout 300 --lock-wait 300
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py Classicism.Semantics.BooleanValuedChecks --timeout 300 --lock-wait 300
```

Run these sequentially. Exit 75 means the compiler slot remained busy and no
check began. Exit 3 requires checking the changed current sources again.
The current lane update retains source hashes and exact manifests. A passing
module alone is not a database `lean: verified` promotion.

Source repairs during ownership return: use `Mathlib.Data.List.FinRange`
for `List.nodup_ofFn`; use `Mathlib.Data.Finite.Defs` and `not_finite Nat`
for the finite-strata contradiction; import the direct permutation-group
provider `Mathlib.Algebra.Group.End` instead of an unavailable broader import.
Repository validation passes; that validates the records, not these Lean proofs.
The one-world source repairs also made sentence satisfaction explicit, corrected
Boolean-lemma naming and definitional reductions, supplied the concrete-domain
inhabitation instances, made equality transport explicit, and used type
annotations rather than an unavailable generated-schema binder name. The
principal statements and their signature scope were preserved.
