# Maximalism and Atomicity Lean verification status

22 October 2026. **The full inconsistency is not Lean verified.**

## Fresh modules ready for integration

Both files below are frozen. Compilation, repair and axiom inspection pass to the designated sole serial compiler. The author ran no Lean or Lake process.

| Module | SHA256 at transfer | Scope |
| --- | --- | --- |
| MaxAtomicityHCodeSyntax | ddb243141435b8936629de3646132a0926e4c013659469091bfda7bae6862cbf | Concrete Rows plus Cover term, with closed-type and purity proofs; no collapse or existence theorem |
| MaxAtomicitySplitCertificate | 1b3073449ce0d8fd45ea234cc71f06ab4a3523bb1c1cab43785a016f79298553 | Instantiates the checked bounded-splitter derivation for arbitrary closed F, derives the exact unboxed Atomicity zero identity, and removes the top guard by a C identity |

Source paths and exact serial commands from the bundle root are in [the handoff manifest](max-verification-handoff.json). These are source submissions, not successful compilation reports.

The substantive new target is `split_zero_under_atomicity`: the positive identity is derived instead of supplied as a hypothesis. The final inconsistency theorem in that module remains conditional on non-theoremhood of the same identity in bare C. It does not provide that certificate.

## Existing checks confirmed against current sources

The current source and recursive dependency fingerprints match successful recorded checks for MaxAtomicitySyntax, MaxAtomicitySetSyntax, MaxAtomicityReduction and BoundedSplitter. This was confirmed by recomputing the checker's hashes using the recorded compiler version; no compiler process was started.

The reduction is conditional. Neither it nor successful syntax compilation establishes the requested unconditional theorem.

## What prevents a complete certificate

The required final theorem is

    ¬ AxiomSet.Consistent (AxiomSet.maximalist ∪ P.AtomicityT.schema)

with no selector, soundness, rigidity or non-theorem premise. No such complete certificate has been supplied.

The constructive side still needs an actual finite selector term and an interpretation showing that its exact split sentence is nonzero. The proof note's imported rigid complete atomless Boolean-algebra theorem has no checked local Lean counterpart. Neither do the HCode collapse/cardinality theorem, the hereditary-size constructible-level identification, or the finite constructible-order interpretation.

There is also a distinction that matters for formalization: the current BooleanValued.Dom source uses full ambient function spaces. The proof in L requires L-internal domains and a formal finite-proof absoluteness argument. An algebra complete and rigid inside L cannot simply be passed as an ambient complete and rigid algebra. The direct ambient Jech–Shelah construction is an alternative route; it would require its concrete forcing, coding and splitting-family proofs instead.

BooleanValued and BooleanValuedSoundness contain proof candidates, but no successful check was found. At the first dependency inspection their Mathlib import was absent. The serial compiler has since obtained the pinned source at /tmp/classicism-mathlib, and Mathlib/Order/CompleteBooleanAlgebra.lean is now present there. Its targeted cache/integration remains with the compiler owner. Source availability does not discharge the preceding mathematical obligations; the targeted SetTheory, Order and ModelTheory source search found no Jech–Shelah or constructible-universe implementation.

## Significance and validation

The proposed full result excludes unboxed Atomicity using one pure Max instance. The new certificate source isolates its elementary logical half from the substantial set-theoretic non-theorem argument. This is a technically meaningful reduction, but is not the full requested verification.

The new source batch passed repository validation: 132 principles, 447 results, 162 models — OK. That validation checks the bundle, not Lean proofs. No database verification status, generated Statements.lean, original proof or previously frozen Lean module was edited.

## Subsequent background-certificate request

The compiler has since checked BooleanValued, BooleanValuedSoundness and its
axiom-report driver successfully. See
[the background-certificate report](max-background-certificates.md) for the exact
run, axiom report, three additional frozen proof-source submissions, and the
remaining set-theoretic obligations. The earlier pending-compilation statement
above is historical. The complete inconsistency remains unverified.
