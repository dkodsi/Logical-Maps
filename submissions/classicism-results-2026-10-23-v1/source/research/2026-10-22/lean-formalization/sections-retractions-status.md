# Sections, retractions, and remaining Choice coverage

This is the expanded Choice and Sections/Retractions assignment over finitary C.
Current delivery evidence and residuals are in
[the contribution summary](sections-retractions-contributions.md) and
[the machine-readable update](verification-updates/choice_sections_retractions.json).
The frozen submission and residual text below is historical; the current
checkpoint supersedes it where exact passing certificates are listed.

## 23 October: ownership returned and locked verification active

The coordinator returned this family to its author for repair and verification.
The historical frozen handoff below is superseded by the live
[verification update](verification-updates/choice_sections_retractions.json).
Checks now use the globally locked runner; no raw Lean/Lake is run.

The principal full-schema equivalences now pass:
`FunctionalChoice <=> Actuality + RightSplitting` and
`Plenitude <=> Actuality + LeftSplitting`, with every admitted relational output
including t. Their certificate closure and final assemblies passed in
`checks/20261023T045645752380Z-c9bdf659.json`; the captured source hashes still
match the live closure when inspected. Earlier base/strong and Choice reverse
checks are listed in the live update.

The relational persistence/strong-section, pairing representation, idempotence
persistence and involutivity persistence schema assemblies also passed in
`checks/20261023T053829038089Z-f7ac4f52.json`. Their captured source closure
matches. Stable graph, modal witness, rigid-section and completely boxed
splitting certificates are listed in the contribution summary. All prepared
SectionsRetractions families now have passing checks. The final combined import
with all earlier Choice certificates also passed in
`checks/20261023T053945495916Z-2d579847.json`. All 120 captured source hashes matched live files on
final inspection, and all 19 principal theorem-axiom reports contain only
`propext` and `Quot.sound`. The lane is stopped; no further run is scheduled.

The hard stop is 05:57 UTC (01:57 New York) on 23 October. This lane will stop
by 05:55 UTC. The remaining window is for prepared leaf certificates and bounded
repairs, followed by exact handoff and residuals. No large new construction is
being started. All historical prepared/pending text below is superseded only
where the live update supplies a successful exact check.

The old pending ChoiceTransversal/CBC descriptions are historical. Their
complete gate/type/derivation logs passed in
`checks/20261023T032657816117Z.json`; they are not counted as freshly rerun.

## Historical READY FOR INTEGRATION — exact inverse and cancellation laws

These sources are frozen for the compiler owner, who may repair them:

| Module path relative to bundle root | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/SectionsRetractions.lean` | `fe23008ae2ab1cf2a47e0ce5d83009a5ea075730629aff1e098ac1289b5d86f3` |
| `topics/classicism/lean/Classicism/Results/Research/SectionsRetractionsCertificates.lean` | `d3ea605501e44956c89784321b26427791366aada4c010963149604f1a11d918` |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.SectionsRetractions --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.SectionsRetractionsCertificates --timeout 240
```

Prepared: FC gives sections; Plenitude gives retractions by the full
inverse-with-default construction; strong inverse equations iff literal
composition identities; strong inverses give necessary injectivity/surjectivity;
BF upgrades pointwise inverse equations; BF at the target gives persistence of
surjectivity; Epi tested at truth values iff necessary surjectivity; necessary
injectivity gives cancellation at each specified source type; actual injectivity
does so with BF at that source. All inverse codomains are relational. Cancellation
at every type is a metalinguistic family, not a quantified type variable in C.

These are prepared proof terms, not yet successful gate/type/object-language
certificates. No section/retraction characterization is assumed as a bridge.

## Historical residual list at the original handoff

Priority substantive families from the newly assigned sources:

1. Necessary-injection retraction construction and its per-map equivalence;
   C5/strong retractions/persistent injectivity, including the two low-type tests.
2. Surjectivity persistence -> BF_rel via the mask, and the idempotence/involution
   variants. Strong sections = ordinary sections + BF_rel, with exact instances.
3. Actuality plus the `tt -> t` section instance -> bivalent evaluator, using the
   escape map and the existing canonical evaluator certificate.
4. Pair-code decoding, the mirrored section construction, and the full
   `Actuality + sections -> FC` reverse direction, including individual inputs.
5. Mirrored injection coding and `Actuality + retractions -> Plenitude`.
6. Boxed FC/boxed Actuality/strong-sections classifications and mirrored fragments.
7. Representation of involutive graphs -> Plenitude; stable unique graph/BF,
   NUW/modal-Plenitude collapse, singleton/Hilbert/atomic choice normal forms,
   and bijection stability, where not already covered by another verified family.
8. Source-model separator verdicts in choice-uniformization §§13–14,16–17,20,22.
   These require model certificates; syntactic implications are not replacements.

The full family audit must still reconcile overlaps with the evaluator, atomic,
model, and hierarchy owners. No residual entry is counted as completed. Bare
RC -> TC and the source's explicitly unresolved bare splitting implications are
not being restarted as research. A complete theorem with an output of the form
`nu -> t` will require its list/vectorized certificate before it is reported as
covering every relational output type, including the nullary type `t`.

Validation log for this lane: `/tmp/classicism-sections-validation.log`.
