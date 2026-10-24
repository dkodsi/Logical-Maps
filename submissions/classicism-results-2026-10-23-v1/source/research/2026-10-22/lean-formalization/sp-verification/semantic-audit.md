# SP auxiliary modules: mathematical-scope audit

Date: 23 October 2026. Reviewer: OpenAI Codex, task `/root/sp_semantic_audit`.

This is an independent AI review of the mathematical statements and their scope. It is not human checking, a `checked_by` assertion, or a Lean verification certificate. The reviewer did not compile, install dependencies, or edit the three modules. Compiler outcomes belong to the separate check manifests. The only authorized edit in this review is this report.

## Finding

No blocking mathematical error or concealed premise strengthening was found in the exported statements of `StrongPossibilityConsequencesAlgebra.lean`, `StrongPossibilityConsequencesComputability.lean`, and `StrongPossibilityConsequencesInfinitaryNumerals.lean`. Their mathematical scopes are narrower than the full research families, and their comments preserve that distinction. No theorem-statement change is recommended to obtain compilation.

The review used the fixed-framework instructions in `topics/classicism/AGENTS.md`, `topic.yaml`, and `background.md`, the pure/signature Strong Possibility records, and the Lean proof-policy documentation. These three files state ordinary metatheorems or semantic results, not shallow object-language C theorems. Ordinary Lean equality and classical metatheory are legitimate in that role; their successful elaboration would not certify a missing C derivation or construct a C model.

## Algebra

The single and relative kernel lemmas establish the stated bottom, downward, join, and modal closure properties under their explicitly supplied assumptions. No blanket filter or modal-algebra structure is silently inferred.

`quotient_no_new_fixed_below` assumes a surjective map preserving meet, complement, and the displayed modal operator, together with the exact zero-kernel characterization. From a fixed point `r` below the image of `g`, the proof lifts `r` to `p`, obtains a kernel witness for `d p ∧ ¬g`, uses extensivity to show `d p ∧ k ∧ ¬g = 0`, and concludes that `p` is in the kernel. The conclusion follows under these assumptions. The theorem does not construct the map, show that the quotient is nontrivial, prove that the kernel is a full many-sorted term congruence, or supply a truth/Henkin interpretation. A trivial quotient is permitted by the statement.

`numerical_return_is_inverse` and `numericalEquiv` assume preservation of both number predicates, an actual retraction on the whole source carrier, and numerical injectivity of the return map. They establish an inverse on the numerical subtypes. They do not prove preservation of addition or multiplication, so the exported equivalence alone is not an arithmetic-structure isomorphism. `numerical_named_of_profiles` is correctly described as the final injectivity step: numeral compatibility, numerical injectivity, and coverage of numerical images by target numerals remain inputs.

Residual bridges: construct the relevant quotient and verify its exact kernel; prove its genuine C/Henkin interpretation; derive numerical preservation/injectivity and arithmetic-operation preservation from the actual C term maps. The distinction between algebraic quotients and genuine models agrees with `notes/sp-algebraic-findings-20261022.md` §§2–3 and `notes/sp-henkin-minimal-20261022.md` §§16–20. None of these lemmas settles SP consistency.

## Computability

The four theorems use actual `Nat.Partrec.Code.eval` computations. The separator proof constructs, using the recursion theorem, a program returning one when its own code belongs to the alleged separator and zero otherwise. Both membership cases contradict the relevant separator condition. The prediction theorem likewise constructs a program returning the computable prediction of its own code; the diagonal-avoider conclusion follows immediately.

These are unconditional, unrelativized program-level results. They do not establish a lower bound for a C theory or model presentation without an effective interpretation/reduction. In particular, the implementation uses `eval c 0`, while the source degree arguments are expressed through numbered diagonal computations `phi_e(e)`. The effective recoding bridge has not been supplied here. Neither has the uniform oracle-relative compiler, a PA-degree characterization, a model-code reconstruction, or an arithmetical-hierarchy completeness reduction.

This is consistent with the boundaries in `notes/positive-effective.md` §§13–17, especially §§16.1–16.6, `notes/max-degree.md` §§8–10, and `notes/strong-possibility-degree.md` §§5–6. Those broader arguments need the stated consistency, arithmetic, trace-coding, and model-code assumptions; this small module does not discharge them.

## Infinitary numerals

`Frame.Number` is defined by zero/successor induction over the frame's admitted predicate domain. The domain is not assumed to contain every external subset. `InfFormula.countableOr` is an explicitly new syntax constructor with an external natural-number index and ordinary pointwise existential semantics. The `Comprehension` hypothesis supplies an admitted predicate with the corresponding beta law, rather than merely identifying an external subset.

`number_iff_numeral` uses the specific range formula `bigvee_n (x = numeral n)` to obtain an admitted zero-containing, successor-closed predicate. This proves numeral exhaustion without assuming exhaustion. The reverse inclusion uses external finite induction. The separate `PeanoOnNumbers` hypotheses are used to prove numeral injectivity and unique naming; they are not smuggled into the exhaustion argument. The final exclusion theorem concerns this enlarged comprehension resource at a local frame.

The blanket abstraction map in `Comprehension` is stronger than the single range predicate used in the proof, but it matches the advertised enlarged syntax; no theorem claims that ordinary finitary C supplies it. The fragment has no Sum/Prod interpretation or modal-world relation. Residual bridges are extraction from the actual Frege/action-model semantics, correctness of Sum/Prod on numerals, the finitary independent arithmetic branches, and the old-Max modal argument. This matches `notes/infinitary-standard-numerals-20261022.md` §§1–3. Neither incompatibility of old Max with this enrichment nor inconsistency of finitary C/Max/SP is proved in this module.

## Validation

Ran `python3 scripts/pmap.py validate` after writing this report. Result: `classicism: 132 principles, 447 results, 162 models — OK`. This checks repository records and is not a Lean or mathematical proof check.

## Addendum: MaxDiagram and Schemas

Also reviewed `StrongPossibilityConsequencesMaxDiagram.lean` and `StrongPossibilityConsequencesSchemas.lean` after the coordinator reported successful compiler checks. This addendum is a statement/definition audit, not an independent compiler run. No blocking scope error was found.

**MaxDiagram.** `identity_iff` explicitly assumes consistency of `C.axioms ∪ Ax` and that `Ax` entails the Max axioms for the same `Sig`. Its compared identities are object-closed typed terms whose whole equality formula passes `closedTypes`; this excludes the metalanguage's free type-variable instances. A non-C identity would meet the original Max distinctness condition, so the alleged identity proof contradicts the explicitly assumed consistency. The resulting equality of distinctness predicates preserves this restriction. The re-maximalization results prove consequence and consistency preservation; they do not prove that any initial Max extension exists. Finite Boolean combinations are handled by actual derivation constructors, and the exact theoremhood equivalence retains consistency. The separate `decides` theorem needs no consistency premise because it only constructs the appropriate derivation from the metalogical C-theoremhood truth table; it does not assert that this table is computable. Classical contradiction and extensional equality of axiom predicates are used in ordinary metalogic, not as additional object-language rules.

**Schemas.** `reflectingMaxConsistent` is exactly the set of closed-type, Max-consistent sentences supplied with an actual `C.Theorem (D p → p)` certificate. It is not defined as all syntactically universal formulas, and this file alone does not establish that larger grammatical characterization. The reverse entailment correctly takes a licensed SP instance `D p`, transfers consistency from `Max+p` to `Max+D p` using the C derivation of `p→D p`, and uses the actual idempotence certificate `D D p→D p`. No optional hypothesis is necessitated.

Both entailments conclude the library's `Theorem`, defined as an actual `Derivable` judgment with an empty hypothesis context; they are not merely implications between shallow Lean propositions. The repaired renaming/substitution conversion in `c_diaNe_idempotent` transports a generated derivation across equality of syntactic terms. It introduces no new logical premise.

`pureSP_monism` and `pureSP_not_atLeastTwo` retain `Consistent (Max + monism)` at `Signature.pure`. Here monism is `∀x:e ∀y:e, x=y`; with C's individual-existence axiom this is the intended E1 condition. The module neither supplies its model-consistency proof nor proves SP consistent. At arbitrary `Sig`, the schema equivalence keeps both Max and SP relative to that same signature. Pure certificates are transported only for the fixed C implication steps; no conservativity or implication from pure SP to signature SP is inferred. The Schemas header's pending-compilation sentence is stale according to the coordinator's successful-check report, but its mathematical limitations remain accurate.

Definitions checked directly: `Syntax/SentenceSchemas.lean` (`distinctness`, `max`, `maximalist`), `Syntax/StrongPossibility.lean`, `Syntax/Entailment.lean` (`Entails`, `Consistent`, and derivation cut), `Syntax/Pure.lean`, and the generated-certificate source theorems in the C and Stability modules. No source module was edited. Repository validation was repeated after this addendum and passed with the same record counts.
