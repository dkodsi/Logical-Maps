# Finite Choice formalization status

The three modules below are source submissions. Certification requires a matching successful check.

## Submitted modules

| Module | Source path | Handoff SHA-256 |
|---|---|---|
| `Classicism.ChoiceHierarchy` | `topics/classicism/lean/Classicism/ChoiceHierarchy.lean` | `2cbe5b25ec438b2f10811e2d66852fc13233001c790d1a118b09e753559f06f0` |
| `Classicism.Syntax.ChoiceHierarchyTypes` | `topics/classicism/lean/Classicism/Syntax/ChoiceHierarchyTypes.lean` | `8d12b0c2e6ae16ec0be6602aa1dbf28306a41cb1a45098d00fa2f884dafd5742` |
| `Classicism.Syntax.FiniteChoiceBasis` | `topics/classicism/lean/Classicism/Syntax/FiniteChoiceBasis.lean` | `c96cb4ea2a4fb24f4493682835df7cedbf6d4acb12709960adedc03c8fc65b99` |

Run these commands serially, from the bundle root, **only in the sole build-owner task**:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Syntax.ChoiceHierarchyTypes --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Syntax.FiniteChoiceBasis --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.ChoiceHierarchy --timeout 240
```

If the bounded runner reports unavailable dependencies, preserve its limitation; do not turn it into an axiom or a certificate. The dependency closure and compiler diagnostics should be retained by the integration owner. Repository validation is separate from all three checks.

## Exact scope

- `Classicism.ChoiceHierarchy`: 21 fixed-type shallow theorems, with explicit gate checks, a type audit, and an object-language derivation audit. Selector equivalence with FC at `(tau t,tau)`; arbitrary-input FC from a selector; boxed versions obtained by necessitating discharged C theorems; retraction transfers; haecceity input transfer including `e`; pure retractions at `t` and predicate types; adjacent predicate-selector descent; the `et`-to-`t` retraction (with individual nonemptiness); diagonal-to-selector reductions at `t` and predicate types. The general retraction/decoder lemmas retain their hypotheses. No output operation has individual type.
- `ChoiceHierarchyTypes`: metalogical recursion on the actual `Ty`/`RTy` syntax. Admitted, closed tower stages `A_0=et`, `A_(n+1)=A_n t`, their orders, the research embedding-budget function, and finite bounds on lists of elaborated types. This is not a proof that the budget is realized by injections, nor that a model preserves a fragment.
- `FiniteChoiceBasis`: a direct induction on the actual C derivation relation extracting finitely many optional axioms, with Logical Equivalence premises confined to the logical part. It combines supports for finitely many conclusions, proves the conditional nonfinite-basis reduction from a finite-fragment gap, and proves that any theorem of an increasing union appears at one stage. These are metalogical theorems about C, not new object-language type or arithmetic quantifiers.

## Coverage and remaining mathematical dependencies

Research sources: `research/2026-10-22/followup/finite-functional-choice.md` §§4–5, 7–10 and `type-t-uniformization.md` §§3–6. Originals and frozen research were preserved; database YAML and generated `Statements.lean` were not edited.

The modules do **not** claim the full strict selector hierarchy, full cofinality with all-type boxed FC, or unconditional nonfinite axiomatizability. The unformalized dependencies include the recursive injection/graph coding under boxed Plenitude, the complete schema-level composition at every closed relational output, and the symmetric ZF model constructions/preservation and interpretation into general C models. The finite-basis theorem visibly assumes the finite-fragment gap and does not conceal a model-existence axiom.

For type-t uniformization, the shallow selector/FC equivalence is covered. The full-internal Gallin dictionary, determinacy model, the sorted-pair counterexample, and the proposed full-automorphism Cohen model are not formalized here. The newest Cohen localization/embedding-extension argument remains a proposed research proof awaiting independent mathematical review. No symmetric-model existence, DC preservation, forcing quotient theorem, or uniformization statement was added as an axiom. An ordinary Lean theorem using full ambient function types would not certify the internal general-model claim.

No language extension is used in these modules. In particular the finite-support and finite-stage results remain finitary; permission to consider infinitary conjunctions does not alter their statements.

## Validation and continuation

All edit batches were checked with `python3 scripts/pmap.py validate`; the current log is `/tmp/choice-formalization-validation.log`. This validates repository structure, not Lean proofs. Compilation, gate/type success and actual `.derivable` artifacts remain pending until the build owner records results.

The author may continue in a separate `ChoiceHierarchyEncoding` module. That prospective file is not part of this handoff unless separately listed below.


## Additional handoff: coding and schema composition

Status: **READY FOR INTEGRATION**. These two additional modules are now frozen and transferred to the sole integration owner. This supersedes the prospective-file sentence above. They have not been compiled by this author.

| Module | Source path | Handoff SHA-256 |
|---|---|---|
| `Classicism.ChoiceHierarchyEncoding` | `topics/classicism/lean/Classicism/ChoiceHierarchyEncoding.lean` | `f397fed19a8a1530033b0321bbc26ccd5e9634ffbf3e9c8aaf11e6c900df46ab` |
| `Classicism.Results.ChoiceHierarchySchemas` | `topics/classicism/lean/Classicism/Results/ChoiceHierarchySchemas.lean` | `20b5e4e4e7fd451a89132d0cff3649b2a158af0aaf8afcdc03006852b41579fe` |

Run serially, after repairing/checking the first handoff's dependencies:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.ChoiceHierarchyEncoding --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.ChoiceHierarchySchemas --timeout 240
```

`ChoiceHierarchyEncoding` submits seven fixed-type C proofs with explicit gate, type and derivation commands: Kuratowski-pair injectivity without Functionality; graph-code injectivity with exactly the stated Functionality premise; total single-valued inverse relations; retractions supplied by Plenitude; and selector transfer through an injection with that Plenitude premise. The graph target uses three predicate levels. No recursive embedding theorem is claimed by this file.

`ChoiceHierarchySchemas` submits five boxed wrappers and schema/rule certificates. Its metalogical part uses actual quoted sentences to define the single-axiom stages, prove adjacent and iterated entailment, identify the exact FC instance supplying each stage, and show a stage supplies arbitrary closed input types at its own output. It proves every theorem of the union of selector stages already appears at a stage, by the actual finite-support theorem. This is cofinality in that union, **not** a proof that it exhausts all-type FC or that the inclusions are strict.

Integration detail observed read-only: the first check of `Classicism.ChoiceHierarchy` reported beta-redex rewrite/elaboration failures and current-module audit discovery failures. Its ownership is already with the core task, which may repair it. No source `sorry` was introduced; `sorryAx` reports in that failed run are elaborator recovery, not successful certificates. The new encoding module uses explicit declaration lists instead of current-module audit discovery. The status of all compiled dependencies must be taken from the core task's final fingerprinted logs, not from this author-side handoff.

## Deliberately unfilled obligations

The remaining cofinality obligation is an actual derivation, uniformly over closed types, that the recursive budget yields injections and that boxed selector stages supply the boxed Plenitude/Functionality premises used in that construction. The submitted pair, graph, inverse and selector lemmas expose those components; they do not assume the missing composition. Strictness, the various incomparability spectra and nonfinite-basis instantiations still require general C models built from the symmetric ZF constructions. No available local module was identified that implements the required forcing/symmetric-model/preservation machinery. The type-t full-automorphism argument additionally remains proposed mathematics, so formalization cannot soundly treat its localization lemma as established.

No further author edits to any of these five handed-off modules are authorized by this handoff; the integration owner may repair them. Repository validation passed after the source batches. Validation of this status update is recorded in the same compact log.


## Recursive realization and full positive cofinality handoff

Status: **READY FOR INTEGRATION**. These three fresh modules are now frozen and transferred to the sole build owner. They are proof submissions pending compilation/certification. They replace several earlier *unfilled positive-construction* obligations with explicit proofs; they do not replace the forcing/model gaps or assert strictness.

| Module | Source path | Handoff SHA-256 |
|---|---|---|
| `Classicism.ChoiceHierarchyPlenitude` | `topics/classicism/lean/Classicism/ChoiceHierarchyPlenitude.lean` | `137510bca1b6390393920fba9407f96d3c9eadaf580aef50fb3e824aa14fb30b` |
| `Classicism.ChoiceHierarchyRealizationSteps` | `topics/classicism/lean/Classicism/ChoiceHierarchyRealizationSteps.lean` | `f5bdc620a2af8d9fe08522a72e2c07cdfe7b1b981dada52b051b75591c6cf46a` |
| `Classicism.Results.ChoiceHierarchyRealization` | `topics/classicism/lean/Classicism/Results/ChoiceHierarchyRealization.lean` | `b4d2a2ab5d085a0be50aefd39efae26a63862213769b7073baf9435684e19132` |

Exact serial commands for the build owner, from the bundle root:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.ChoiceHierarchyPlenitude --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.ChoiceHierarchyRealizationSteps --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.ChoiceHierarchyRealization --timeout 240
```

The proof chain is substantive, rather than a new gap hypothesis:

1. `ChoiceHierarchyPlenitude` derives all boxed Plenitude instances from the exact single instance at `(t,t)`. It uses the existing C proofs of ND, Actuality, rigid comprehension and weak rigid comprehension, plus the existing vectorization theorem to cover arbitrary finite output arity (including zero). It also derives boxed Functionality and shows every selector stage supplies that base. The two vectorized rules are explicit compiler checkpoints; no vectorization claim is assumed as an axiom.
2. `ChoiceHierarchyRealizationSteps` constructs existential injections at `e` and `t`, raises targets by haecceities, and constructs the three-level graph injection. The Functionality and Plenitude dependencies are explicit and boxed in the exact steps used by the recursive proof. Existential witnesses remain inside boxes; no single witness across worlds is claimed.
3. `ChoiceHierarchyRealization` performs mutual structural recursion on the actual closed `Ty`/`RTy` codes, proving the computed embedding budget is realized under the single boxed Plenitude base. It derives the selector at every closed relational output from its specified stage, obtains every fixed boxed FC instance there, and proves `fullChoice_theorem_iff_stage` using the actual finitary derivation-support theorem. This is the full positive cofinality statement, pending the integrator's successful check; it has no assumed injection-realization, cofinality or separation-model premise.

These results do not certify strictness, independence, nonfinite axiomatizability, or the proposed type-t symmetric construction. The source mathematical construction remains qualified as before. No Lean/Lake command or dependency download was run in this author task. Every new source edit batch passed repository validation; that is not Lean certification. Integration may repair the frozen modules, and this author will not edit them without returned ownership.


## Diagonal and actual retraction handoff

Status: **READY FOR INTEGRATION**. These final two fresh modules are frozen and transferred to the sole integrator. They remain submissions until checked against the exact dependency sources. No author-side compilation was performed.

| Module | Source path | Handoff SHA-256 |
|---|---|---|
| `Classicism.Results.ChoiceHierarchyDiagonal` | `topics/classicism/lean/Classicism/Results/ChoiceHierarchyDiagonal.lean` | `df22b2b6267d6cde808bc3f4c042ee77b73d473e09c7ce45f2d8cac49affb08d` |
| `Classicism.ChoiceHierarchyRetractions` | `topics/classicism/lean/Classicism/ChoiceHierarchyRetractions.lean` | `a57529ebf59a608ba4885db41aebcd7793380cf89d1e96f45687613e36229a7b` |

Exact serial checks, after the preceding recursive-realization modules:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.ChoiceHierarchyDiagonal --timeout 240
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.ChoiceHierarchyRetractions --timeout 240
```

`ChoiceHierarchyDiagonal` derives the all-relational-type diagonal schema from full boxed FC and the converse, through the actual cofinality proof. It also gives the ascending diagonal stages and proves every full-FC theorem already follows from one finite diagonal stage. The `D_n`/`T_n` entailments have their correct directions: `T_n` entails `D_n`, and `D_(n+1)` entails `T_n`. Strictness is not asserted.

`ChoiceHierarchyRetractions` realizes an actual existential retraction at each recursive budget under the boxed Plenitude base. It separately proves the pure haecceity-decoder theorem at every closed relational type using the predicate construction and vectorization, including the empty argument list for `t`. This gives C theorems for the adjacent haecceity retraction and the exact arbitrary-relational-type diagonal-to-selector reduction. All inverse outputs are relational; the budget inverse is supplied by Plenitude and is not described as a pure inverse term. Boxed existential witnesses remain inside the box.

## Current positive coverage and boundary

The ten submitted modules now contain an explicit proposed Lean proof chain for the completed positive hierarchy work: admitted closed tower syntax; finite derivation support; exact selector/FC reductions; pair and graph coding; the exact scalar boxed-Plenitude base and its all-arity consequences; actual recursive injection and inverse realization; full selector-stage cofinality; and diagonal-schema/stage cofinality. This is source-level coverage, **not a count of successful certificates**. The sole integrator's compiler results, gate/type checks, translated C proofs and source fingerprints determine which have passed.

The remaining strictness and nonfinite-basis applications require formal symmetric forcing/general-model infrastructure, not another propositional wrapper. The proposed full-automorphism type-t argument additionally needs independent mathematical review. Those are unchanged gaps, and no new assumption conceals them. No infinitary language extension was used in this lane. Originals, frozen research, YAML verification statuses and generated statements were preserved. Validation was run after each edit batch; certificate checkership remains with the designated task.

## Negative hierarchy audit and concrete fresh-column handoff

The significance-focused continuation is recorded in [finite-choice-negative-audit.md](finite-choice-negative-audit.md). It audits the finite-domain and bounded-order preservation, the fresh-column selector obstruction, full internal typed closure, and first-order ground extraction without a countable-transitive-model assumption. Those ordinary ZFC arguments pass this rereading; this is not independent human checking or an end-to-end Lean certificate. The report identifies the unavailable symmetric-forcing and extraction infrastructure, a dependency roadmap, and the first adjacent selector cutoff as the next substantive semantic target. No new finite-fragment-gap wrapper was introduced.

**READY FOR INTEGRATION; frozen:** `topics/classicism/lean/Classicism/Models/ChoiceFreshColumns.lean`, SHA-256 `1ab33f4ad5c9e969a5a157a0b903b6a3b633f533addd31432798ce8173ae5a0e`.

This Init-only module gives an explicit fresh-column common extension (`fresh_amalgam`, with exact union-of-domains theorem) and the unconditional ordinary metatheorem `no_finitely_supported_selector` on natural-number atoms. It does not assert a C-model, a forcing extension, or the nonfinite-basis theorem. The forcing-name/symmetric-model bridge is deliberately absent rather than assumed. No `sorry` or new mathematical axiom was added. Only the build owner should compile or repair the frozen file:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Models.ChoiceFreshColumns --timeout 120
```

No author-side Lean/Lake check or dependency installation was run. Repository validation passed after the new source and audit batches; integration must record the actual compiler outcome. Earlier positive-source handoffs remain frozen. Their pending/successful status must be read from the integrator's fingerprinted checks; this new handoff does not promote the full positive or negative hierarchy to verified.
