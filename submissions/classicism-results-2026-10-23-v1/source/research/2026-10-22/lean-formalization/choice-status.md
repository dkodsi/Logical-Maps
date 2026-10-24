# Choice formalization

## Certificate scope

The complete delivered Choice/SectionsRetractions aggregate passed in
[`20261023T053945495916Z-2d579847.json`](checks/20261023T053945495916Z-2d579847.json), including a fresh successful translation of
the sharp `RC_(t,t) + BC_tt -> Actuality`, its boxed counterpart, direct and
Actuality-mediated TC consequences, Countable/CBC results, and JoinTruth.
All 120 captured local source hashes match the live closure on final inspection.
The 19 principal aggregate axiom reports contain only `propext` and `Quot.sound`.
This supersedes historical pending integration statements below.

See [the delivery summary](sections-retractions-contributions.md) and
[the exact stopped-state update](verification-updates/choice_sections_retractions.json)
for the expanded splitting equivalences and remaining unimplemented work.
 Literature priority remains
unconfirmed, and the original RC-alone-to-TC problem remains unresolved here.

Expanded SectionsRetractions work and its explicit residual list are tracked in
[sections-retractions-status.md](sections-retractions-status.md). Earlier frozen
submissions below remain under certificate checkership.

## Current integration status

The certificate checker has successfully checked **ChoiceCompleteness**,
**ChoiceFixedPoint**, and **ChoiceActuality**, including their certificate
modules. I verified the saved manifests and independently recomputed their
dependency/source fingerprints against the current files; all three match.

The sharp finitary theorem `RC_(t,t) + BC_tt -> Actuality`, its correctly boxed
version, and `RC_(t,t) + BC_tt + RC_(sigma t,sigma) -> TC_sigma` now have successful
Classicism gate audits, relational-type audits, and translated object-language
derivations (reported in `C^-`). This is stronger evidence than ordinary Lean
compilation. No YAML status was changed, and literature priority remains open.

Evidence, relative to this directory:

- `checks/20261023T020457049464Z.json`: completeness certificate module exit 0.
- `checks/20261023T021005026513Z.json`: fixed-point certificate module exit 0.
- `checks/20261023T022130038754Z.json`: Actuality certificate module exit 0;
  that multi-family run's overall status is incomplete, but this module passed.
- `logs/runs/20261023T022130038754Z/Classicism_Results_Research_ChoiceActualityCertificates.log`
  records the audits and the generated derivations.

The certificate checker repaired the handed-off completeness and Actuality sources.
Their current source hashes when checked here are respectively
`0633f3eccc9508477291bb4a3486ce09cde3dc12c2c404424c5619d1bf752f57`
and `e63bba0e1e0a490bb8f1c4b3564e3041c3721e18a1eb223d5f4532b59370a3c9`.
The original handoff hashes and pending descriptions below are historical;
this current-status section supersedes them for those three completed families.
Later canonical-chain, CBC/CCC, and direct local Transversal modules are still
pending integration as separately indicated.

## READY FOR INTEGRATION — completeness lemmas

These sources are prepared C proofs and certificate drivers; certification requires a matching successful check.

| Module path relative to bundle root | Source SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ChoiceCompleteness.lean` | `9a257e097a30e4a78d2ee128e4dafcc2e48e118fee56cd0b268ddf0597b6d2c5` |
| `topics/classicism/lean/Classicism/Results/Research/ChoiceCompletenessCertificates.lean` | `354ad339a09e90a0b243b3695b0569ee97f99c202cb1ed31ef4a4a570e527cb6` |

Run these commands from the bundle root:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceCompleteness --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceCompletenessCertificates --timeout 180
```

The certificate module requests the Classicism gate, the relational-type audit,
and object-language derivations. It does not merely print ordinary Lean axioms.
Direct imports are existing `Principles.Choice`, `Principles.Lattice`, and the
existing check/type/schema tools. No new mathematical axiom, Mathlib import,
`sorry`, schema-level quantification over types, or language extension was added.

Prepared substantive results:

- Evaluation's right adjoint and preservation of represented algebraic joins.
- `BC_tt -> BC_t`, through constant properties.
- Closure of a haecceity join under a necessarily true relation on its seeds.
- `BC_tt`: a represented disjoint family's algebraic join is true iff an actual
  member is true. This uses no RC, BF, ND, or Plenitude.
- Actuality iff the meet of current truths is true; a false such meet is bottom.
- Failure of Actuality gives a nonzero false part of every nonzero proposition.

Source: `../followup/choice-completeness-actuality.md`, §§1–3, original research
(`misc`, unpaginated). Mathematical correctness remains subject to the audits and
independent checking. Repository validation passed after this edit batch:
132 principles, 447 results, 162 models. Validation is not Lean verification.

## READY FOR INTEGRATION — fixed-point lemma

Additional modules:

| Module path relative to bundle root | Source SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ChoiceFixedPoint.lean` | `b1260db321e998c8deb5acd1799301871c58448222e7d6fcacdffbba44acd883` |
| `topics/classicism/lean/Classicism/Results/Research/ChoiceFixedPointCertificates.lean` | `2040e89953d7c1338d8e38dbf20c53beb6cabcef1f10edca5b5f2f3dc4cbabcc` |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceFixedPoint --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceFixedPointCertificates --timeout 180
```

The source imports existing `Results.Records.Choice`. The graph theorem proves
the closed-domain Bourbaki–Witt argument via `Proofs.lewin_core`; its chain-code
selector is proved coextension invariant using entity-unique suprema. A bottom
equivalence class extends the domain order to the ambient type. This is an actual
preorder construction, not a quotient type. The operation corollary is restricted
to relational output types. Neither theorem assumes RC, TC, Plenitude, Zorn, or
an external ordinal. Gate/type and object-language derivations remain unchecked.

## READY FOR INTEGRATION — Actuality and Transversal Choice

Additional modules:

| Module path relative to bundle root | Source SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ChoiceActuality.lean` | `4faf427ba7a08f02528ad386832b52865f3e87e6e87507bbf6bc75795a995517` |
| `topics/classicism/lean/Classicism/Results/Research/ChoiceActualityCertificates.lean` | `9e4193ed4d140973dffe07dfba7d87c786d8776fd6edf6d640e37b08a731e209` |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceActuality --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceActualityCertificates --timeout 180
```

Imports: the two frozen choice modules above. The source contains complete
proposed proof terms for the guarded domain's chain completeness, its progressive
strict-extension operation, and both the guarded and sharp Actuality theorems.
No unproved research dependency appears as an extra hypothesis of these theorems.
They still await compilation, gate/type audit, and object-language certificates.

The sharp proof became shorter during translation: the `RC_(t,t)` selector is
indexed by the unique proposition which is the algebraic join of the current
antichain. See [the new mathematical refinement](choice-join-indexed-refinement.md).
This supplies the same safe selector used by the guarded operation and avoids a
second canonical-chain/disjoint-refinement formalization. It is an ordinary
finitary C argument, with no language extension.

Exact prepared main conclusions:

- `RC_(tt,t) + BC_tt -> Actuality` (guarded route).
- `RC_(t,t) + BC_tt -> Actuality` (sharp route).
- The boxed version with both premises boxed.
- At each admitted `sigma`, `RC_(t,t) + BC_tt + RC_(sigma t,sigma) -> TC_sigma`.
  Hence all-type RC with BC only at `tt` suffices for all-type TC.

The original RC alone implying TC remains unresolved. Literature priority also
remains unconfirmed: the proof is a proposed new result, and the public
Classicism drafts searched contain no proof of this implication. No formalization
status establishes priority.

## Continuing independently

The remaining certificate targets are the canonical-chain, CBC/CCC, direct type-local TC, and join-truth results.

## READY FOR INTEGRATION — canonical chains without completeness

| Module path relative to bundle root | Source SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ChoiceChains.lean` | `7ba77fa3d627a892b06e287b9ff936bc871ae0480b21d9b809e65911de6be61c` |
| `topics/classicism/lean/Classicism/Results/Research/ChoiceChainsCertificates.lean` | `556df3884139d4630e9ce872fc5ad1f8f5626c0fdd083882df1655e4d34ed729` |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceChains --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceChainsCertificates --timeout 180
```

The new foundation forms the
represented, well-ordered union of all conforming chains without a completeness
premise, proves the successor-bound lemma, and proves that a supremum of this
single union yields a fixed point. This is substantive input for the CBC/CCC
argument, not yet that upgrade. It imports only the frozen fixed-point module
and the existing Lewin lemmas. All three checks remain pending.

## READY FOR INTEGRATION — CBC + CCC upgrade

| Module path relative to bundle root | Source SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ChoiceBoolean.lean` | `ee63985e7c0c60bd15a9c5e42a74cf4b18c77399cf0fd5fff3bdf3743a089d56` |
| `topics/classicism/lean/Classicism/Results/Research/ChoiceCountable.lean` | `a89c78f4c95df600629e04a7a8332c161a2cc06705865d0e25b53a99788d4a63` |
| `topics/classicism/lean/Classicism/Results/Research/ChoiceCountableCertificates.lean` | `3e9b44139e95b63cd6a73727159d6a67f14a6f299053110713a885806162e279` |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceCountable --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceCountableCertificates --timeout 180
```

The main prepared theorem is
the exact type-local `RC_(tau,tau) + CBC_(kappa,tau) + CCC_(kappa,tau) -> BC_tau`,
using the library's Frege-label definition of countability. The proof constructs
the represented canonical chain before invoking completeness, transfers labels
from its nonzero disjoint increments, and then invokes CBC only for that chain.
It includes a reusable countability pullback through a represented relation with
disjoint fibers. No external countability, arithmetic recursion, or enumeration
was substituted. The generic Boolean order lemmas use the existing
`Rel`/`Order`/`Pointwise` interfaces at every relational type.

No extra unproved research hypothesis occurs in the main theorem. Compilation,
gate/type audit, and object-language certification are pending; this is still a
prepared proof, not a completed verification claim.

## READY FOR INTEGRATION — direct local Transversal route

| Module path relative to bundle root | Source SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ChoiceTransversal.lean` | `61750169b60a567a55745cc597dcb51c6e706d2678c8783df938042d45a40cae` |
| `topics/classicism/lean/Classicism/Results/Research/ChoiceTransversalCertificates.lean` | `4802aa8affb8be3cc51ead72c5eb6d859a0659e2b96d880aad36f8fd31394a13` |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceTransversal --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceTransversalCertificates --timeout 180
```

Exact prepared conclusions:

- `RC_(sigma t,sigma t) + BC_(sigma t) -> TC_sigma`.
- `RC_(sigma t,sigma t) + CBC_(kappa,sigma t) + CCC_(kappa,sigma t) -> TC_sigma`.

The first argument uses the algebraic poset of necessarily partial representative
properties, with quantifiers outside the boxes. Each actual nonfull member has
a strict extension using an internal two-direction guard. RC chooses an actual
functional graph of extensions; the graph fixed-point theorem yields a full
representative property. This route has no Actuality or `BC_tt` premise and does
not use the Actuality theorem. The given equivalence relation is only actually
an equivalence relation. The second theorem combines this route with the exact
CBC/CCC completeness upgrade. Both await compiler integration and certificates.

## READY FOR INTEGRATION — represented joins and truth

| Module path relative to bundle root | Source SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ChoiceJoinTruth.lean` | `ffd3997823beda2979bb4403c1f20703f2f81b08cb0a0c3608e8bf6d57da3887` |
| `topics/classicism/lean/Classicism/Results/Research/ChoiceJoinTruthCertificates.lean` | `75b82c016a1f7cf7ab67b524b7087bfe72f529f78510bd2700ccef06d8c100f0` |

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceJoinTruth --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ChoiceJoinTruthCertificates --timeout 180
```

They sharpen the saved join
descendant: Actuality alone makes every existing represented algebraic join
reflect current truth. No general completeness is required when that particular
join is given. Conversely, failure of Actuality already makes `True` the algebraic
join of all current falsehoods in bare C. Thus Actuality is equivalent to this
truth-reflection property for all represented joins that exist.

Evaluation then gives current coextension of a relation's algebraic join with
its material union, under Actuality or the now-certified sharp RC + BC premises.
The proof does not claim equality of coextensive relation entities, BF, or future
preservation of a current supremum. These new descendants await checking.

## Final worker check


The frozen research notes, existing proof modules, YAML statuses, and generated
`Statements.lean` have not been changed. No priority claim follows from this work.
