# Arithmetic transfer formalization status

> Current delivery and verification status: [contribution summary](arithmetic-contribution-summary.md),
> [verification ledger](verification-updates/infinity_arithmetic_profiles.json), and
> [exact principal statements](arithmetic-principal-statements.json). Earlier frozen/sole-integrator
> language and direct-Lake commands below are historical. The current verification protocol
> and shared locked runner govern repairs and checks. A saved draft is not a passing certificate.


## READY FOR INTEGRATION — Frege foundation

Both files below are frozen. Ownership passes to the designated sole serial compiler/integrator, who may repair them. The author has run no Lean/Lake command, installed nothing, and downloaded nothing. This is a saved proof submission; compilation, gate/type audits and object-language translation remain unchecked.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FregeInfinity.lean` | `b0007e4dad8fdcf52a01e8ef77bbce988fa3f6aa06570c89c4f2397ea138c759` |
| `topics/classicism/lean/Classicism/Results/Research/FregeInfinityCertificates.lean` | `02f55108d0ae28c0e3cb7489dc9dc590525ff7c8b38637facc4f8100a65af46d` |

Scope: 18 shallow C theorems, including extension invariance, fresh-point realization, quantified Infinity realizing every internal number, internal cases and persistence, Swap, the full boxed Exclusivity alternative, literal identity from a common instance, numerical extensionality under Infinity, and successor injectivity. No Choice, BF, ND, individual-valued operation, or external-standardness premise. Sources are stated in the module. Original Cardinality.lean, records, Statements.lean and frozen research notes are untouched.

Exact serial check from the bundle root (for compiler owner only):

```sh
PATH=/tmp/classicism-lean-toolchain/lean-4.33.1-darwin_aarch64/bin:$PATH /tmp/classicism-lean-toolchain/lean-4.33.1-darwin_aarch64/bin/lake -d topics/classicism/lean build Classicism.Results.Research.FregeInfinityCertificates
```

The driver performs the Classicism gate audit, relational-type audit and genuine object-language derivation of every theorem, then prints axioms of the principal derivations. A successful shallow compile alone is insufficient. `#classicism_derive_audit` must report every theorem derived; no `sorryAx` is acceptable. Compiler/translator diagnostics, if any, belong to integration status rather than a verification claim here.

Repository validation after the proof batch passed: 132 principles, 447 results, 162 models. Validation is not Lean certification.

## Continuing separately

CoreNumberIsomorphism will consume this foundation. The world author owns constructing supported-core predicates/operations. Any unprovided core induction or representation premise will remain explicit, not be asserted as an axiom. GeneratedAlgebraTransfer will retain exact map/commutation hypotheses and distinguish object-language results from external metatheory.

## READY FOR INTEGRATION — core-number arithmetic kernel

The following two files are now frozen and transferred to the same serial integrator. They have not been compiled by this author.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/CoreNumberIsomorphism.lean` | `8dab1e18b29eeafd81e644b0b94d07cb04e21918d0b08eb3863eb2208aefe27d` |
| `topics/classicism/lean/Classicism/Results/Research/CoreNumberIsomorphismCertificates.lean` | `6dfb81fa07aa82610da79b597faec08bb4455bf12f0d9e1ea50bf24de0a9d079` |

Eight shallow C theorems prove literal number injectivity, reflected identity, exact quantified-Infinity equivalence, a total unique inverse graph, current subset push/pull round trips and reflected successor. The substantive injectivity proof uses the actual fresh-point/realization/exclusivity foundation above. No external numerical standardness or selection operation is assumed.

**Exact remaining interpretation dependency:** the world/core owner must construct the supplied property field P and number map q; prove `PropertyFieldCovers P`, `NumberMapTests P q`, forward numberhood, surjectivity onto its actual target `K`, target-universe membership/truth, and the number-restricted successor equation. Target-core admission of the pushed predicates, and identification of the target's addition/multiplication graphs, are also outstanding. The module proves the conditional arithmetic kernel, not the full Actuality/Gallin interpretation. The hypotheses are ordinary formula premises, never new axioms.

Serial check, from bundle root, after Frege foundation:

```sh
PATH=/tmp/classicism-lean-toolchain/lean-4.33.1-darwin_aarch64/bin:$PATH /tmp/classicism-lean-toolchain/lean-4.33.1-darwin_aarch64/bin/lake -d topics/classicism/lean build Classicism.Results.Research.CoreNumberIsomorphismCertificates
```

The driver runs both audits and derives every theorem into the object calculus; key `.derivable` axiom reports are included. No database verification status has changed.

## READY FOR INTEGRATION — generated algebra, one-sort C instance

These two additional files are frozen. Nineteen shallow theorems are submitted; the author has not compiled them.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/GeneratedAlgebraTransfer.lean` | `9611715d82e682bd3c52822fd195644151859ea4ad8369f432ca2f94845d322d` |
| `topics/classicism/lean/Classicism/Results/Research/GeneratedAlgebraTransferCertificates.lean` | `15777964d1eae3e2ee9072582234cf5b151645ff637af8f1f6793b4a48753011` |

Exact proved scope of the draft: one relational source sort and one relational target sort, one generator, one unary and one binary constructor. The module proves impredicative carrier persistence, C5 rigidity, forward transfer with guarded commutation, represented-image persistence/support/rigidity, surjectivity onto supported rigid generation, a left inverse under reverse commutation, and the injectivity/right-inverse consequences. No freeness, external-standardness or Choice is assumed. Image persistence itself uses no BF: a single positive existential witness persists using NI. C5 supplies its inextensibility.

**Not yet formalized:** arbitrary finite lists of sorts/constructors and their object-language encoding. This concrete C instance does not claim that generality. No map-existence theorem is asserted.

Serial check (bundle root, compiler owner only):

```sh
PATH=/tmp/classicism-lean-toolchain/lean-4.33.1-darwin_aarch64/bin:$PATH /tmp/classicism-lean-toolchain/lean-4.33.1-darwin_aarch64/bin/lake -d topics/classicism/lean build Classicism.Results.Research.GeneratedAlgebraTransferCertificates
```

The existing integration wrapper is an alternative that records fingerprints and keeps checks serial:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.GeneratedAlgebraTransfer --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.GeneratedAlgebraTransferCertificates --timeout 180
```

The all-theorems certificate drivers may be split into per-theorem drivers by the integrator if translation memory/time warrants; no author is running checks in parallel. Repository validation passed after the source batch.

## Next independent module

The world lane has now frozen ActualityCore.lean. Its localization and Domain/Cut lemmas suffice to discharge the concrete Actuality-slice property coverage/application interface. A new ActualityCoreNumbers module will own that arithmetic instantiation; frozen shared modules will remain untouched.

## READY FOR INTEGRATION — concrete Actuality-core numbers

These two files are frozen and transferred to the designated serial integrator. The author has run no compiler. All statements remain unverified proof drafts until the separate gate, type and translation checks succeed.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreNumbers.lean` | `ee9e0968e1145e104def78fa31f449ee4b3ac54a0a5b227bc2d65d061e1a916f` |
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreNumbersCertificates.lean` | `e7780286bad74294159b6a436dbfa8b64a9dff8f9bfc72e657112272119648e6` |

The draft contains 23 shallow C theorems. It constructs the property/cardinality fields, cut map, supported-core zero and successor, and the actual represented-predicate Frege induction formula. It discharges property coverage, application testing, deletion closure, literal successor commutation, forward numberhood, surjectivity and exact quantified-Infinity transfer at every fixed counting type. With quantified Infinity it obtains literal numerical identity, the total unique inverse graph, reflected successor, and admitted-subset push/pull. The pushed subsets and induction image are proved admitted; this closes that outstanding Actuality interpretation premise of the earlier generic kernel.

Dependencies: the frozen ActualityCore and CoreNumberIsomorphism modules, and their dependencies. The target definitions and current interpretation scope are explicit. No Choice, BF, C5, boxed Actuality, external standardness or selecting inverse operation is assumed.

Preferred fingerprinted serial commands, from the bundle root (compiler owner only):

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ActualityCoreNumbers --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ActualityCoreNumbersCertificates --timeout 180
```

The driver requests all three audits and key `.derivable` axiom reports. Repository validation passed after the source batch: 132 principles, 447 results, 162 models. This validates records, not these Lean proofs.

Still outstanding: concrete Gallin-core realization; arbitrary syntax interpretation; addition/multiplication graph identification. A separate arithmetic-graph module will address the last item without reopening these frozen files.

## READY FOR INTEGRATION — internal arithmetic graphs

These files are frozen for the sole serial integrator. The 14 theorem drafts have not been compiled by their author.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FregeArithmeticGraphs.lean` | `d0448a51f720730ab5a6932a819d8250f4a5f71fe0b890999fa496b433f33bf4` |
| `topics/classicism/lean/Classicism/Results/Research/FregeArithmeticGraphsCertificates.lean` | `8891b31ef9f2505c90b6e63c43fa9ed2ef83397805eb7ed9f716cb5f5fbab7d7` |

Addition and multiplication are explicit impredicative least binary relations with zero/successor recurrence rules. The module proves the rules, totality, inversion, and functionality. Functionality uses quantified Infinity for literal successor cancellation. Totality uses no Infinity or Choice. All arguments stay in C's relational types and internal Frege-number induction; no external Nat or selecting function is introduced. These are concrete graphs whose target-core correspondence will be proved separately.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeArithmeticGraphs --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeArithmeticGraphsCertificates --timeout 180
```

The certificate driver requests the gate/type audits, translations and key axiom reports. Repository validation passed after the source batch; proof certification remains pending.

## READY FOR INTEGRATION — concrete Actuality arithmetic comparison

These two files are frozen for the sole serial integrator. The 21 theorem drafts have not been compiled by their author.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreArithmetic.lean` | `f62b430cedaed8f32b30535f4a3903f6112e99961f8b5c385152229ce4e7978e` |
| `topics/classicism/lean/Classicism/Results/Research/ActualityCoreArithmeticCertificates.lean` | `7690f3dbb96ca32e240241cf9be2b25975d5cea2144fbe39e18324a9ae42dd98` |

The core addition and multiplication graphs quantify over admitted supported binary relations. The binary image predicates used for reflection are constructed and proved admitted. The module proves forward and reverse graph comparison, target totality and functionality, addition-defined order comparison, and admission of the target arithmetic graphs as supported ternary/binary relations. Forward transfer and totality need only the actual-world witness; reflection and functionality also require quantified Infinity. This discharges the earlier arithmetic-graph identification gap for these explicit impredicative recurrence definitions.

The admitted binary-predicate push/pull laws are reusable. No ambient arithmetic operation is selected. No arbitrary-syntax truth lemma, external standardness or Gallin-core construction is asserted.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ActualityCoreArithmetic --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ActualityCoreArithmeticCertificates --timeout 180
```

All three audits and key axiom reports are requested by the driver. Repository validation passed after the source batch. A textual source scan found no proof holes, added axioms, Classical calls or hypothesis-extensionality tactics; this is not a replacement for the pending compiler and C certificates.

## READY FOR INTEGRATION — numerical-field support and Peano laws

These files are frozen for the sole serial integrator. The 15 theorem drafts have not been compiled by their author.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/ActualityNumericalRelations.lean` | `cf8a004cfad81f3f16af4f653869e5162c8da461a61617204498f850d3439c1d` |
| `topics/classicism/lean/Classicism/Results/Research/ActualityNumericalRelationsCertificates.lean` | `5882beb5132f1e9515f8a94dcd8d96c58d5d8937097640112d2e8f1ac3f6024f` |

Pushed unary and binary predicates are proved admitted on the number field itself, using current localization to seal image support. Admitted target numerical predicates and binary relations have literal push/pull round trips; source predicate comparison remains explicitly restricted to internal numbers. Addition, multiplication and order are admitted on the corresponding numerical product supports. Numerical-field induction, zero/successor disjointness and successor injectivity are also supplied, with quantified Infinity retained on the last two statements.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ActualityNumericalRelations --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ActualityNumericalRelationsCertificates --timeout 180
```

The certificate driver requests all three audits and representative axiom reports. The source scan found no proof holes, added axioms, Classical calls or hypothesis-extensionality tactics. Repository validation passed after the source batch. None of these checks establish compilation or object-language certification.

## Final author handoff and exact residual scope

Seven source modules plus seven certificate drivers have been submitted in this lane. All listed files are frozen; the sole serial integrator may repair them. The author executed no Lean/Lake commands, started no extra workers, and installed or downloaded nothing. Record YAML, generated Statements.lean and research sources were not changed. Each source module has a direct unpaginated source/section attribution. No database proof status was promoted.

Suggested dependency order: FregeInfinity; CoreNumberIsomorphism; GeneratedAlgebraTransfer independently; ActualityCoreNumbers after the world lane's ActualityCore; FregeArithmeticGraphs; ActualityCoreArithmetic; ActualityNumericalRelations. Run source and corresponding certificate driver serially, splitting translation drivers if necessary for memory. A source compile alone is not a C derivation.

Remaining substantive work:

- **Gallin:** the generic number-map kernel is ready, but concrete two-valued normalized property/cardinality domains, admitted higher-type predicates and the normalizer's truth/uniqueness/support laws still need an integrated source interface. The successor equation must use Frege coextension invariance to compare raw deletion with normalized deletion; arbitrary ambient cardinality objects must not be treated as coextension-invariant. The source is gallin-extensional-core.md §7; world-core-status.md separately records the missing Gallin domain/normalizer integration. No extra assumptions were substituted for these construction obligations.
- **Generated algebras:** the submitted result is the explicit one-sort, one-generator, one-unary/one-binary-constructor instance. Arbitrary finite multi-sorted signatures and their object-language encoding remain unformalized.
- **Interpretation:** the Actuality numerical and arithmetic graph constructions are concrete, including numerical subset/relation admission. A complete recursively indexed higher-order syntax interpretation and truth lemma remain separate work; these drafts do not claim them.
- **Certification:** all author submissions await the serial integrator's actual compiler, gate, relational type and object-language derivation results. Any integration report and its recorded source fingerprints supersede these initial draft hashes.

## Resumed broad-scope lane

The coordinating instruction explicitly resumes all interesting original families, not a ranked subset. `arithmetic-transfer-queue.md` maps every original numbered family, the missing main theorem, and immediate implementation order. Earlier final author handoff is superseded as a stopping point, not as a transfer of frozen-file ownership. New work stays in separate files. The world author owns the resumed actual/Gallin interpretation; the Max author owns predecessor/operation obstructions.

## READY FOR INTEGRATION — Frege finite-set calculus

Both files are now frozen for the serial integrator. No compiler was run here.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FregeFiniteSets.lean` | `9510257847837420c4ed3398a45107e5f6b47d040a14a7e52957eb238af9d2e3` |
| `topics/classicism/lean/Classicism/Results/Research/FregeFiniteSetsCertificates.lean` | `00fa78bf52b25fe1990cf66f99673e0696dc71566c394771ca4b5bd9ece1bd0d` |

Concrete proofs cover Frege-finite subsets, adjoining points, finite unions, finite-fibre unions, partial functional images, injective preimages, finite truth-coordinate separating families, equal-count inclusion, actual-Infinity/realization/outsider equivalences, count preservation by same-sort injective graphs, and the finite graph pigeonhole theorem. No external finite-list, Choice, BF or ND assumption replaces internal finiteness. Both graph sorts may be individuals. These are supporting foundations for original families 1–2 and the profile finite-powerset theorem, not a claim that those entire families are certified.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeFiniteSets --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeFiniteSetsCertificates --timeout 180
```

Repository validation passed after the source batch; gate/type/translation remain unexecuted by the author. The entire-module translation driver may be split into individual theorem drivers by the compiler owner.

## READY FOR INTEGRATION — arithmetic noncollapse and number-domain dichotomy

Both files are frozen for the sole compiler. The author ran no compiler.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FregeNoncollapse.lean` | `dcf960e4a9b29f61a90b13a99bf5dc4db499fea803237f890d14a4bc7546406c` |
| `topics/classicism/lean/Classicism/Results/Research/FregeNoncollapseCertificates.lean` | `949f2c9aa817942de59ff95c59b0d1bb32c00b60794978f22b7bd6e5adc229ae` |

The draft proves the successor-collision-at-bottom theorem, Noncollapse iff bottom is not a number iff every internal number is possibly realized, I iff IStar with the exact two Peano clauses, finite successor paths, finite numerical domain iff bottom is a number, and numerical infinitude iff relational Dedekind infinitude. It gives the successor graph explicitly, proves the finite graph pigeonhole obstruction, derives necessary finiteness in the collapsed case, and supplies a last nonbottom cardinality. This implements the bare-C part of original family 1 (§§26–27), rather than merely assuming a finite/infinite dichotomy. The C5 bridge to actual domain Infinity and the coalesced separator remain separate. The shallow ArithmeticI matches the existing arithmetic syntax by definition shape; a formal quotation equality with Meta.arithI is not yet submitted.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeNoncollapse --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeNoncollapseCertificates --timeout 180
```

Repository validation passed after the source batch. No new axiom or optional-premise necessitation was inserted. Gate/type/translation remain the serial checker's responsibility.

## READY FOR INTEGRATION — canonical cross-base arithmetic graphs

Both files are frozen for the serial compiler; no compilation was run here.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/CrossBaseArithmetic.lean` | `a71fa2104c6f0867637f83fdb5284edf47761eecda63a5768a7d111f2ee8c058` |
| `topics/classicism/lean/Classicism/Results/Research/CrossBaseArithmeticCertificates.lean` | `a694a05e2cca825d005b5356587ff20a310cf40628e3a31e28b08eb904bb5607` |

This is the concrete least synchronized-successor relation of original family 5, not an assumed comparison map. The proofs give unfolding, totality at both bases, symmetry, functionality under source noncollapse alone, injectivity under target noncollapse, the graph bijection under both, uniqueness among supported successor-preserving function graphs, and addition/multiplication preservation. A possibly collapsed target is retained in the one-way results. No actual quantified Infinity, operation selection, external numerical standardness or intensional equality of coextensive graphs is assumed.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.CrossBaseArithmetic --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.CrossBaseArithmeticCertificates --timeout 180
```

Repository validation passed. Still to connect explicitly: the existing Certified/Arithmetic Sum/Prod vocabulary, formal quotation of I, and the metalinguistic first-order formula induction. The graph theorems themselves have complete draft proofs; the object-language certificates remain unchecked by this author.

## READY FOR INTEGRATION — arbitrary finite-signature proof emitter

The generator, selected signature, emitted source and certificate driver are frozen for the sole compiler/integrator.

| File | SHA-256 at handoff |
|---|---|
| `research/2026-10-22/lean-formalization/generate_generated_algebra.py` | `791d5602965c449fa76f912918ba7356ebaeec3747d3bc806d41649b65c93cb8` |
| `research/2026-10-22/lean-formalization/generated-algebra-finite-signature.json` | `099248c62d3a6319822693a89202cfd44d88a8dff982042aa25bfcc8dd8daf7f` |
| `topics/classicism/lean/Classicism/Results/Research/GeneratedAlgebraFinite.lean` | `b4911c128403a5c245e384369aeb01cc340b4b4e9f72cb1de46b842fae176f1d` |
| `topics/classicism/lean/Classicism/Results/Research/GeneratedAlgebraFiniteCertificates.lean` | `4dc2e5466baa04662c5317eb14fe052e6497426dd16e16e4f43c53c33c637b3e` |

The emitter accepts any finite list of relational source/target sorts and any finite list of constructors with arbitrary finite typed input lists, including nullary generators, repeated input sorts, sorts with no generators, and the vacuous empty signature. It emits concrete simultaneous impredicative definitions and proof bodies for source closure/persistence/C5 rigidity, target closure, forward transfer, image-rigidity-based surjectivity, left inverses, injectivity and right inverses at every sort. The given map/commutation premises are exactly those of the original generated-algebra theorem; persistence and onto are proved, not assumed.

The saved stress instance has three distinct source and target sorts, two generators, and cross-sort unary, binary, repeated-sort binary and ternary constructors. Python-only checks covered the vacuous signature, two empty generated sorts and a quaternary constructor, rejected malformed signatures, and verified exact saved-source reproducibility. These checks do not certify Lean proofs.

**Exact generality status:** this is a uniform proof-producing implementation of the all-finite-signature schema, with each emitted instance intended for kernel/type/C checking. It is not yet a single deep-syntax metatheorem universally certified over signature codes, and no generated instance is claimed checked by this author. A passing stress instance alone would not certify the generator universally. That distinction remains in the queue.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.GeneratedAlgebraFinite --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.GeneratedAlgebraFiniteCertificates --timeout 180
```

For a new signature, invoke `generate_generated_algebra.py SIGNATURE.json NEW.lean --module MODULE --certificates NEWCertificates.lean`; it refuses to overwrite existing frozen paths. Then run the generated source and certificate serially. Large drivers may be split per theorem. The three-sort instance is about 1,200 lines; all proof parameters remain ordinary relational types, not object-level finite-index/dependent-family objects.

## READY FOR INTEGRATION — raw profile cardinality theorems

The files below are frozen; author has not compiled them.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FiniteProfiles.lean` | `abbc3a0bcdefbd3dc238d4ce6b2bd446108b3ab8d1935bcfc4e39b0283a4de37` |
| `topics/classicism/lean/Classicism/Results/Research/FiniteProfilesCertificates.lean` | `369f5a4fd3b8ee902d145b34d2067eb9834ffa1165476c21275c2f4cf0c9ca64` |

The generic profile definitions quantify over actual admitted predicates. The proofs establish unique representation iff existence plus separation, finite coordinates plus separation implies finite profiles, complete profiles plus finite profile field implies finite coordinates, and the exact finiteness equivalence for unique profiles. A diagonal excludes any total disjoint-fibre graph coding the profile field into its coordinates, without selecting outputs or assuming Choice. Specializing to atom profiles `w ≤ V x` gives raw UWR finite atoms iff quantified finite base, the quantified-Infinity counterpart, no raw WR on propositions, and no raw WR on unary predicate inputs with an explicit argument witness. These are the concrete source §12/§20 results, not mere profile-interface assumptions.

The all-relational-input WR obstruction still needs the formal closed-type induction that constructs an injective constant-relation map. The explicit unary theorem retains its argument witness; a `Ty` marker alone was not treated as an inhabitation axiom. Rigid-profile UCP/AUCP equivalence requires its separate background and is not identified with raw WR/UWR here.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteProfiles --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteProfilesCertificates --timeout 180
```

Repository validation passed after the corrected draft. Gate/type/translation certification is pending the designated compiler.

## READY FOR INTEGRATION — exact arithmetic vocabulary bridge

Both files are now frozen for the designated serial checker. No compiler was run by the author.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FregeArithmeticVocabulary.lean` | `ce212432c93f250f5daa69fc0abcd733f2c7eb2100c1f73c7e6875a47b766599` |
| `topics/classicism/lean/Classicism/Results/Research/FregeArithmeticVocabularyCertificates.lean` | `ea36b39f2e01b4792c3a80564e9965b6b3be9aca5c3d98dc08629c04ebe5c99a` |

The five draft theorems identify the guarded AddGraph and MulGraph with the existing Arith.Sum and Arith.Prod ON NUMBERS, and transfer Sum, Prod and equality along the concrete synchronized-successor graph under the two displayed noncollapse assumptions. The old predicates are not identified away from the numerical fields. This discharges the vocabulary gap in original family 5; the first-order formula schema and deep-syntax I quotation remain separate.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeArithmeticVocabulary --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeArithmeticVocabularyCertificates --timeout 180
```

Repository validation passed after the source batch. Gate, relational type audit and translated C derivations remain pending. These are proof submissions, not certificates.

## READY FOR INTEGRATION — finite atoms and propositions

Both files are now frozen for the designated serial checker. No compiler was run by the author.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FiniteAtomProfiles.lean` | `fa1fac0c6cbb662e70b193187ba44b90876f79f794854ca831eec6ec57b42ebd` |
| `topics/classicism/lean/Classicism/Results/Research/FiniteAtomProfilesCertificates.lean` | `9d3d5912b54f7413a51dd9c914491745b441f7322399a2a67796306ff22d774b` |

The six draft theorems use Atomicity to prove that atom-incidence profiles separate proposition identities, then derive finite atoms iff a finite proposition domain. Together with raw UWR this gives finite base iff finite propositions and the exact quantified-Infinity counterpart. Neither Choice nor C5 is added. These are the actual atomic-coverage and finite-separation proofs, not an assumed cardinal comparison.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteAtomProfiles --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteAtomProfilesCertificates --timeout 180
```

Repository validation passed after the source batch. Gate, relational type audit and translated C derivations remain pending. These are proof submissions, not certificates.

## READY FOR INTEGRATION — C5 realization and null collapse

Both files are now frozen for the designated serial checker. No compiler was run by the author.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/C5Frege.lean` | `157a0a6be950be4ed400e020871e48603ca006e22b18b56dcf5855c69cda246b` |
| `topics/classicism/lean/Classicism/Results/Research/C5FregeCertificates.lean` | `ab1661d06e81428dff909c662ca43ec67626b3ae5aa1d8637fa262dc882c21c4` |

The draft constructs settled membership of persistent properties under BOXED ND_t, proves settled finite counts by Frege induction, and derives actual realization or literal bottom for every internal number. It then proves null collapse, numerical extensionality, actual quantified Infinity iff noncollapse iff ArithmeticI iff bottom is not a number, and finite base iff finite numerical domain. This supplies the C5/domain bridge of original family 1. It does not claim the finite-leaf semantic separator or replace quantified Infinity with an external finite-distinctness schema.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.C5Frege --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.C5FregeCertificates --timeout 180
```

Repository validation passed after the source batch. Gate, relational type audit and translated C derivations remain pending. These are proof submissions, not certificates.

## READY FOR INTEGRATION — finite rigid powers and binary core fields

23 October 2026. Both files are frozen for the designated checker; the author ran no compiler.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FiniteRigidPowers.lean` | `49ccd0c2e87ca33182998458922082f56a75dcd828f1accaf1e5b40427c7f2a1` |
| `topics/classicism/lean/Classicism/Results/Research/FiniteRigidPowersCertificates.lean` | `2b3c13d5b30c718389c5017471b70e14abdb103af4897559a7ff24fa928033ae` |

The proofs establish Fin(RigidPowerField A) iff Fin(A), construct finite whole-tuple haecceity codes, prove binary rigid support fields finite over finite factors, and prove the converse for each coordinate with the other coordinate inhabited. The nullary rigid proposition field is finite. This supplies concrete bare-C unary and binary steps for family 2; the all-type hereditary recursion is still outstanding.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteRigidPowers --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteRigidPowersCertificates --timeout 180
```

Repository validation passed for the source batch; Lean checking and any applicable C certificates remain pending.

## READY FOR INTEGRATION — finite operation fields and the BF predicate boundary

23 October 2026. Both files are frozen for the designated checker; the author ran no compiler.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FiniteFunctionFields.lean` | `2aa575af1ef32f47c8d8a1d6ec73783ed97a83255b914ca82c1fb549682e20d0` |
| `topics/classicism/lean/Classicism/Results/Research/FiniteFunctionFieldsCertificates.lean` | `418ae693dec5340b5de7171c989af8808d2ac182cd5ed45d16ac93945ec66cfb` |

Finite input/value fields plus operation separation give a finite admitted operation family. Functionality supplies the separation for the whole operation domain; BF supplies Functionality. Evaluation of constant operations gives the output converse with an explicit input witness, and unary haecceities give the input converse for predicates. Thus, with BF and an input witness, quantified Infinity at the predicate type is exactly Infinity at the input or proposition type. No extensional fullness or externally standard numeral bound is used.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteFunctionFields --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteFunctionFieldsCertificates --timeout 180
```

Repository validation passed for the source batch; Lean checking and any applicable C certificates remain pending.

## READY FOR INTEGRATION — first-order arithmetic structural transfer

23 October 2026. Both files are frozen for the designated checker; the author ran no compiler.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/CrossBaseFirstOrder.lean` | `7ad93094418ca6f0a2b6fa548f43756ce041819467fae7de65a632fb09ccbbc8` |
| `topics/classicism/lean/Classicism/Results/Research/CrossBaseFirstOrderChecks.lean` | `ef8fecbfeb77a66abd4efccc3b752958d682dfa4af71dda4dcde73d32a62717f` |

A structural induction over the repository's exact Meta.ATerm/AForm grammar proves term synchronization and formula/sentence invariance under the concrete cross-base relation, including guarded universal quantifiers and the existing Sum/Prod vocabulary. This is external syntax metatheory with Nat/Fin environments, not an object-language C theorem over a syntax-code domain. The Checks file requests kernel axiom reports only. A full AForm.toTerm reflection theorem and a universally certified object-derivation builder remain outstanding.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.CrossBaseFirstOrder --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.CrossBaseFirstOrderChecks --timeout 180
```

Repository validation passed for the source batch; Lean checking and any applicable C certificates remain pending.

### Known static repair after CrossBaseFirstOrder ownership transfer

A post-handoff API comparison found that `synch_onto` and `synch_total` return a witness plus `Synch`, not a witness plus a numberhood/Synch pair. The frozen source is not re-edited by its author. `cross-base-first-order-repair.patch` supplies the two exact repairs: obtain the pair, then obtain numberhood from `synch_numbers`. Apply before the compiler check. This is a known draft error, not a failed compiler certificate or a new mathematical premise.

## READY FOR INTEGRATION — C5 comparison with concrete Actuality numbers

23 October 2026. The following files are frozen for the designated serial checker. The author has not run Lean, Lake, or any compiler.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/C5ActualityNumbers.lean` | `f88bef4440fe4c357058584eab7e75a9fd40d9811fe11dc663cd71278d187af6` |
| `topics/classicism/lean/Classicism/Results/Research/C5ActualityNumbersCertificates.lean` | `9fea23da942bb2cbba6a837b61454a0423d065fa837374f9f35e32dcc04e48d4` |

Eleven draft theorems give injectivity and the relational inverse of the existing concrete numberMap under C5 plus Actuality, including finite bases. They preserve and reflect zero/successor, represented subsets and binary predicates, addition, multiplication and order through the existing admitted target graphs. They do not assert PA on collapsed finite number systems or require actual quantified Infinity.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.C5ActualityNumbers --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.C5ActualityNumbersCertificates --timeout 180
```

Repository validation passed. Source/gate/type/translated-C checking is pending; schema assemblies additionally require the listed full-schema theorem.

## READY FOR INTEGRATION — finite Hume classes without Plenitude

23 October 2026. The following files are frozen for the designated serial checker. The author has not run Lean, Lake, or any compiler.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FregeHumeClasses.lean` | `c694371e538d035a1c9310d86fde17c6d21a6b5b8fbbb8f1cf74ed4f83275484` |
| `topics/classicism/lean/Classicism/Results/Research/FregeHumeClassesCertificates.lean` | `675be0e75ca3cfd97638855dd6bbcac70ff2d24cdb270dce4f1a4150e10bdf95` |

The draft defines actual supported bijection graphs, constructs an extended graph in each Frege induction step, and proves common finite count iff graph equinumerosity. Under C5 a persistent finite property has an explicit Hume class literally equal to its Frege number; equal Hume classes characterize equinumerosity on persistent finite properties. No selector, global Choice, Plenitude or external standardness is assumed.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeHumeClasses --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeHumeClassesCertificates --timeout 180
```

Repository validation passed. Source/gate/type/translated-C checking is pending; schema assemblies additionally require the listed full-schema theorem.

## READY FOR INTEGRATION — raw WR at every relational input type

23 October 2026. The following files are frozen for the designated serial checker. The author has not run Lean, Lake, or any compiler.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/RawWorldRepresentationBoundary.lean` | `0a9132fce0b8b10570e2cf33db8d6f1de4d0972ecc454abe4ef117cae6b8773c` |
| `topics/classicism/lean/Classicism/Results/Research/RawWorldRepresentationBoundaryCertificates.lean` | `c452c19b2caeb1e5af097c8015a6d4473573e3355f12b2d010b98ea7949970d7` |
| `topics/classicism/lean/Classicism/Results/Research/RawWorldRepresentationBoundarySchemas.lean` | `239b50a921d47164b242452846d453f332e95534220dad8f810a61ca85694337` |

The unary constant-predicate diagonal is vectorized over arbitrary finite argument lists, and the complete C Existence schema discharges tuple inhabitation. The schema assembly covers every closed relational input type, including propositions via the empty list. A missing listRule/listEntails is explicitly a failed check. This is now a complete draft schema construction for the former all-relational-input gap; its object-language certificate still must be run.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.RawWorldRepresentationBoundary --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.RawWorldRepresentationBoundaryCertificates --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.RawWorldRepresentationBoundarySchemas --timeout 180
```

Repository validation passed. Source/gate/type/translated-C checking is pending; schema assemblies additionally require the listed full-schema theorem.

## READY FOR INTEGRATION — finite tuple laws

23 October 2026. The following files are frozen for the designated serial checker. The author has not run Lean, Lake, or any compiler.

| File | SHA-256 at handoff |
|---|---|
| `topics/classicism/lean/Classicism/Results/Research/FiniteTupleLaws.lean` | `5e1bb21b3a0476893464ceb3ce64bf900d9ef08521152c1873ae2f49c8afa564` |
| `topics/classicism/lean/Classicism/Results/Research/FiniteTupleLawsCertificates.lean` | `5f5009719a3983ddcbf9e8b577aabd9f7f38d5413edf5c5df238eba34450e069` |

The wrapper laws request genuine vectorized listRule derivations of finite rigid powers and finite separating families. These are arbitrary finite tuple arities in the existing syntax, not new tuple sorts. The recursively defined hereditary-domain interpretation and its all-type classification remain separate obligations.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteTupleLaws --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FiniteTupleLawsCertificates --timeout 180
```

Repository validation passed. Source/gate/type/translated-C checking is pending; schema assemblies additionally require the listed full-schema theorem.
