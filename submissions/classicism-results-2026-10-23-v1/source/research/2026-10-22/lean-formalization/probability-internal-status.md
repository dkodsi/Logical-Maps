# Concrete internal probability continuation

**READY FOR INTEGRATION — 44 source/driver files frozen across the submissions below.** Author has run no Lean/Lake/compiler/download. Existing frozen submissions were not edited. These are new C-language proofs and concrete code constructions, not additional external scalar interfaces.

- **SupportedReals:** the supported field of domain-relative Dedekind cuts and an explicit supported supremum operation. Actuality now discharges both previously assumed union-representative and extensional-code interfaces. Nonmember witnesses are inside the represented base domain. Bounded families have literally unique supremum codes; the operation graph is admitted and total/unique. The rational base domain and its arithmetic are not yet constructed.
- **NaturalOrder:** direct internal Frege-induction proofs for the existing AddGraph: zero/successor in the first input, commutativity, associativity, cancellation, zero decomposition, and additive numerical order with totality, antisymmetry and successor strictness. Quantified Infinity is retained where used. No assumed semiring or external Nat.
- **LeastNumber:** from that concrete numerical order, every nonempty represented field of internal numbers has a unique least member; each inhabited represented numerical fibre has a unique least-index graph. The positive-mass threshold nonemptiness will still require internal real Archimedeanness.
- **Cantor:** an explicit supported diagonal proves there is no represented serial injective graph from the full represented supported predicate interval into its base domain. Only current truth of its world guard is needed. This supplies the actual C diagonal in the type-ceiling proof; the finite-fibre/rank reduction is not silently assumed.

All statements preserve fixed relational types and current versus boxed scope. The source dependencies are the frozen world/core and Frege arithmetic submissions. No proof is claimed compiled, gated, type-checked or translated until the designated integrator runs the drivers.

## Exact serial checks

```sh
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilitySupportedRealsCertificates --timeout 180
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityNaturalOrderCertificates --timeout 180
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityLeastNumberCertificates --timeout 180
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityCantorCertificates --timeout 180
```

If translation needs memory isolation, use one-target derivative drivers rather than parallel builds. Shallow source checks alone do not count as object-language C certificates.

## Frozen source hashes

| Source | Handoff SHA-256 |
|---|---|
| [AtomicProbabilitySupportedReals.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilitySupportedReals.lean) | `acee83f5bb11608e9f6d6ac220c56c344568e069ab85a3aff1d658f19a86b4a3` |
| [AtomicProbabilitySupportedRealsCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilitySupportedRealsCertificates.lean) | `c5dd4555d8e5d7d08f6f2fea5f478cd29045da1ad174d1219261d2404e4fa211` |
| [AtomicProbabilityNaturalOrder.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNaturalOrder.lean) | `4603ae02e1e2e9d9bb04b2e912c5d0b8cd5b95aa8f1b4570bd4f616b7c9f5c13` |
| [AtomicProbabilityNaturalOrderCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNaturalOrderCertificates.lean) | `61454c0b9f23fff44f146341345787d190c070e091691f8a8417bbd7621240e1` |
| [AtomicProbabilityLeastNumber.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityLeastNumber.lean) | `8d3a9183b8edb6986652134e286d31ed6a3f0280c6b527f9da819276331289e6` |
| [AtomicProbabilityLeastNumberCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityLeastNumberCertificates.lean) | `62ed8450b219b638888b81bb92728f9c028576fc2ab88b31ecde0327ee11b842` |
| [AtomicProbabilityCantor.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCantor.lean) | `6ba316b1b04f5b4aee06ae004073a46618ebe383c6d7a23a157764055be1e2ae` |
| [AtomicProbabilityCantorCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCantorCertificates.lean) | `d9241952bb57239b49639de68201a21293c3efdbd67d693eae7c20c088360df1` |

Machine-readable imports and check targets: [probability-internal-manifest.json](probability-internal-manifest.json). Repository validation passed after each batch: 132 principles, 447 results, 162 models. This is not Lean verification.

Next independent work: actual multiplication/distributivity/cancellation for the submitted Frege graphs, then concrete signed-fraction codes; finite-code and finite-fibre/type-ceiling steps remain required. The field of rational codes, rational graph laws and Archimedean small-gap theorem are still exact outstanding constructions, not assumptions discharged by SupportedReals.

## Concrete numerical operations and semiring laws — READY FOR INTEGRATION

Six more files are frozen. Supported pointwise union realizes the actual CoreAdd/CoreMul graphs as literal numerical operation terms, without Choice or Plenitude. A normalized admitted predicate justifies induction on the actual numerical field. Direct internal induction then proves additive/multiplicative commutativity and associativity, distributivity, zero/one identities, additive cancellation, no zero divisors and cancellation of a nonzero multiplier. These laws have not been assumed as an external semiring interface. The context is current ActualWorld w plus quantified Infinity at the counting type.

The intended next use is the concrete fraction-code equivalence relation and its well-defined operations; no rational domain or Archimedean theorem is claimed merely from these numerical laws.

```sh
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityNumericOperationsCertificates --timeout 180
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityNumericAdditionCertificates --timeout 180
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityNumericMultiplicationCertificates --timeout 180
```

| Frozen source | Handoff SHA-256 |
|---|---|
| [AtomicProbabilityNumericOperations.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNumericOperations.lean) | `18b095e415da6a775c8779118ead5240fe2ac8830adc7196d905a0a9ffe23d23` |
| [AtomicProbabilityNumericOperationsCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNumericOperationsCertificates.lean) | `f3b4a80180877320b96cb9a2fd76f8d4d3c158324e2ba071a4927a2311a4a638` |
| [AtomicProbabilityNumericAddition.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNumericAddition.lean) | `a96dd900647ee5f2712fb845b9bd3ecac1b8b345931ccb313e9da2d77630db7e` |
| [AtomicProbabilityNumericAdditionCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNumericAdditionCertificates.lean) | `15e19d71c47b1e0a26fee877963535a64120800946acec1a7acf255125663c67` |
| [AtomicProbabilityNumericMultiplication.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNumericMultiplication.lean) | `b72a4498153e8eed300ebb75573d6722652807c93ae0edc8ccb1390fe312dcf1` |
| [AtomicProbabilityNumericMultiplicationCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNumericMultiplicationCertificates.lean) | `f75244b33d9355bb27fc2815eff0137e3756d6c5c228ccf0f1274ccf67e68023` |

## Concrete fractions and signed additive completion — READY FOR INTEGRATION

Fourteen more files are frozen to the designated serial integrator. The seven new source modules construct supported equivalence-class predicates for nonnegative fractions, prove cross-multiplication equivalence and literal identity, realize the addition and multiplication graphs, construct common denominators, and derive the cancellative commutative semiring laws and a concrete nonzero reciprocal. They then construct signed difference-class predicates, prove the injective nonnegative embedding, and realize an additive group with explicit transpose negation. All of this concerns the actual supported internal numerical domain under ActualWorld w and quantified Infinity; no external rational type, quotient, chosen representative, or assumed semiring is used.

The class codes use higher admitted relational types (natural code pairs, then fraction code pairs). The current graph values do not assert rigidity or necessitated field laws. The term names FractionField and RationalField designate the constructed domains; complete signed field/order/Archimedean laws are not yet claimed. Signed multiplication, ordered-field completeness hypotheses for the cut construction, represented finite families and the faithful-finite-fibre/type-ceiling reductions remain to be supplied.

No author compiler has run. The drivers request the C gate, type audit and object-language derivations; repository validation is separate from those checks. The machine-readable manifest contains every import, hash and exact serial command.

| New frozen source | Handoff SHA-256 |
|---|---|
| [AtomicProbabilityFractions.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractions.lean) | `64503e1ab36083caed6c0aa13888537bea50d4ac0f95383a4967e871080b8f95` |
| [AtomicProbabilityFractionsCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionsCertificates.lean) | `e53db87c9cbfb50e497d045aeb95a37349cc3093f7c72337cc32008fd0ad7313` |
| [AtomicProbabilityFractionArithmetic.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionArithmetic.lean) | `aef4d6f31a568edaa0a6f672274dd6be36309d71290b2d366e8a4a5c42ef9610` |
| [AtomicProbabilityFractionArithmeticCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionArithmeticCertificates.lean) | `a186648755c6d9da7f8ded36dd53e9c16967dec21f69b373bd4fe2bb7c95eb6c` |
| [AtomicProbabilityFractionAdditive.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionAdditive.lean) | `3bd62f03e43597a8700b13a9def5112bd355d58aaabcc790733c96cfa784231b` |
| [AtomicProbabilityFractionAdditiveCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionAdditiveCertificates.lean) | `db3cb9790b14e751ae71148e01a5d71f64a4f3a5b4191504b1b8ddec06c40123` |
| [AtomicProbabilityFractionMultiplicative.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionMultiplicative.lean) | `29e9a17aa0afbd862436cebe9347c07b2abaf7ffa40cc250dee4c3dd1a6bcbbc` |
| [AtomicProbabilityFractionMultiplicativeCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionMultiplicativeCertificates.lean) | `2d740c12018fadc9efc156f0377061d0ef2a98cb32550e207f00e158bbf9c752` |
| [AtomicProbabilityFractionInverse.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionInverse.lean) | `e170955b8d10f7f00fa8eb15fa03cbc80b9278d38c6a922cbc338c8288547701` |
| [AtomicProbabilityFractionInverseCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionInverseCertificates.lean) | `afba3aa59e9250ecd9257afa605d92a5d7aa08d8306c50b6d2d60cbe7778d5cc` |
| [AtomicProbabilitySignedRationals.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilitySignedRationals.lean) | `61cd636b546389ff011ad511cf01ea0df5bc3b6579f76869042a5e885b62ba32` |
| [AtomicProbabilitySignedRationalsCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilitySignedRationalsCertificates.lean) | `59f17bea500ad192419669673db9b34ad8fbda06a54152ca7ccacf24dd4c2c4a` |
| [AtomicProbabilityRationalAdditive.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityRationalAdditive.lean) | `b2fd32fbc7472ec7a334de5c06fd786dfb642e98b2a297eb5b307202e2384f93` |
| [AtomicProbabilityRationalAdditiveCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityRationalAdditiveCertificates.lean) | `7f8b1bdb31f395b11d67804cb236297f221d14a40b0c3efd5dd4e4d80467a0ed` |

Next mathematical target: prove the internal additive order and rational Archimedean bounds, and extend the signed construction with multiplication/order. Existing status sections describe earlier submission boundaries; this section supersedes their next-work descriptions.

## Concrete order, Archimedean bounds and a nontrivial complete cut order — READY FOR INTEGRATION

Twelve additional source/driver files are frozen on 23 October 2026. NumericComparison proves total additive comparison directly by internal number induction and proves that a nonzero number is at least one. FractionOrder, FractionArchimedean and FractionDensity derive the ordered nonnegative fraction structure, reverse order under reciprocals, bound each fraction strictly by an embedded internal natural, find a reciprocal natural below every positive fraction, and construct strict midpoints by explicit halving. RationalOrder extends the order to signed difference codes, with totality, antisymmetry, translation, density, no endpoints, natural upper bounds and the corresponding positive small-reciprocal theorem.

ConcreteReals instantiates the earlier supported-cut construction at that actual rational domain. Its source supplies principal cuts, an injective order-preserving and order-reflecting embedding, two distinct real codes, a total cut order, and literally unique suprema of represented nonempty bounded families. Thus its underlying rational domain/order are no longer arbitrary interfaces. The final supremum claim is for represented families; no claim about all external families or external standardness of the internal naturals is made.

This submission is still uncompiled author source. Gate/type/object-derivation drivers are supplied for every theorem, with the same exclusive serial compiler owner. Every source import resolves, and repository validation passed. These checks do not establish Lean or C certification.

| New frozen source | Handoff SHA-256 |
|---|---|
| [AtomicProbabilityNumericComparison.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNumericComparison.lean) | `8ba029eca1fb986678de54247256448e14deafbea97e4e2bccd0720de272f434` |
| [AtomicProbabilityNumericComparisonCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNumericComparisonCertificates.lean) | `90fb15550ecc9d6760b99c90686fe147b9d4e3957f105a0bc970e8a45ccbc380` |
| [AtomicProbabilityFractionOrder.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionOrder.lean) | `82d5c8a8063f5d32230d2ad4a4f5273f1c7a1dc47120dc6ead4ba13f369250eb` |
| [AtomicProbabilityFractionOrderCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionOrderCertificates.lean) | `5d80f53f6db4fd3e93f8d76f55a0bcff48b69101694f0aec323d0e8a501d0705` |
| [AtomicProbabilityFractionArchimedean.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionArchimedean.lean) | `aeff0231aeea06739dbdeea3acb42dca8b176d0cacd2ea1bacca3ec3608aecfa` |
| [AtomicProbabilityFractionArchimedeanCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionArchimedeanCertificates.lean) | `4107ecafbc18798fc239d2c9936c81c7880198efc15d2e37f12d35071d9894f1` |
| [AtomicProbabilityFractionDensity.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionDensity.lean) | `acceb1aa2aa30af485d4aebd9ad4de75eeb0e4fe0a6bab1987323fe06f8cccf2` |
| [AtomicProbabilityFractionDensityCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFractionDensityCertificates.lean) | `a756eef2ffaa60438fb837ff35058f09e59d1f594dd4390c2bb6bd45d1cc9621` |
| [AtomicProbabilityRationalOrder.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityRationalOrder.lean) | `69b8c85f052e793e4e8bbd9de15e29a1888f86e5fbffc607b398f4125ba3f660` |
| [AtomicProbabilityRationalOrderCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityRationalOrderCertificates.lean) | `d76d367610844ebf23ce43c50ba9f2b61441e77c795e56c5e61a5f5255e5c3e8` |
| [AtomicProbabilityConcreteReals.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityConcreteReals.lean) | `5414ccf3c1e62c0294dc72f2daeb03ed5e11e5b76d894e0ee587405c5306550f` |
| [AtomicProbabilityConcreteRealsCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityConcreteRealsCertificates.lean) | `8db89003fe8451e12a0d9325b2742b57f26fdc22dd0b339ef4bfb7e6924ca6e9` |

### Exact remaining scope

- Construct signed multiplication/reciprocal and finish its ordered-field laws; only the nonnegative fraction multiplicative laws are in this submission.
- Finish real negation, multiplication and positive normalization on the concrete cuts, including the Archimedean/small-gap transfer to cuts. Concrete real addition is now supplied by the final submission below; a complete real-field proof remains outstanding.
- Replace the external finite-support/finite-fibre probability interfaces with represented internal finite-family operations; prove the threshold/faithfulness equivalence and the finite-block/rank reduction needed before the already submitted Cantor diagonal.
- Complete symmetry/type-ceiling and global versus local hypothesis accounting after those bridges. No source status, map record, or existing mathematical note has been promoted by this handoff.

The earlier next-work paragraphs are historical checkpoints. This remaining-scope list is the current boundary; the overall probability formalization is not complete. The integrator may repair frozen files. The author will not edit them without explicit ownership return.

## Concrete real addition — READY FOR INTEGRATION

Four further files are frozen on 23 October. RationalTranslation supplies strict translation, subtraction cancellation and an associative addition graph guarded by actual rational domain membership. ConcreteRealAddition constructs the cut sum from that graph and supplies properness, downward closure, roundedness, literal commutativity/associativity, the principal zero identity, monotonicity, and an exact distribution identity for the represented supremum operation. The invalid codes remain outside the guarded graph, so no all-code ordered-group axiom is assumed.

These are uncompiled source claims with complete gate/type/derivation drivers. They do not yet establish additive inverses, real multiplication or the probability measure equivalences. The next concrete missing lemma is a represented finite-step crossing of a cut at arbitrarily small rational step size; internal numeric induction and the submitted rational Archimedean bounds supply the planned ingredients, but that lemma has not been submitted. Its use in proving the reverse additive-inverse inclusion remains explicit.

| New frozen source | Handoff SHA-256 |
|---|---|
| [AtomicProbabilityRationalTranslation.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityRationalTranslation.lean) | `98a479af83b8b6a1729a918c96dcc989e68517bea7a4a1d7de4264c716727e9b` |
| [AtomicProbabilityRationalTranslationCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityRationalTranslationCertificates.lean) | `379ea994dea939dbf01320a98be66bd243c77ffa69734f4afee67cfc123bc483` |
| [AtomicProbabilityConcreteRealAddition.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityConcreteRealAddition.lean) | `4e7135726462c48915ea7a6564d6e96cd114ca13c3b518a3f7bc3676b6f88f15` |
| [AtomicProbabilityConcreteRealAdditionCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityConcreteRealAdditionCertificates.lean) | `abc545de7d85f89dcfbfdadc4184b22d16ad0ccea9fe82a27a87710c40a05b40` |

Final author check for this handoff: all new import paths resolve; the newly frozen hashes were reread; repository validation passes (132 principles, 447 results, 162 models). No Lean, Lake, compiler or download process was launched by the author. Serial compilation, gate/type audits and object-language translation remain with the designated integrator.
