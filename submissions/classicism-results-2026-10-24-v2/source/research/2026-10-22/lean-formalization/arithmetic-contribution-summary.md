# Arithmetic, finite domains, profiles and generated algebras

This is the contribution and scope index for the infinity/arithmetic lane, updated
23 October 2026. Current checking state is in
`verification-updates/infinity_arithmetic_profiles.json`; old submission hashes
and READY headings are historical, not current proof certification.
The [principal statement index](arithmetic-principal-statements.json) preserves
exact source text, type parameters, locations and hashes separately from that
verification ledger.

## Principal mathematical contributions

1. **Exact arithmetic Infinity.** `FregeNoncollapse` uses the internal impredicative
   Frege number predicate, proves that a collision of distinct numerical successors
   occurs only at the bottom cardinality, and identifies successor noncollapse
   with absence of bottom from the number field. It gives the finite/Dedekind-
   infinite dichotomy for that numerical field. `C5Frege` supplies the actual-domain
   bridge by proving settled finite counts on persistent properties and actual
   realization or bottom. C5 is boxed ND at propositions. Neither result replaces
   quantified Infinity with the external finite-distinctness schema.
2. **Concrete arithmetic comparison.** `CrossBaseArithmetic` constructs the least
   synchronized-successor relation between two counting bases. It is a total,
   onto function graph under source noncollapse and a bijection under both
   noncollapse premises. `FregeArithmeticVocabulary` connects its addition and
   multiplication statements to the existing guarded readings of `Arith.Sum` and
   `Arith.Prod`. `CrossBaseFirstOrder` is a structural metatheorem over the existing
   arithmetic grammar; it is not yet a universal C-derivation builder.
3. **Actuality numbers.** The concrete supported property/cardinal fields and
   number map in `ActualityCoreNumbers` have admitted induction images and onto
   proofs. Arithmetic and represented numerical predicates transfer through that
   map. `C5ActualityNumbers` uses null collapse to extend injectivity and reflection
   to finite bases; it does not assert Peano arithmetic on a collapsed finite
   system or select an inverse operation.
4. **Finite and profile calculus.** `FregeFiniteSets` proves finite subsets,
   unions, finite-fibre unions, relational images/injections, finite separating
   families and finite graph pigeonhole. `FiniteProfiles` and `FiniteAtomProfiles`
   give exact raw-UWR finiteness consequences and the Atomicity comparison with
   propositions. `RawWorldRepresentationBoundarySchemas` assembles the
   all-relational-input raw-WR obstruction using vectorization plus actual C
   Existence. Rigid-profile UCP is not identified with raw WR.
5. **Rigid powers and Hume classes.** `FiniteRigidPowers` and `FiniteTupleLaws`
   provide finite rigid-power/separation steps without assuming that sections of
   rigid relations are rigid in bare C. `FregeHumeClasses` constructs finite
   bijection graphs and the literal C5 identification of the Hume class of a
   persistent finite property with its Frege number.
6. **Generated algebra transfer.** `GeneratedAlgebraTransfer` proves the concrete
   one-sort transfer, image rigidity, onto and inverse laws. The finite-signature
   emitter produces complete shallow proof bodies for arbitrary finite relational
   sort lists and finite constructor arities; `GeneratedAlgebraFinite` is the
   saved three-sort instance. A checked instance is not a universal internally
   certified theorem over all signature codes. That interpretation gap remains.

## Prose proof sources

- [Frege Infinity and noncollapse](../notes/frege-infinity-20261022-1726.md),
  especially sections 20, 25–27.
- [Relational arithmetic, finite cores and synchronized graphs](../notes/relational-coding-recursion-20261022.md),
  especially sections 27, 30, 34 and 38.
- [Number-isomorphism refinement](../proof-refinements/infinity-core-number-isomorphism.md).
- [Generated-algebra transfer](../notes/c5-generated-algebra-transfer-20261022.md).
- [World and profile cardinality proofs](../notes/world-cardinality-ucp-20261022.md),
  especially sections 12 and 20.

## Certification boundary

Earlier core manifests record passing certificates for FregeInfinity,
CoreNumberIsomorphism, GeneratedAlgebraTransfer, FregeArithmeticGraphs and the
concrete Actuality-number/arithmetic/numerical-relation chain. The lane checked
the continuation in dependency order using the common locked runner and is now stopped for the human deadline. The continuation has these
fresh passes:

| Main certificate | Checked scope | Evidence |
|---|---|---|
| `FregeFiniteSetsCertificates` | Finite fibres, separating families, Infinity realization, finite self-injection surjectivity; full source/gate/type/translated-C audit | [Manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| `FregeNoncollapseCertificates` | Bottom criterion, possible-realization criterion, `ArithmeticI ↔ IStar`, finite/Dedekind-infinite number-field dichotomy; full source/gate/type/translated-C audit | [Manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| `CrossBaseArithmeticCertificates` | Canonical synchronized graph bijection and addition/multiplication transfer under both noncollapse premises; full C derivations | [Manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| `FregeArithmeticVocabularyCertificates` | Exact transfer for the existing Sum/Prod definitions on internal numbers; full C derivations | [Manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| `C5FregeCertificates` | Realization-or-bottom, numerical extensionality, actual Infinity iff ArithmeticI, and finite base iff finite numerical field under boxed ND at propositions; full C derivations | [Manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2) |
| `C5ActualityNumbersCertificates` | Concrete Actuality number-map bijection and arithmetic/order reflection under C5, including finite bases; full C derivations | [Manifest](checks/20261023T052411006203Z-90a4d7dd.json) |
| `FregeHumeClassesCertificates` | Finite count iff equinumerosity and literal Hume-class/Frege-number identity under C5 for persistent finite properties; full C derivations | [Manifest](checks/20261023T052411006203Z-90a4d7dd.json) |

`CrossBaseFirstOrderChecks` also passed as ordinary syntax metatheory in
[its manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2). It does not build
a C derivation uniformly for every formula code. The later quotation target
in that batch failed initially; its repaired module subsequently passed
[exact conversion and reflection](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2).

The printed principal `.derivable` proofs use only `propext` and `Quot.sound`
in Lean's metatheory; the translated conclusions are C derivations. This is
distinct from granting unrestricted extensionality inside C. Exact source and
dependency hashes are in the manifests. Noncollapse's initial elaboration errors
were repaired by parenthesizing the diamond argument and typing its existing
cardinality witnesses; no premise was added.

The generated-algebra emitter now regenerates both checked-in source and
certificate driver exactly, including dependency-certificate imports. The
three-sort source compiled, but its full translated-C driver timed out
after 180 seconds in [this manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2).
The Python reproducibility and source-compilation passes do not supply that
certificate; a bounded split of its translation driver is the next check step.
`FregeArithmeticQuotation` now verifies the exact-I syntax conversion. Its
conversion proof uses only `propext` and `Quot.sound`; its standard-denotation
reflection additionally uses existing `Classical.choice` and the type constant
`Classicism.e`, as ordinary metatheory. `FregeArithmeticReflection` now passes
for terms, all formulas and sentences
([manifest](https://github.com/dkodsi/Logical-Maps/releases/tag/classicism-results-2026-10-24-v2)). It uses standard
Prop-valued denotation and does not constitute an interpretation in arbitrary intensional models or a C-derivation builder.

Outstanding main obligations include universal all-signature interpretation,
recursive Gallin and arbitrary-syntax interpretation with the world/core lane,
a uniform C-derivation builder, arbitrary intensional-model syntax reflection,
and the model/effective constructions enumerated in `arithmetic-transfer-queue.md`.
No database verification flag or published proof is altered by these submissions.

## Reproduction

Run from the bundle root through the common locked runner, one target or small
dependency-ordered batch at a time. For example:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.FregeNoncollapseCertificates --timeout 180 --lock-wait 300
python3 research/2026-10-22/lean-formalization/check_with_mathlib.py Classicism.Results.Research.CrossBaseArithmeticCertificates Classicism.Results.Research.FregeArithmeticVocabularyCertificates Classicism.Results.Research.CrossBaseFirstOrderChecks --timeout 180 --lock-wait 300
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.GeneratedAlgebraFiniteCertificates --timeout 180 --lock-wait 300
```

`CrossBaseFirstOrderChecks`, `FregeArithmeticQuotation` and
`FregeArithmeticReflection` concern external syntax/metatheory. They must not
be reported as all-formula object-language certificates. The shared protocol
controls compiler use; old direct-Lake commands in the historical handoff are
not current instructions. Exit 75 means no compilation began because the lock
was occupied; it is neither a theorem failure nor a verification pass.

## Final checkpoint — 23 October 2026

The final profile batch was not checked; no mathematical refutation follows.

The [delivery manifest](arithmetic-delivery-manifest.json) records all 47 owned
Lean files and the generator inputs. The [current evidence audit](arithmetic-current-evidence.json)
compares the passing targets' full local dependency closures with their captured
source snapshots. These source comparisons do not replace compiler evidence.

Remaining execution work:

- `GeneratedAlgebraFiniteCertificates`: split the translation driver into bounded
  dependency-ordered pieces and complete the full audit. Its source compiled;
  the original full driver timed out at 180 seconds.
- `FiniteProfilesCertificates`, `FiniteAtomProfilesCertificates` and
  `RawWorldRepresentationBoundarySchemas`: the final check never started.
- `FiniteRigidPowersCertificates`, `FiniteFunctionFieldsCertificates` and
  `FiniteTupleLawsCertificates`: saved proof drafts and drivers remain unchecked
  in this delivery pass. The shared nullary rigidity source was repaired by its
  owner; that does not certify these dependent main results.

The universal generated-signature interpretation, recursive Gallin/hereditary
interpretation, uniform first-order C-derivation builder, and the semantic/effective
families in the original queue remain explicit formalization gaps. The checked
standard-denotation reflection does not supply arbitrary intensional-model
reflection. No original record, generated Statements file, database Lean flag,
or published/human-authored mathematical proof was changed by this lane.

