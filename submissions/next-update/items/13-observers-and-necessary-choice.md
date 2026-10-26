# Witness transport and supporting observer results

**Contribution:** Finite-instance reflection proofs and consolidation of existing connections.

Observer separation concerns identity and distinguishability at **every admitted relational type**; propositions are the zero-argument case. An observer $`E:tt`$ acts on proposition-valued instances, while separation compares whole relations across their argument tuples and connects these tests to Functionality.

The [proposals](../../classicism-results-2026-10-24-v2/CANDIDATES_DK.md#observers) and [existing hierarchy](../../classicism-results-2026-10-24-v2/proofs/h-observer-space/SUMMARY.md) supply the structural context. The [Rev definition](14-reversible-separation-single-sentence.md), [group representation](18-reversible-group-semantics.md), [OS shift semantics](15-observer-shift-semantics.md) and [shorter OS schema](19-observer-single-type-schema.md) have separate entries. This page covers witness transport and its applications.

## Choice and comprehension

For full schemas over C,

```math
\mathrm C+\mathrm{OS}+\text{Functional Choice}
\quad\equiv\quad
\mathrm C+\Box\text{Functional Choice}.
```

The equivalence was already derivable through Plenitude, endpoint separation and No Pure Contingency. For this consequence, the new direct proof needs just one choice instance and one finite propositional separation instance:

```math
\mathrm C+S_{t,\Delta}+\mathrm{FC}_{\sigma,\tau}
\quad\vdash\quad\Box\mathrm{FC}_{\sigma,\tau},
\qquad\Delta=\{\sigma\tau t,\sigma,\tau,\sigma\tau\},\quad\tau\ne e.
```

Transform the input relation by $`U^E[x,y]=E(U[x,y])`$. Its selecting operation $`f`$ can be reused unchanged in $`fx`$. Every qualified observer therefore accepts the choice sentence, and separation identifies it with Top. No C5 premise or observer surjectivity is required. See the [transport theorem, §3](../proofs/observer-witness-transport.md#3-transport-with-witnesses-used-as-arguments), and [Choice proof, §2](../proofs/observer-choice-transport.md#2-why-functional-choice-reflects).

The [direct atom-test proof](17-choice-proof-simplifications.md) starts instead with Atomicity and the relevant BF instances. It shortens the total proof even after counting the test construction, and gives a short proof of ☐Plenitude + Relational Choice ⇔ ☐Functional Choice.

At any fixed relation type, **Rigid, Persistent and Gallin Extensional Comprehension** likewise become necessary under current ND at $`t`$ and separation qualified at the relation type and its argument types. Their witnesses have observer-fixed values. The [comprehension proof](../proofs/observer-comprehension-reflection.md) gives this refinement of the older full-schema results. The transport theorem also covers Boolean Completeness and Plenitude with the stated output-type ND premise.

## Necessary separation and mathematical propagation

Under C5 + ☐OS, each of the supported Choice, completeness and comprehension instances is modally constant:

```math
\Diamond A\quad\longleftrightarrow\quad A
\quad\longleftrightarrow\quad\Box A.
```

The [positive-bounds proof](../proofs/necessary-observer-positive-bounds.md) gives the exact finite qualification lists. At a fixed carrier type, separately possible unary, binary and ternary Rigid Comprehension therefore suffice for CH and first-order analytical propagation. The general CH conclusion from C5 + ☐OS remains [unresolved](../PENDING.md).

## Completeness and observer images

Over C + BC_t, a logical observer that commutes with native ☐ accepts BC_t if it is idempotent or surjective. Separation by either class therefore gives ☐BC_t. The [image-bound proof](../proofs/box-observer-completeness.md) needs neither C5 nor Actuality.

Without native-☐ preservation, even necessary typed OS and BF do not suffice. The [infinite-colour model](../proofs/infinite-colour-conditional-completeness-countermodel.md) satisfies

```math
C+BC_t+\Box\mathrm{OS}+\Box\mathrm{BF}_{\mathrm{all}}
+\Diamond(\Box ND_t\land\neg BC_t).
```

Its target satisfies full C5. Thus OS + BC_t does not imply ☐(☐ND_t → BC_t). This removes a proposed completeness-persistence route to the Max comparison; the Max + OS + BC_t question remains open.

## Supporting structure and models

The [typed-core theorem](21-observer-classical-cores.md) gives a complementary use of logical observers: over C5, an idempotent observer determines a whole Henkin model. Endpoint retractions already give canonical classical cores over C, with an individual quotient when needed; Functional Choice and Boolean Completeness descend to those cores. This uses recursive normalization rather than the witness-reflection argument above.

The [Rev characterization](12-reversible-family-realization.md) gives a modal interpretation of reversible symmetry. Its model comparison explains the strength beyond recoverable observation and restricted parameter noncontingency.

The [Choice model comparison, §§3–5](../proofs/observer-choice-transport.md#3-extensional-fullness-at-a-trivial-symmetry-object), explains why arbitrary selector relations need an observer-image witness, whereas selecting operations can be reused as arguments. It verifies current Relational Choice at $`W_1`$ of the existing qualitative-contrast model, in ZFC, while its necessary form fails despite C5 and qualified left-inverse separation.

The [correct-evaluator constructions](16-evaluators-and-comprehension.md) separately connect established completeness and comprehension principles. Correct evaluation is weaker than full logical qualification.

New transport arguments: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`). Earlier observer results and the Bacon–Dorr and Dorr constructions retain their original attribution in the proofs.

**Proof length:** Long (11,108 words in the linked proofs; imported dependencies excluded).
