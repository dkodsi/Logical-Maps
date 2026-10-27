# Vicinity and Actuality

**Contribution:** Connections between Vicinity and Actuality, using one shared construction.

```math
C+\mathrm{Atomicity}_t+\mathrm{Vicinity}
\quad\Longrightarrow\quad\mathrm{Actuality}
```

The [atom-decision proof](../../integration-register/proofs/atomicity-vicinity-actuality.md) needs no Choice or completeness. Under Atomicityₜ, Actuality and Vicinity are equivalent. The existing NDₜ ⇒ Vicinity connection also gives NDₜ + Atomicityₜ ⇒ Actuality.

## Propositional completeness and Choice

```math
C+BC_t+\mathrm{Vicinity}+RC_{t,t}\ \Longrightarrow\ \mathrm{Actuality}
```

```math
C+BC_t+\mathrm{Vicinity}+\mathrm{Zorn}_t\ \Longrightarrow\ \mathrm{Actuality}
```

All added premises are unprefixed. The first theorem needs only Relational Choice with propositional inputs and outputs; the second needs only Zorn on propositions. Neither proof needs higher-type completeness.

Since Actuality implies Vicinity, **over C + BC_t plus either RC at t,t or Zorn at t, Actuality is equivalent to Vicinity and to the existence of an admitted cofinal chain of proper persistent propositions**. Here a persistent proposition satisfies p=☐p, and proper means p≠⊤. Cofinality says every proper persistent proposition entails a member of the chain. The [cofinal-chain proof](../../integration-register/proofs/modal-choice/persistent-fixed-points-and-cofinal-chains.md) therefore also gives Actuality when the persistent propositions are linearly ordered by entailment. Unprefixed propositional ND also suffices in place of Vicinity. Whether either pair of premises already implies Vicinity remains [open](../PENDING.md).

## One construction, two transfers

The [shared Vicinity construction](../proofs/vicinity-supported-interpretation.md) supplies a true support and a C5 interpretation on its supported domains. It preserves BC_t and carries any supported Actuality witness back to the original structure. The [Relational Choice transfer](../proofs/vicinity-relational-choice-and-propositional-completeness-imply-actuality.md) and [Zorn transfer](../proofs/vicinity-zorn-and-propositional-completeness-imply-actuality.md) then invoke their respective C5 Actuality theorems. The Zorn transfer does not assume or derive RC at t,t.

The C5 proofs use [two applications of propositional Relational Choice](../proofs/c5-relational-choice-and-propositional-completeness-imply-actuality.md), or [proposition-coded histories and masks under Zorn](../proofs/c5-zorn-and-propositional-completeness-imply-actuality.md), with the same [canonical-chain lemmas](../proofs/propositional-canonical-chain-lemmas.md).

The shared construction also gives a bare-C characterization: **Vicinity holds exactly when the persistent propositions have a greatest proper member**.

## A different completeness trade-off

With completeness at tt, the type of properties of propositions, Vicinity is unnecessary:

```math
C+BC_{tt}+\mathrm{Zorn}_t\ \Longrightarrow\ \mathrm{Actuality}
```

The [proof](../proofs/zorn-and-higher-completeness-imply-actuality.md) uses a reverse-wellordered chain of truths, its disjoint stage differences, and higher-type completeness to reflect truth of their join. This is a sharper type requirement for an implication already derivable from all-type completeness and all-type Zorn; no duplicate all-type record is proposed.

Over C5 plus either choice premise, BC_t, Actuality and all-type Boolean Completeness coincide. The converse from C5 + Actuality is the established [Bacon–Dorr completeness theorem](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/results/c5-and-actuality-imply-completeness.yaml).

New connecting arguments: OpenAI Codex, prompted by Daniel Kodsi, 25–26 October 2026 (`misc`). The common-core mechanism extends Christopher Sun's recorded 19 October 2026 Vicinity argument.

**Proof length:** Long (about 15,000 words across the linked proofs, counting the shared construction once).

## Database patch

[Patch 07](../patches/07-propositional-zorn-actuality.patch) supplies the Atomicityₜ + Vicinity implication, the two completeness-and-Choice implications and the C5 Zorn supporting theorem. It includes the cofinal-chain proof and uses the shared interpretation in [patch 05](../patches/05-c5-choice.patch). The records use existing principle nodes and retain the sharper propositional instances. The chain condition stays in the proof family; no new principle node or duplicate NDₜ corollary is proposed.
