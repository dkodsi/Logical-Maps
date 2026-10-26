# Vicinity, propositional completeness and choice recover Actuality

**Contribution:** Two new implications between established principles, using one shared construction.

```math
C+BC_t+\mathrm{Vicinity}+RC_{t,t}\ \Longrightarrow\ \mathrm{Actuality}.
```

```math
C+BC_t+\mathrm{Vicinity}+\mathrm{Zorn}_t\ \Longrightarrow\ \mathrm{Actuality}.
```

All added premises are unprefixed. The first theorem needs only Relational Choice with propositional inputs and outputs; the second needs only Zorn on propositions. Neither proof needs higher-type completeness.

Since Actuality implies Vicinity, **Actuality is equivalent to Vicinity over C + BC_t plus either RC at t,t or Zorn at t**. Unprefixed propositional ND also suffices in place of Vicinity. Whether either pair of premises already implies Vicinity remains [open](../PENDING.md).

## One construction, two transfers

The [shared Vicinity construction](../proofs/vicinity-supported-interpretation.md) supplies a true support and a C5 interpretation on its supported domains. It preserves BC_t and carries any supported Actuality witness back to the original structure. The [Relational Choice transfer](../proofs/vicinity-relational-choice-and-propositional-completeness-imply-actuality.md) and [Zorn transfer](../proofs/vicinity-zorn-and-propositional-completeness-imply-actuality.md) then invoke their respective C5 Actuality theorems. The Zorn transfer does not assume or derive RC at t,t.

The C5 proofs use [two applications of propositional Relational Choice](../proofs/c5-relational-choice-and-propositional-completeness-imply-actuality.md), or [proposition-coded histories and masks under Zorn](../proofs/c5-zorn-and-propositional-completeness-imply-actuality.md), with the same [canonical-chain lemmas](../proofs/propositional-canonical-chain-lemmas.md).

The shared construction also gives a bare-C characterization: **Vicinity holds exactly when the persistent propositions have a greatest proper member**.

## A different completeness trade-off

With completeness at tt, the type of properties of propositions, Vicinity is unnecessary:

```math
C+BC_{tt}+\mathrm{Zorn}_t\ \Longrightarrow\ \mathrm{Actuality}.
```

The [proof](../proofs/zorn-and-higher-completeness-imply-actuality.md) uses a reverse-wellordered chain of truths, its disjoint stage differences, and higher-type completeness to reflect truth of their join. This is a sharper type requirement for an implication already derivable from all-type completeness and all-type Zorn; no duplicate all-type record is proposed.

Over C5 plus either choice premise, BC_t, Actuality and all-type Boolean Completeness coincide. The converse from C5 + Actuality is the established [Bacon–Dorr completeness theorem](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/results/c5-and-actuality-imply-completeness.yaml).

**Proof length:** Long (about 12,600 words across the shared construction, two transfers, C5 proofs, chain lemmas and higher-completeness theorem; the shared proof is counted once).

New connecting arguments: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`). The common-core mechanism extends Christopher Sun's recorded 19 October 2026 Vicinity argument.

## Database patch

[Patch 07](../patches/07-propositional-zorn-actuality.patch) supplies the two Vicinity implications and the C5 Zorn implication, with a single shared-interpretation write-up and their proof dependencies. It uses the existing `vicinity`, `boolean-completeness-t`, `relational-choice-r`, `zorn-r` and C5 nodes; the records state the sharper propositional instances. No new principle node is proposed.
