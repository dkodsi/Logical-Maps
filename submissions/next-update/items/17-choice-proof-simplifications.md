# Shorter Choice proofs and modal rigidity

**Contribution:** A shorter proof of an established package equivalence, a sharper Functional Choice theorem, and new modal-choice corollaries.

Over C,

```math
\Box\mathrm{Plenitude}+\mathrm{Relational\ Choice}
\quad\Longleftrightarrow\quad\Box\mathrm{Functional\ Choice}.
```

Select a functional graph, represent it using Plenitude, and apply observer transport. Boxed Plenitude supplies the required observers independently of No Pure Contingency. This proves the existing equivalence without the conjugation argument or the alternative Zorn/well-ordering route.

The sharp instancewise theorem is

```math
\mathrm C+\mathrm{Atomicity}_t+\mathrm{BF}_\Delta+\mathrm{FC}_{\sigma,\tau}
\quad\vdash\quad\Box\mathrm{FC}_{\sigma,\tau},
\qquad\Delta=\{\sigma\tau t,\sigma,\tau,\sigma\tau\},\quad\tau\ne e.
```

Its shortest proof uses principal atom tests directly: transform the input relation, reuse the operation witness, and conclude every atom entails the Choice sentence. No full OS construction, extra BF at t, ND or C5 is needed.

The same proof review gives two further connections, without observer premises:

| Premises over C | Conclusion |
|---|---|
| ND at t + BF at σt | Each Intensional Choice instance is equivalent to its necessary form. |
| ND at t + BF at στt | Each Modalized Relational Choice instance is equivalent to its necessary form. |

Their negations are rigid too. The proof treats inner boxed formulas as single tests, so BF is needed only at the outer binder types. Over C5, Modalized Relational Choice is consequently equivalent to ☐Relational Choice + Intensional Choice, also to ☐Relational Choice + ☐Intensional Choice.

[Statements, proofs and native record correspondence](../proofs/choice-proof-simplifications.md). The all-type consequences target the existing `intensional-choice-r` / `necessary-intensional-choice-r` and `modalized-relational-choice-r` / `necessary-modalized-relational-choice-r` nodes. The original No Pure Contingency reflection records remain separate valid results.

New connecting arguments: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`).

**Proof length:** Short (965 words in the linked proof; imported dependencies excluded).
