# One evaluator unifies completeness, Plenitude and comprehension

**Contribution:** Direct proofs of established connections, sharper type requirements, and a finite presentation of endpoint separation.

ND at t and Boolean Completeness at tt supply an admitted operation assigning Top to each current truth and Bottom to each current falsehood. Its diagonal gives Actuality:

```math
\mathrm C+\mathrm{ND}_t+\mathrm{BC}_{tt}
\quad\vdash\quad\exists E^{tt}\, .\,\mathrm{Correct}(E)
\quad\vdash\quad\mathrm{Actuality}.
```

Join the haecceities of the currently true propositions. ND makes the complement of each false proposition's haecceity an upper bound, forcing the required endpoint outputs. This avoids the older route through Vicinity and Weakly Inextensible Comprehension and requires neither BF nor OS. Completeness is at tt, not t.

Over C5, this yields the current-package equivalence

```math
\begin{aligned}
\mathrm{Actuality}
&\Longleftrightarrow\exists E\, .\,\mathrm{Correct}(E)
\Longleftrightarrow\mathrm{BC}_{tt}\\
&\Longleftrightarrow\mathrm{Boolean\ Completeness}
\Longleftrightarrow\mathrm{Plenitude}_{t,t}\\
&\Longleftrightarrow\mathrm{Plenitude}
\Longleftrightarrow\mathrm{Rigid\ Comprehension}.
\end{aligned}
```

The evaluator supplies explicit meets, operations representing functional graphs, and rigid coextensions. These global connections already follow from established results; the common construction and type localization are the contribution. The package need not imply OS or global Atomicity.

[Proof and original record references](../proofs/endpoint-evaluators-and-comprehension.md). The same join construction gives BC + ND ⇒ Weak Rigid Comprehension directly, preserving the weaker conclusion outside C5.

The [finite endpoint presentation](../proofs/endpoint-separation-finite-presentation.md) sharpens the observer connection. Over C,

```math
\mathrm{End}
\quad\Longleftrightarrow\quad
S_{t,\{t\}}+\mathrm{Eval}
\quad\Longleftrightarrow\quad
S_{t,\{t\}}+\mathrm{ND}_t+\mathrm{BC}_{tt}.
```

Here Eval is existence of a correct evaluator, and the single separation formula uses Boolean observers preserving only the quantifier at t. These finite premises recover the full endpoint schema, equivalently C5 + Atomicity at t or ☐Plenitude. The contribution is this finite assembly of established local arguments.

New connecting proofs: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`). Original theorem attributions remain with their records.

**Proof length:** Medium (1,736 words in the linked proofs; imported dependencies excluded).
