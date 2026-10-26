# Choice, atom tests and necessity

The direct atom-test proof makes a single Functional Choice instance necessary under Atomicity and four relevant BF instances. It avoids the all-type conjugation and No Pure Contingency theorem. Related proofs give a short established package equivalence and new type-specific rigidity consequences for modal choice.

## 1. A single Functional Choice instance

Fix admitted $`\sigma,\tau`$ with $`\tau\ne e`$. Let $`\rho=\sigma\tau t`$, $`\Delta=\{\rho,\sigma,\tau,\sigma\tau\}`$, and

```math
A:=\mathrm{FC}_{\sigma,\tau}:=
\forall U^\rho\, .\,
(\forall x^\sigma\exists y^\tau\, .\,U[x,y])
\to\exists f^{\sigma\tau}\forall x^\sigma\, .\,U[x,fx].
```

**Theorem.**

```math
\mathrm C+\mathrm{Atomicity}_t+\mathrm{BF}_\Delta
+\mathrm{FC}_{\sigma,\tau}
\quad\vdash\quad\Box\mathrm{FC}_{\sigma,\tau}.
```

For any propositional atom $`a`$, define the admitted test $`P_a(p):=\Box(a\to p)`$. An atom lies below exactly one of $`p,\neg p`$, so the test's truth values preserve negation. Boolean entailment gives preservation of conjunction, acceptance of Top and rejection of Bottom; the other Boolean truth laws follow.

For each $`\kappa\in\Delta`$, BF and CBF, with fixed-parameter quantifier distribution, give

```math
P_a(\forall x^\kappa\, .\,Fx)
\quad\Longleftrightarrow\quad\forall x^\kappa\, .\,P_a(Fx).
```

Existential truth follows by duality. Apply these truth equivalences through the single displayed formula $`A`$. The result is

```math
P_a(A)\leftrightarrow
\forall U^\rho\, .\,
(\forall x^\sigma\exists y^\tau\, .\,P_a(U[x,y]))
\to\exists f^{\sigma\tau}\forall x^\sigma\, .\,P_a(U[x,fx]).
```

For each $`U`$, abstraction admits $`U^a:=\lambda x,y\, .\,P_a(U[x,y])`$. Current $`\mathrm{FC}_{\sigma,\tau}`$ selects an operation for $`U^a`$ whenever it is serial. Its operation witness is reused unchanged in $`fx`$. Thus the right side is true, and $`a\le A`$ for every atom $`a`$.

If $`A\ne\top`$, Atomicity supplies an atom below $`\neg A`$, contradicting the preceding conclusion. Hence $`A=\top`$, which is $`\Box A`$.

Only the displayed BF instances are used; BF at t is needed only when t is already in $`\Delta`$. There is no assumption of ND, C5, a true atom, Actuality, other Choice instances or OS. The proof uses the tests' truth conditions directly and does not construct full logical qualification. For a finite input tuple, list its binder types and the corresponding relation and operation types; the same argument applies.

The [general observer version](observer-choice-transport.md#2-why-functional-choice-reflects) replaces Atomicity plus these BF instances by $`S_{t,\Delta}`$. The [guarded atom construction](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/observer-lattice.md#5-atomicity-improves-the-logical-separation-upper-bound) supplies that separation, but its whole-operation qualification is unnecessary for the direct proof above.

Compared with the older full-schema route, this drops the Plenitude-to-ND step, stabilization to C5, atom swapping, all-type conjugation and invariance of arbitrary pure terms. The reduction in proof work remains after counting the atom-test construction.

## 2. Boxed Plenitude and current Relational Choice

Over C, the established packages satisfy

```math
\begin{aligned}
\Box\mathrm{Functional\ Choice}
&\Longleftrightarrow\mathrm{OS}+\mathrm{Functional\ Choice}\\
&\Longleftrightarrow\mathrm{End}+\mathrm{Relational\ Choice}\\
&\Longleftrightarrow\Box\mathrm{Plenitude}+\mathrm{Relational\ Choice}\\
&\Longleftrightarrow\mathrm{C5}+\mathrm{Atomicity}_t+\mathrm{Relational\ Choice}.
\end{aligned}
```

Here End is full endpoint logical separation. The short proof of the boxed-Plenitude direction is particularly useful. Boxed Plenitude supplies C5 and Atomicity, and current Plenitude. Relational Choice selects a functional graph from each serial relation; Plenitude represents the graph by an operation. This gives Functional Choice. Section 1 now makes each instance necessary, since C5 supplies the required BF instances. Equivalently, the independent principal-atom construction supplies End and OS, and observer transport completes the proof.

Conversely, boxed Functional Choice supplies boxed Plenitude and boxed Relational Choice; T gives current Relational Choice. The equivalence of boxed Plenitude with C5 + Atomicity at t, and of that package with End, gives the remaining forms. For OS + Functional Choice, direct observer transport gives boxed Functional Choice; the reverse follows from boxed Plenitude and T.

This is a shorter proof of an existing equivalence. It avoids both the No Pure Contingency proof and the alternative route through transversals, Zorn and modal well-ordering. Relational Choice remains unboxed in the starting package.

## 3. Rigidity of modal choice

**Lemma.** Assume ND at t and BF at the exposed binder types of a formula built from boxed tests by Boolean operations and quantification. The formula and its negation imply their necessities. Binders inside the boxed tests do not enter the requirement.

For a true $`\Box B`$, axiom 4 gives necessity. If it is false, $`B\ne\top`$, and ND gives $`\Box(B\ne\top)`$, namely $`\Box\neg\Box B`$. Boolean induction preserves endpoint-valuedness. A true universal is made necessary by the pointwise induction hypothesis and BF at its binder. A false universal has a current counterexample with a persistent negated matrix; necessitated existential introduction preserves that counterexample. Existentials follow dually. No optional ND or BF premise is necessitated.

Intensional Choice has the form

```math
\mathrm{IC}_\sigma:=\forall F^{\sigma t}\, .\,
\Box\exists x^\sigma\, .\,Fx
\to\exists G^{\sigma t}\, .\,G\le F\land\Box\exists!x^\sigma\, .\,Gx.
```

The entailment $`G\le F`$ is a boxed universally closed implication. Its exposed binders are therefore only at $`\sigma t`$. Modalized Relational Choice is

```math
\mathrm{MRC}_{\sigma,\tau}:=\forall R^{\sigma\tau t}\, .\,
\Box\mathrm{Serial}(R)
\to\exists S^{\sigma\tau t}\, .\,\Box\mathrm{Functional}(S)\land S\le R.
```

Its exposed binders are at $`\sigma\tau t`$. The lemma gives

```math
\begin{aligned}
\mathrm C+\mathrm{ND}_t+\mathrm{BF}_{\sigma t}
&\vdash\mathrm{IC}_\sigma\leftrightarrow\Box\mathrm{IC}_\sigma,\\
\mathrm C+\mathrm{ND}_t+\mathrm{BF}_{\sigma\tau t}
&\vdash\mathrm{MRC}_{\sigma,\tau}\leftrightarrow\Box\mathrm{MRC}_{\sigma,\tau}.
\end{aligned}
```

Their negations are rigid too. No observer premise is needed. C5 supplies the hypotheses, so the existing implications for boxed Modalized Relational Choice give, over C5,

```math
\begin{aligned}
\mathrm{Modalized\ Relational\ Choice}
&\Longleftrightarrow\Box\mathrm{Relational\ Choice}+\mathrm{Intensional\ Choice}\\
&\Longleftrightarrow\Box\mathrm{Relational\ Choice}+\Box\mathrm{Intensional\ Choice}.
\end{aligned}
```

Forward, make Modalized Relational Choice necessary and use its established boxed consequences. Reverse, boxed Relational Choice and Intensional Choice supply the existing chooser-of-graphs proof. This does not make current Relational Choice necessary by itself.

## Sources and record correspondence

New type-specific arguments and proof comparisons: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), *Synthesis examples comparison*, §§1–3, and *Choice and mathematics proof comparison*, §§2–3, unpaginated. [Source hashes](../evidence/source-manifest.json) · [Review evidence](../evidence/proof-reviews.json).

The modal rigidity induction adapts the existing lemma in [C5 and Atomicity imply No Pure Contingency, §1](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/writeups/c5-and-atomicity-imply-no-pure-contingency.md#1-rigid-propositions-and-the-lifting-lemma). The original Goodsell–Yli-Vakkuri theorem and Dorr proof retain their attribution and certification; this is an application with specified binder scope.

Section 2 re-proves an existing derived connection using the records `relational-choice-and-plenitude-imply-functional-choice-r`, the necessary Functional Choice splitting records, and the boxed-Plenitude/Atomicity equivalences. Section 3 adds conclusions not derived by the proved-only native closure checked in the source audit. Relevant existing records are `necessary-modalized-relational-choice-implies-necessary-relational-choice`, `necessary-modalized-relational-choice-implies-necessary-intensional-choice`, and `necessary-relational-choice-and-intensional-choice-imply-modalized-relational-choice`.
