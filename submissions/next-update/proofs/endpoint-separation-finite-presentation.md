# A finite presentation of endpoint separation

Over C, one propositional separation formula and one correct truth evaluator give the full endpoint-separation schema:

```math
\mathrm{End}
\quad\Longleftrightarrow\quad
S_{t,\{t\}}+\mathrm{Eval}
\quad\Longleftrightarrow\quad
S_{t,\{t\}}+\mathrm{ND}_t+\mathrm{BC}_{tt}.
```

Here $`S_{t,\{t\}}`$ separates propositions using Boolean observers preserving the universal quantifier at $`t`$, as identities of whole operations. Put

```math
\mathrm{Eval}:=\exists E^{tt}\, .\,
\forall p^t\, .\,[(p\to Ep=\top)\land(\neg p\to Ep=\bot)].
```

No logical-preservation condition is part of Eval. Boolean Completeness at $`tt`$ concerns families of operations on propositions, not families of propositions.

## 1. Reaching C5 and a qualified evaluator

The [evaluator construction](endpoint-evaluators-and-comprehension.md) proves

```math
\mathrm{Eval}\longleftrightarrow\mathrm{Actuality}+\mathrm{ND}_t,
\qquad
\mathrm{ND}_t+\mathrm{BC}_{tt}\longrightarrow\mathrm{Eval}.
```

The separation formula supplies BF at $`t`$. If every $`Fp=\top`$, every qualified observer accepts each instance and therefore accepts its universal quantification. It also accepts Top. Separation identifies the universal proposition with Top.

Eval gives ND at $`t`$. The established implications ND at $`t`$ + BF at $`t`$ ⇒ ☐ND at $`t`$ ⇒ C5 now apply. Actuality supplies a true atom $`a`$. Its canonical evaluator

```math
E_a(p)=\Box(a\to p)
```

is correct and, under C5, qualified at every finite type list. Atomhood gives the Boolean laws and endpoint values; BF and CBF give quantifier preservation. Necessary BF, persistence of atomhood and Intensionality give the whole-operation identities. This is the [established principal-atom construction](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §3; it requires no global Atomicity.

For each separator $`O`$ qualified at $`t`$, the composite $`E_a\circ O`$ has endpoint values, is qualified at $`t`$, and has the same current truth profile as $`O`$. Thus we have endpoint separation at $`t`$ with the single list $`\{t\}`$.

## 2. The diagonal produces atoms everywhere

Given $`d\ne\bot`$, choose an endpoint separator $`B`$ with $`Bd=\top`$, and set

```math
b_B=\forall p^t\, .\,(Bp\to p).
```

Endpoint fixing gives $`B(Bp)=Bp`$. Quantifier and Boolean preservation therefore give $`B(b_B)=\top`$, so $`b_B\ne\bot`$. Necessary universal instantiation gives $`b_B\le(Bp\to p)`$. If $`Bp=\top`$, then $`b_B\le p`$; otherwise $`B(\neg p)=\top`$, so $`b_B\le\neg p`$. Thus $`b_B`$ is an atom, and $`Bd=\top`$ gives $`b_B\le d`$.

We have Atomicity at $`t`$. Together with C5, the principal-atom construction and Functionality give full End.

Conversely, End supplies C5 + Atomicity at $`t`$, hence Actuality, Eval and Boolean Completeness, as well as the required separation formula. This proves both equivalences.

## 3. Related finite presentations

The same constructions give

```math
\mathrm C+\mathrm{BF}_t+\mathrm{Plenitude}_{t,t}
\quad\equiv\quad
\mathrm{C5}+\mathrm{Actuality}
\quad\equiv\quad
\mathrm C+\mathrm{ND}_t+\mathrm{BF}_t+\mathrm{BC}_{tt}.
```

Plenitude at $`t,t`$ realizes the unique endpoint output specified by current truth, giving Eval. The converse follows from the evaluator's explicit graph-realization construction.

Over C5, the existing evaluator/Actuality/completeness/Plenitude cluster also includes the $`tt`$ instances of Rigid, Persistent, Weak Rigid and Gallin Extensional Comprehension, as well as their full schemas. A $`tt`$ witness coextensive with truth has necessary true values; its diagonal witnesses Actuality. Conversely the canonical evaluator supplies full rigid coextensions. These are finite presentations and common proofs of established global connections.

One immediate representation consequence is that pure Maximalism excludes Eval: Eval supplies ND at every type, and the native Max + ND incompatibility applies. This does not settle Max + ordinary OS.

## Sources

New finite assembly and refinements: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`). The source is §5 of the bridge proof, with §§2–4 and 8 for the connected statements; [source hashes](../evidence/source-manifest.json).

The substantive local evaluator and atom arguments are prior results, assembled here with a single separation list. Native background is Bacon–Dorr, *Classicism*, 16 May 2023 draft: Proposition 2.4, p. 23, for ND + BF; Propositions 2.5–2.6, pp. 25–26, for atomic propagation; §2.3, p. 33, for the boxed-Plenitude package; §2.6, p. 41, for Max + ND. The [evaluator proof](endpoint-evaluators-and-comprehension.md) retains the comprehension attributions and direct constructions.
