# Database-owner guide: changes since 10-24 v2

This update supplements the [24 October v2 post](../classicism-results-2026-10-24-v2/README.md). The [results page](README.md) organizes the contributions by subject; the table below identifies their relationship to that post. [Already incorporated results](UPSTREAM.md) are separated from additions proposed here.

## From the earlier post to this update

| Family in 10-24 v2 | Contribution in this update | Database treatment |
|---|---|---|
| [Choice and completeness](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#choice-completeness) | [RC, TC, Zorn and Well-Ordering coincide over C5](items/05-c5-choice.md). [Propositional completeness with RC or Zorn makes Actuality equivalent to Vicinity](items/23-propositional-zorn-actuality.md). | New implications: patches 05 and 07. The earlier RC + all-type completeness theorem is already incorporated. |
| [Maximalism and Forcing Possibilism](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#forcing-possibilism) | [Strict FP is independent of pure Max](items/04-maximalism-forcing.md); [finite-collapse classification](items/06-finite-collapse.md) extends the earlier operation obstructions. | Model verdicts in patch 04; classification supplied as a proof supplement. |
| [Arithmetic and analysis](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#arithmetic-and-evaluation) | [Exact analytical strength of Max](items/07-analytical-shadow.md), [Functional Choice comparison](items/08-analytical-choice.md), and [standard actual mathematics without new necessities](items/22-classical-present-conservation.md). | Exact-strength and conservation theorems, with their separate scopes. The Max theorem supersedes the earlier proposed arithmetic equality. |
| [Structural principles and mathematical contingency](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#continuum-hypothesis-and-forcing) | [C5 + Functional Choice permits analytical contingency](items/03-analytical-contingency.md); [Choice and rigid comprehension do not force Atomicity](items/02-cloud-relational-choice.md). | Model construction and additional model verdicts: patches 03 and 02. |
| [Logical observers](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#logical-observers) | [OS shift semantics](items/15-observer-shift-semantics.md), [Rev group representation](items/18-reversible-group-semantics.md), [canonical classical cores](items/21-observer-classical-cores.md), and [witness transport](items/13-observers-and-necessary-choice.md). | Extensions and representation theorems; separate from the native implication patches. |
| [Endpoint separation and Infinitary Comprehension](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#lambda-free-endpoint-comprehension) | [Full representation and converse over λ-free H — Lean certified](items/20-endpoint-ic-certificates.md), preserving original typed carriers and formula values. | Stronger, complete certificate with its exact language and assumptions. |
| [Max + Atomicity](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#max-atomicity) | [Simplified proof — Lean certified](items/10-max-atomicity-certificate.md). | Certificate for the simplified proof of the existing result. |
| [Forcing Possibilism and Infinity](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#forcing-possibilism) | [Internal proof of FP ⇒ quantified Infinity](items/11-forcing-infinity-proof.md). | Alternative proof in patch 06; original theorem attribution retained. |
| [Integration records](../classicism-results-2026-10-24-v2/DATABASE-INTEGRATION.md) | [Source and explanation corrections](items/01-explanation-corrections.md) and [upstream reconciliation](UPSTREAM.md). | Patch 01 and reconciliation notes; previously incorporated results are not resubmitted. |

## Applying the database changes

The seven patches target upstream commit [`a89a5058`](https://github.com/zwlgzwlg/Logical-Maps/commit/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb), with paths relative to the repository root. Apply them in numerical order; patch 04 depends on patch 01. The [patch manifest](evidence/patch-manifest.json) lists exact target files, original blob IDs and dependencies. The [validation record](evidence/validation.json) includes application checks and proved-only consequence queries against that base.

Each linked contribution supplies its statement, proof, attribution and proposed action. Proof supplements and observer extensions have no native patch unless one is explicitly linked. The included patches do not replace the database with the dated research source snapshot.

Review [the current unresolved questions](PENDING.md) alongside [the 10-24 conjecture catalogue](../classicism-results-2026-10-24-v2/CONJECTURES.md). Special-case solutions retain the original question and its remaining scope.

The certificate entries identify exact declarations, source closures and saved verification evidence. Research certification is distinguished from certification of a native database statement. [Source provenance](evidence/source-manifest.json) and [review evidence](evidence/proof-reviews.json) retain those distinctions.
