# Classicism update — 25–26 October 2026

An update to the [10-24 v2 post](../classicism-results-2026-10-24-v2/README.md). The [database-owner guide](DATABASE-HANDOFF.md) maps each family to the earlier post and identifies the proposed database actions.

Results and source patches against upstream [`a89a5058`](https://github.com/zwlgzwlg/Logical-Maps/commit/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb). Each linked entry identifies the contribution, proof and attribution. [Unresolved questions](PENDING.md) are separate.

## Database connections and corrections

| Contribution | Database change | Patch |
|---|---|---|
| [Vicinity + Relational Choice ⇒ Transversal Choice](items/05-c5-choice.md) | RC, TC, Zorn and Well-Ordering coincide over C + Vicinity; unboxed NDₜ also suffices. The bare-C question remains open. | [05](patches/05-c5-choice.patch) |
| [C5 + Functional Choice permits analytical contingency](items/03-analytical-contingency.md) | A constructible-ground Cohen model, retaining both quantified infinities and necessary CH. | [03](patches/03-analytical-contingency.patch) |
| [Strict Forcing Possibilism is independent of pure Max](items/04-maximalism-forcing.md) | Positive definable-root and negative pinned-root verdicts. | [04](patches/04-maximalism-forcing.patch) |
| [Vicinity and Actuality](items/23-propositional-zorn-actuality.md) | Atomicityₜ + Vicinity ⇒ Actuality. Under BCₜ with RC_(t,t) or Zornₜ, Actuality ⇔ Vicinity ⇔ a cofinal chain of proper persistent propositions. | [07](patches/07-propositional-zorn-actuality.patch) |
| [Choice and rigid comprehension do not force Atomicity](items/02-cloud-relational-choice.md) | A new Choice argument for the existing Cohen/lottery cloud family. | [02](patches/02-cloud-relational-choice.patch) |
| [Forcing Possibilism ⇒ quantified Infinity](items/11-forcing-infinity-proof.md) | Alternative internal proof of the existing theorem, preserving its attribution. | [06](patches/06-forcing-infinity-proof.patch) |
| [Explanation and source-status corrections](items/01-explanation-corrections.md) | Definable-root, Boolean-transfer, analytical and FP/CH corrections; no proved-result verdict withdrawn. | [01](patches/01-explanation-corrections.patch) |

Apply patches in numerical order from the repository root; 04 depends on 01, and 07 uses the shared construction in 05. Each includes its native write-up. [Files and dependencies](evidence/patch-manifest.json) · [Validation and question outcomes](evidence/validation.json).

## Further results about established principles

| Contribution | Main result |
|---|---|
| [Unrestricted analytical shadow](items/07-analytical-shadow.md) | Max's complete ordinary analytical consequences are those of the boxed-Plenitude package plus true Π⁰₁ arithmetic. |
| [Functional Choice comparison](items/08-analytical-choice.md) | Π¹₄ conservation, an explicit higher-level separator, and its conditional independence from Max. |
| [Standard actual mathematics without new necessities](items/22-classical-present-conservation.md) | A full standard core over any C model; standard relational second-order mathematics and current selection add no necessary consequences over disequality theories, including Max. |
| [Finite-collapse classification](items/06-finite-collapse.md) | Exactly which freely represented operation packages can occur under pure Max, including proposition-valued operations. |
| [Choice proofs and modal rigidity](items/17-choice-proof-simplifications.md) | Shorter boxed-Plenitude/Choice proof, finite-instance necessity of Functional Choice, and type-specific rigidity of Intensional and Modalized Relational Choice. |
| [Evaluators and comprehension](items/16-evaluators-and-comprehension.md) | Direct completeness and comprehension constructions; one propositional separation formula plus a correct evaluator gives full endpoint separation. |

The analytical metatheorems are supplied with proofs rather than native implication records. The Choice and evaluator entries distinguish new type-specific consequences from alternative proofs of established connections.

## Extensions and new directions

| Contribution | Main result |
|---|---|
| [Endpoint separation + Infinitary Comprehension](items/20-endpoint-ic-certificates.md) | Characterize full standard relational hierarchies over λ-free H, preserving original typed carriers and formula values. **Lean certified.** |
| [Shift models for C + OS](items/15-observer-shift-semantics.md) | Sound and strongly complete semantics with ordinary Henkin functions, quantifier intersections and admitted shifts; one fixed monoid suffices in a countable language. |
| [Classical cores from logical observers](items/21-observer-classical-cores.md) | Endpoint retractions give canonical classical cores already over C, inheriting Functional Choice and Boolean Completeness; exact fullness, mathematical-transfer and recovery results. |
| [Direct group models for C + Rev](items/18-reversible-group-semantics.md) | Every model has a group representation preserving its typed domains; inverse shifts give crisp equality and coherent higher-type transports. |
| [Rev from conjunction-preserving involutions](items/14-reversible-separation-single-sentence.md) | Over C, one separation sentence at type tt implies the full reversible logical-observer schema. Quantifier preservation follows. |

The [shorter OS schema](items/19-observer-single-type-schema.md) has an instance for each type of propositions or relations; its supporting proofs also explain why no finite fixed-type basis suffices.

[Witness transport and supporting observer results](items/13-observers-and-necessary-choice.md) connects the hierarchy to Choice and comprehension, including [positive bounds under ☐OS](proofs/necessary-observer-positive-bounds.md) for CH and analysis. The [invariant-family characterization of Rev](items/12-reversible-family-realization.md) supplies a complementary modal interpretation.

[Numerical stability, recursion and finite realization](items/09-numerical-operations.md) connects protected numerical cardinalities with admitted operations, gives higher-type recursion from one alternating bit, and characterizes operation realization on internally finite domains.

## Formalizations and evidence

The [simplified Max–Atomicity proof is Lean certified](items/10-max-atomicity-certificate.md), with the exact theorem, source archive and axiom audit.

[Already incorporated results and certificates](UPSTREAM.md) are distinguished from this update. The preceding package retains its [full catalogue](../classicism-results-2026-10-24-v2/CATALOG.md), [existing-result formalizations](../classicism-results-2026-10-24-v2/MAIN-RESULTS.md#previously-known-results-formalized) and [certificate manifest](../classicism-results-2026-10-24-v2/evidence/CERTIFICATES.json).

[Source hashes](evidence/source-manifest.json) · [Review evidence](evidence/proof-reviews.json). Proof length counts the linked exposition, excluding imported dependencies: short below 1,000 words, medium 1,000–4,000, long above 4,000.

Package integrity can be checked against [SHA256SUMS](SHA256SUMS) using the existing verifier:

```sh
python3 submissions/classicism-results-2026-10-24-v2/verify_package.py --root submissions/next-update
```
