# Endpoint separation and Infinitary Comprehension: full representation certified

**Lean certified:** λ-free H, with its stated theorem-only logical necessitation, full typed endpoint-valued observer separation and actual Infinitary Comprehension characterize the full standard relational hierarchies.

The representation preserves the original typed carriers, application, current truth and complete values of original formulas, including parameters and infinitary subformulas. The converse is proved in the same native syntax. C, Intensionality, ND and fullness are derived; the syntax interpretation and original-type grounding are proved rather than assumed.

| Declaration | Certified result |
|---|---|
| `HOriginalTheorem.full_standard_representation` | Full standard representation from the original closed-type H, endpoint-OS and IC premises. |
| `HOriginalTheorem.original_carriers_preserved` | Preservation of every original typed carrier and application. |
| `HOriginalTheorem.original_syntax_interpretation` | Preservation of complete values of original formed formulas. |
| `HStandard.full_standard_satisfies` | Full standard hierarchies satisfy the same native schemas. |

The [statement and proof](../proofs/endpoint-ic-representation.md) specify the infinitary language and observer qualification. The infinitary box/meet law is also derived from logical necessities and recovered K.

The combined audit checks 42 sources and compiled artifacts, with 41 principal axiom reports containing only `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or custom axioms. Source snapshots, artifact hashes, compiler identity and saved reports were reconciled during collection, without recompiling.

- [Full certificate and exact assumptions](../certificates/endpoint-ic-full.json)
- [Exact audited source closure](../certificates/endpoint-ic-full-sources.zip)

The certificate uses Lean's classical metatheory. It does not certify the separate choice-free ZF argument or completeness for an infinitary proof calculus. The earlier 137-source certificate remains unchanged.

**Proof length:** Medium (1,155 words in the linked exposition; imported dependencies excluded).

Mathematics and Lean formalization: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`).
