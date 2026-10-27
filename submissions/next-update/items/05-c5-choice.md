# Vicinity closes the Relational Choice–Transversal Choice gap

**Contribution:** New implication and progress on an existing question.

```math
C+\mathrm{Vicinity}+RC_{(\sigma t),\sigma}
\quad\Longrightarrow\quad TC_\sigma.
```

This holds at every admitted type σ, including e. Choice is unboxed; Boolean Completeness and Actuality are not premises. Unboxed NDₜ also suffices in place of Vicinity. At σ=t the required Choice instance is RC_(tt,t), not RC_(t,t).

Consequently **RC, TC, Zorn and Well-Ordering coincide over C + Vicinity** by existing connections. The bare-C question `relational-choice-r-implies-transversal-choice-r` remains open and retains its statement, certificate and attribution.

## Proof and credit

The [proof](../../integration-register/proofs/vicinity-relational-choice-transversals.md) rebases the [supported C5 interpretation](../proofs/vicinity-supported-interpretation.md) to the entire original σ carrier. It transfers the required Choice instance, applies the [C5 transversal theorem](../proofs/c5-relational-choice-implies-transversal-choice.md), and brings the transversal back to the original carrier.

New connecting arguments: OpenAI Codex, prompted by Daniel Kodsi, 25–26 October 2026 (`misc`). The shared construction extends Christopher Sun's recorded Vicinity argument; the proofs retain the original credits.

**Proof length:** Long (about 5,100 words across the linked proofs, counting the shared construction once).

## Database patch

[Patch 05](../patches/05-c5-choice.patch) adds `vicinity-relational-choice-implies-transversal-choice` with its proof and shared interpretation. It retains `c5-relational-choice-implies-transversal-choice` as a supporting theorem, and links the stronger positive case from the unresolved bare-C record. The NDₜ corollary is derived, not duplicated.

[Exact files and dependencies](../evidence/patch-manifest.json).
