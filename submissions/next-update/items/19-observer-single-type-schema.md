# A shorter OS schema

**Contribution:** Equivalent schema over C, together with a general obstruction to finite or bounded-type-order axiomatizations.

For every relational type $`\rho`$, require propositions to be separated by Boolean observers preserving quantification at $`e`$ and $`\rho`$. These instances together are equivalent to full OS.

The construction compresses any finite list of relational qualification types into

```math
\rho=(\sigma_1t)\cdots(\sigma_nt)t
```

Each $`\sigma_i`$ is a definable retract of $`\rho`$. Preservation of quantification descends along those retractions, so the **same observer** handles the entire list. The proof uses unconditional H equivalences and whole-operation identities; it needs no additional BF, C5 or Choice premise.

This reduces both the varying qualification list and the separation-output type. The [reduction proof](../proofs/observer-single-type-schema.md) includes the boundary for omitting individual quantification.

The type parameter must remain unbounded: OS has no finite equivalent axiomatization over C, nor an equivalent axiom set of uniformly bounded elaborated type order. This also applies to every theory between C + BF and C + OS, including BF, Functionality and Tractarianism. It concerns fixed-type axioms; finite stronger theories such as Rev or End can still imply OS.

The [direct Boolean-algebra proof](../proofs/observer-no-finite-basis-direct.md) constructs two models agreeing throughout any prescribed bounded-order fragment, with a higher failure of BF in one. In the [coherent-profile construction](../proofs/observer-term-closed-profile-models.md#8-henkin-leaves-and-the-exact-witness-condition), OS holds exactly when every available nonempty leaf predicate has an available witness. The [forcing proof](../proofs/observer-no-finite-basis.md) supplies an alternative route. Both work in ZFC without GCH or a countable-transitive-model assumption.

New reduction, models and axiomatizability results: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`).

**Proof length:** Long (4,685 words across the primary proofs; alternative proof and imported dependencies excluded).
