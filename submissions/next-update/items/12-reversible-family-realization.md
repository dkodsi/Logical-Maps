# Reversible separation: supporting characterization

For the simpler defining sentence, see [conjunction-preserving involutions](14-reversible-separation-single-sentence.md). The characterization here describes Rev's modal witness behavior.

**Contribution:** Equivalent formulation and supporting model.

Over C5, Rev is equivalent to this condition: **every admitted endpoint-valued family of propositions closed under reversible logical observers has a true member whenever it has a possible member.** The condition is one finitary sentence and characterizes full relational Rev.

For the converse, the proof uses the admitted orbit predicate

```math
X_r(q):=\exists E^{tt}\, .\,A(E)\land q=Er,
```

where $`A(E)`$ requires a logical observer qualified at $`t`$ with an admitted qualified two-sided inverse. A true member of this family provides a reversible separator. The [complete formulation and proof, §3](../proofs/reversible-invariant-family-realization.md#3-an-exact-modal-witness-principle-for-invariant-families), also give the equivalent uniform noncontingency statement. This is a formulation of Rev using its observers, not an additional principle.

## Supporting comparison

The [component-shift model with fixed individuals](../proofs/fixed-individual-component-shift.md) satisfies

```math
\mathrm{C5}+\Box\mathrm{SplitMono}+\Box\mathrm{EPNC}_e+\neg\mathrm{Rev}.
```

SplitMono requires qualified left inverses. Here $`\mathrm{EPNC}_e`$ is noncontingency for pure formulas with individual and endpoint-valued first-order relation parameters $`e^nt`$, $`n\ge1`$; bound variables may have any admitted type. Thus reversible symmetry adds something beyond necessary recoverable observation and this parameter noncontingency. The construction permits any nonempty fixed individual domain; no object-language Infinity verdict is claimed.

Allowing unrestricted endpoint-valued parameters already at $`(et)t`$ instead forces Extensionality. This explains the stability restriction in the characterization; see [§4](../proofs/reversible-invariant-family-realization.md#4-why-endpoint-valuedness-alone-is-too-strong-at-higher-types).

Include the characterization with Rev's proposed equivalent forms, and the comparison as model evidence. New arguments: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`); the model proof retains the construction's earlier attribution.

**Proof length:** Long (4,279 words across the two linked proofs; imported dependencies excluded). Preserving the full proposition-generated hierarchy while replacing individuals is the more involved argument.
