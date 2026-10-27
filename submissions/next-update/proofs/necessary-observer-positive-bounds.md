# Positive bounds under necessary observer separation

Over C5, necessary separation makes each supported Choice, completeness and comprehension instance modally constant. For CH and first-order analysis at a fixed carrier, separately possible unary, binary and ternary Rigid Comprehension suffice. The [finite-support symmetric construction](../../integration-register/proofs/observer-analysis/necessary-os-ch-inaccessible-countermodel.md) refutes general CH propagation under C5 + ☐OS, starting from a strongly inaccessible cardinal. Its fixed real field is persistent and necessarily complete for nonempty bounded admitted subproperties.

## 1. From reflection to modal constancy

Suppose a finite proof establishes the C theorem

```math
K\land S\to(A\to\Box A),
```

where C5 supplies $`\Box K`$. Necessitating this discharged theorem and assuming $`\Box S`$ gives $`\Box(A\to\Box A)`$. Hence $`\Diamond A\to\Diamond\Box A\to\Box A`$ by S5. Reflexivity gives the converse implications:

```math
\mathrm{C5}+\Box S\ \vdash\
(\Diamond A\leftrightarrow A\leftrightarrow\Box A)
\land(\Box A\lor\Box\neg A).
```

The final disjunction follows by splitting on $`A`$: if false, $`\Diamond A\to A`$ gives $`\neg\Diamond A`$. Only the closed theorem is necessitated.

The [witness-transport proofs](observer-witness-transport.md) and [comprehension proof](observer-comprehension-reflection.md) supply the following instances, where $`S=S_{t,\Delta}`$:

| Instance $`A`$ | Qualification list $`\Delta`$ |
|---|---|
| Boolean Completeness at relational $`\tau`$ | $`\{\tau,\tau t\}`$ |
| Plenitude or Functional Choice at $`\sigma,\tau`$ | $`\{\sigma\tau t,\sigma,\tau,\sigma\tau\}`$ |
| Rigid, Persistent or Gallin Extensional Comprehension at $`\tau=\sigma_1\cdots\sigma_nt`$ | $`\{\tau,\sigma_1,\ldots,\sigma_n\}`$ |

Thus C5 + ☐OS makes each such closed instance modally constant. This does not treat a full schema as an object-language conjunction.

## 2. Possible finite rigidity and mathematical propagation

Fix a carrier type $`\sigma`$, put $`\rho_k=\sigma^kt`$ for $`k=1,2,3`$, and let $`\Delta_\sigma=\{\sigma,\rho_1,\rho_2,\rho_3\}`$. Write

```math
U_{\sigma,\varphi}:=\forall\mathfrak R\, .\,
(\mathrm{Real}_\sigma(\mathfrak R)\to\varphi(\mathfrak R)).
```

For CH, or a first-order ordered-field sentence with the natural-numbers predicate,

```math
\mathrm{C5}+\Box S_{t,\Delta_\sigma}
+\bigwedge_{k=1}^{3}\Diamond\mathrm{RigidComp}_{\rho_k}
\ \vdash\ U_{\sigma,\varphi}\to\Box U_{\sigma,\varphi}.
```

Section 1 makes each separately possible comprehension instance necessary. A common possible world of witnesses is not assumed.

The [established structural proof](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/writeups/c5-and-necessary-rigid-comprehension-imply-second-order-analytic-necessitism.md) needs exactly these three comprehension types for the selected targets. Unary comprehension rigidifies the carrier, natural numbers and admitted subproperties used in completeness and leastness; binary comprehension rigidifies order; ternary comprehension rigidifies the field-operation graphs. Represented unary and binary powers are the properties of rigid relations supported on the rigid carrier. Their rigidity follows from C5 and BF; no family-type comprehension is required.

For detail, start at a possible real structure and take these rigid coextensions there. S5 transfers rigidity, and first-order facts about the resulting rigid structure are necessary. At any other world, replace a nonempty bounded subproperty by a rigid coextension, transfer its bounds back to the original real structure, obtain its supremum there, and transfer that least-upper-bound fact forward. The least-inductive-property argument is analogous. This produces a necessarily real rigid structure and the represented relations needed for CH.

The existence argument is essential. If a real structure is possible, the construction supplies one currently; the existing invariance theorem and current $`U_{\sigma,\varphi}`$ then select the correct necessary alternative. If no real structure is possible, the universal target is necessarily vacuous. Completeness throughout concerns **nonempty bounded** admitted subproperties.

Consequently a counterexample under C5 + ☐OS at this carrier must make at least one of those three Rigid Comprehension instances necessarily false.

## 3. One possible evaluator reaches the endpoint theory

Over C5 + $`\Box S_{t,\{t\}}`$, the [one-atom theorem](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/necessary-separation-and-atoms.md) and the [finite endpoint presentation](endpoint-separation-finite-presentation.md) give

```math
\mathrm{End}\ \longleftrightarrow\
\text{there is an atom}\ \longleftrightarrow\
\Diamond\mathrm{Actuality}\ \longleftrightarrow\
\Diamond\mathrm{Eval}.
```

The possible condition may equally be Boolean Completeness at $`tt`$, Plenitude at $`t,t`$, or Rigid Comprehension at $`tt`$. Their current versions are equivalent as well.

Indeed an atom is possible and persists under C5, giving possible Actuality. Necessitate the finite implication from C5 + $`S_{t,\{t\}}`$ + Actuality to propositional Atomicity. Necessary separation gives possible Atomicity; its C5 persistence and S5 make it current. The endpoint construction follows. Conversely End supplies all the stated current conditions and hence their possibilities. The evaluator equivalences transfer each other possible premise to possible Actuality.

Possible Functional Choice at $`t,t`$ is also sufficient, since it gives possible Plenitude at $`t,t`$. An equivalence with that Choice premise is not asserted.

## 4. A useful model-class bound

Suppose at every object of a symmetric action model each current structure has a finite common pin $`S`$, and every external relation invariant under the stabilizer of $`S`$ is an admitted current extension. Then every admitted real structure is a full real structure of the ambient universe.

The stabilizer acts by ordered-field automorphisms and fixes every standard numeral. The external standard-natural subset is therefore invariant and admitted. If bounded, its supremum minus one would also bound it, a contradiction. The field is Archimedean. Rational density then forces each stabilizer automorphism to fix every real point: a rational between a point and its image contradicts order preservation. Every external relation on the carrier is now invariant and hence admitted. Native completeness becomes full Dedekind completeness, and the real structure is the ambient real field with all its relations.

For a connected model satisfying this admission hypothesis over one ambient universe, CH and first- and second-order analytical noncontingency follow. The existing finite-block counterexample to C5 + ☐OS ⇒ Rev satisfies this hypothesis; its pure-choice contingency is not a CH counterexample. The admission assumption is stronger than ordinary Henkin closure and is not inferred from ☐OS.

## Sources

New modal promotion, finite-scope combination and invariant-extension argument: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), §§1–4 above; the [manifest](../evidence/source-manifest.json) records the source proofs and the finite-scope audit.

The underlying rigid-structure theorem retains its attribution to Zachary Goodsell's connection and the proof by Claude Fable 5.1, prompted by Zachary Goodsell, after Bacon's *Could the truths of mathematics have been different?*, Corollary 5.1. The new contribution is the exact finite comprehension scope and its weakening to separate possibilities. The [remaining question](../PENDING.md) is stated independently of these sufficient bounds.
