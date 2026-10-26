# Classical cores from logical observers

**Contribution:** Canonical classical cores over C; mathematical inheritance and recovery theorems.

A single endpoint-valued logical observer determines a classical, extensional Henkin core already over **C**. It preserves the Boolean operations and every typed quantifier as whole operations. A short diagonal argument derives $`E\circ E=E`$ from the Boolean laws, the quantifier law at t and endpoint-valuedness.

Normalize every relational type recursively:

```math
r_e(x)=x,\qquad r_t(p)=E(p),\qquad
r_{\sigma\tau}(f)=\lambda x^\sigma.\,r_\tau(f(r_\sigma(x))).
```

Keep the fixed relational objects and identify individuals when $`E(a=b)=\top`$. The notation at e introduces no individual-valued operation. All eligible observers give the same individual quotient and canonically isomorphic pure logical cores. Individual constants are preserved; named relations require compatibility of their normalized interpretations. **Functional Choice and Boolean Completeness descend instancewise.**

[Full proof over C](../proofs/endpoint-classical-cores.md) · [Why the individual quotient is needed](../proofs/endpoint-core-individual-quotient.md).

The [C5 construction](../proofs/observer-classical-cores.md) also permits nonendpoint proposition images and retains the original individuals. In that setting:

- **Quantified Infinity at e has an exact observed value:** $`\mathrm{Infinity}_e^c=E(\mathrm{Infinity}_e)`$. Thus ☐Infinity at e descends. Endpoint cores have only two propositions, so this does not transfer Infinity at t.
- **Observed Relational Choice and Transversal Choice descend**, including individual outputs. Their necessary instances therefore descend; merely current instances require the stated observation conditions.
- **Crisp relational structures on individuals retain their first-order theories.**

An endpoint core is **full standard exactly when its predicate Boolean algebras are externally complete**; joins of every external family of singleton predicates suffice. This criterion concerns the constructed classical core and also applies after the bare-C construction. Internal Functional Choice, Boolean Completeness and quantified Infinity alone do not imply fullness. A full core with infinitely many individuals has standard Frege arithmetic and full second-order arithmetic. [Proofs](../proofs/observer-core-mathematics.md).

Over C5, separating endpoint observers evaluate ordinary relational second-order formulas in **one common classical Henkin structure**, with varying joint interpretations of relation parameters. Their normalizations faithfully recover relations on individuals. At types with relational arguments, full recovery instead retains the original arguments before observing outputs. [Exact recovery and modal tests](../proofs/observer-core-recovery.md).

**Proof length:** Long (about 8,800 words across the linked proofs). The substantial arguments establish extensionality inside the core over C, prove the whole-operation comparison identities, and transport the impredicative natural-cardinality definition.

New construction and connecting arguments: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`). Earlier core, world-slice and representation results retain their attribution in the proofs. This is a model-theoretic supplement; no new native principle is proposed.
