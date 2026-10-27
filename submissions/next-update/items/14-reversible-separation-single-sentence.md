# Reversible separation has a single-sentence formulation

**Contribution:** Equivalent definition of full Rev over C, with one preservation law and one separation sentence.

Different unary propositional operations can be distinguished by conjunction-preserving involutions. Put $`I:=\lambda p\, .\,p`$ and

```math
K(E):=\bigl((\lambda p,q\, .\,E(p\land q))=(\lambda p,q\, .\,Ep\land Eq)\bigr)
\land E\circ E=I
```

Over C, full Rev is equivalent to

```math
\forall X,Y^{tt}\, .\,
\bigl[\forall E^{tt}\, .\,K(E)\to\forall p^t\, .\,(E(Xp)\leftrightarrow E(Yp))\bigr]
\to X=Y
```

The sentence first yields Functionality at tt and BF at t. Reversibility and equality substitution give ND at t, hence C5. Quantifiers are then admitted-range infima, so the same automorphisms preserve every quantifier. Functionality lifts separation to every relational type. The converse uses the established involutive normalization of Rev.

The [direct group representation](18-reversible-group-semantics.md) uses these admitted automorphisms to represent every Rev model without enlarging its domains.

This removes all quantifier clauses and the inverse existential from the qualification. The tt separation scope is essential to this proof. The [full proof](../proofs/reversible-separation-single-sentence.md) also gives the admitted inverse-pair variant. The [invariant-family characterization](12-reversible-family-realization.md) supplies a complementary modal interpretation.

New characterization: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`).

**Proof length:** Short (770 words in the linked proof; imported dependencies excluded).
