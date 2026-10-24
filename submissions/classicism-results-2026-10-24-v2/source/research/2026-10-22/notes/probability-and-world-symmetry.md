# Faithful probability necessarily breaks infinite world symmetry

Research addendum, 22 October 2026 (`misc`). Background and internal real/number coding are exactly those of `faithful-probability-countable-worlds.md`: C+boxed Functional Choice plus quantified Infinity_e. The symmetry theorem is `represented-world-permutations.md`. No external-standardness, full-powerset, or literature-novelty claim.

Independent mathematical audit: the choice lane checked both arguments on 22 October 2026, including internal finite/Archimedean reasoning, fixed real outputs, and the distinction between operation-term definability and a description using designated current truth. This is an AI-agent audit, not a named-human check or formal verification.

## 1. Symmetry-invariant faithful probability is exactly finite-world probability

Call a faithful real state μ invariant if μ(F_P(p))=μ(p) for every admitted world-permutation graph P, where F_P is the induced propositional automorphism. It suffices to require this for the definable transpositions of pairs of atoms.

**Theorem.** Such an invariant faithful state exists iff the atom-world field W is internally finite. When it exists it is uniquely the normalized counting state

    μ(p)=number of atoms below p / number of all atoms.

For the forward direction, a transposition of atoms a,b sends a to b. Invariance therefore gives μ(a)=μ(b). Choose an atom a; its common weight c is positive by faithfulness. The internal Archimedean theorem gives a positive n with 1/n<=c. The finite-additivity threshold argument in the probability note shows that at most n atoms can have weight at least 1/n. Since every atom does, W is finite.

Conversely if W has finite nonzero cardinality m, every proposition is the finite join of its atoms. The displayed counting state is represented by ordinary core comprehension and finite counting, is positive on nonzero propositions, and is invariant under every represented permutation. Any invariant faithful state assigns a common weight c to each atom; finite additivity gives mc=1. Finite decomposition of p then determines its value uniquely. These are internal finite inductions, valid even when m is not externally standard.

Thus the faithful probability principle compatible with infinitely many worlds necessarily selects an asymmetry among those worlds. This conclusion concerns invariance of one state, not the existence of a family of states closed under permutations.

## 2. A finite-parameter term cannot define infinite-world faithful probability

Use the original hereditary rigid mathematical core over individuals and Boolean endpoints. Its represented Dedekind real codes are fixed pointwise by the lifted world permutations. Let μ be a real-valued operation denoted by a pure lambda term with finitely many propositional parameters p_1,...,p_n and any finite tuple of parameters in this original hereditary core.

Suppose μ is a faithful state on all propositions. Partition the worlds into the finitely many Boolean cells of the p_i. Any transposition of two atoms in one cell fixes all the p_i, and the full lifted automorphism fixes every core parameter. The pure-term substitution theorem therefore fixes the denotation of μ. Its output μ(a) is a core real code, hence is also fixed by the automorphism. Application preservation gives

    μ(a)=μ(b)

for any two atoms a,b in the same cell. Every nonempty cell therefore has a single positive atom weight. The Archimedean threshold argument bounds the number of its atoms by an internal natural number. The union of the finitely many cells is internally finite. Hence W is internally finite.

Consequently, in any infinite-world model of the background, no faithful state can be denoted by such a finite-parameter pure term, even when a faithful state exists. In particular this applies in the full countable-world model with its geometric probability. A faithful state's denotation must carry intensional information beyond finitely many proposition names and ordinary core mathematical parameters.

This is a TERM-definability statement. A unique description using current truth is not automatically a term and need not be preserved by an automorphism that moves the designated truth point. Likewise an arbitrary pure graph formula is not covered merely because its CURRENT extension happens to be a functional graph; an operation term, or a graph whose membership is suitably invariant/bivalent, is needed. The proof uses literal application preservation and the fact that each output real lies in the fixed original core.

The obstruction is slightly weaker than the atom-selector obstruction: atom choice forces every nonzero parameter cell to be a singleton, whereas a faithful state forces every such cell merely to be finite. Both are exact consequences of the same internal homogeneity, but they should not be conflated.
