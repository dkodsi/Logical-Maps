# The probability type ceiling without a choice of atoms

22 October 2026. Ordinary mathematical refinement by OpenAI Codex; direct source `misc`. No independent or formal verification claim. Original: [faithful probability, §§7–8](../notes/faithful-probability-countable-worlds.md#7-type-local-factorization-probability-on-individual-state-events).

Use B₀=C+□Plenitude+quantified Infinity_e and the explicit choice-free internal mathematics of [finite-fibre probability](choice-free-faithful-probability.md). Write Fin(X) for bijectivity with an initial segment of N=N_e, and Cuf(X) for existence of a finite-fibre graph X→N. All powersets below consist of **admitted** subsets, not all external subsets. No Choice is assumed.

## 1. A reusable finite-fibre Cantor lemma

**Lemma.** In the interpreted extensional mathematics,

    Cuf(P(X)) iff Fin(X).                                    (1)

The forward implication is the important one. A singleton embedding X→P(X) pulls the labelling back to a finite-fibre map ℓ:X→N. Suppose X were not finite. The range S of ℓ must be unbounded in N: a bounded range would express X as a finite union of finite fibres, which is finite by internal induction. The nonempty fibres can therefore be indexed increasingly:

    s₀ = min S,           sₙ₊₁ = min {s∈S : s>sₙ}.

These are unique least-number definitions. Finite recursion followed by its unique-history graph supplies the admitted sequence; no choice from the fibres occurs. Let D_n=ℓ⁻¹(s_n). These are disjoint nonempty finite blocks.

For an admitted subset U⊆N define

    J(U) := {x∈X : ∃n∈U, ℓ(x)=s_n}.

Comprehension makes J admitted, and it is injective: if U,V differ at n, any member of the nonempty D_n distinguishes J(U),J(V). This is one existential witness for a comparison, not a simultaneous choice of a point in every block. Pulling the assumed finite-fibre labelling of P(X) back along J gives a finite-fibre labelling L of P(N).

There is a definable strict total order on P(N): compare distinct U,V at their least differing number and put the one with bit 0 first. The least number exists by internal induction, and the usual first-difference argument proves transitivity. Thus **each finite L-fibre has a canonical order**, although X itself had no chosen order. No well-order of all of P(N) is asserted or needed.

Assign U the pair consisting of L(U) and the number of elements of its L-fibre preceding it in this order. Finite counting and pairing give an admitted injection P(N)→N. This contradicts the internal Cantor diagonal. Explicitly, for an injective graph I(U,n), define

    f(n)(k) iff ∃U (I(U,n) ∧ U(k)).

An unused n yields the empty set, and at a used n the value is its unique preimage. Hence f enumerates all admitted subsets of N. Comprehension supplies {n:¬f(n)(n)}, contradiction. This proves Fin(X). The reverse direction of (1) follows from the finite-powerset induction. ∎

All inductions and finite counts in this argument are internal; s_n and the size of a fibre may be externally nonstandard. The proof replaces the old use of Choice to obtain a sequence of distinct atoms by a sequence of **nonempty finite blocks**, which is uniquely indexed and requires no selection within a block.

## 2. Complete atomic Boolean fields

For a represented complete atomic Boolean algebra A with atom field At(A),

    x ↦ {a∈At(A):a≤x}

is an admitted bijection A→P(At(A)). Injectivity is atomicity. For surjectivity, take the represented join of the given subset of atoms; the atom–join lemma identifies exactly its atoms. All these constructions use comprehension and unique-value graphs, not Choice.

Equation (1) therefore gives

    Cuf(A) iff Fin(At(A)) iff Fin(A).                         (2)

For the second equivalence, one direction uses the subset inclusion of atoms; the other uses the finite-powerset description. Atomicity and represented completeness are hypotheses of (2). It is not asserted for arbitrary Boolean algebras with missing joins.

## 3. The state criterion at an arbitrary fixed relational type

The finite-fibre probability theorem applies to any relational Boolean algebra B_τ. Under B₀ the [atom normal form](atom-normal-form.md) gives the admitted bijection

    At(B_τ) ≅ W × D_σ₁ × … × D_σₖ,
    τ=σ₁…σₖt.                                               (3)

Here D_σ is the entire current domain of the original type σ. The representation uses literal equality, not a quotient of current extensions. All its BF/ND hypotheses follow from the retained boxed Plenitude.

A finite product of nonempty fields has a finite-fibre numerical labelling iff each factor does. Fix one element in each of the finitely many other factors for the forward embeddings. For the reverse implication pair their labels; a label fibre is a finite product of finite fields and is finite by internal induction. Only finitely many default elements are chosen, not a choice function on an infinite family.

Consequently

    faithful probability on B_τ
      iff Cuf(W) and Cuf(D_σ₁) and … and Cuf(D_σₖ).            (4)

The state may be completely additive. This removes boxed Functional Choice from the original factorization, replacing injections by the exact choice-free finite-fibre condition. For finite individual arities, (4) gives Cuf(W)∧Cuf(D_e), as before with the appropriate weaker countability notion.

## 4. The original ceiling and its single-instance obstruction

At tt, (4) gives Cuf(W)∧Cuf(D_t). The current D_t is a complete atomic Boolean algebra, so (2) makes it internally finite, and then W is finite. Conversely finite W makes D_t finite by its atom representation; the finite atom field W×D_t has a normalized counting state. Thus, already over B₀,

    faithful probability on B_tt iff Fin(W).                 (5)

No chosen countable sequence of worlds or numerical copy in the world field is needed.

More generally let σ be relational. A state on B_(σt) makes D_σ Cuf by (4), hence **finite** by (2). Its atom field (3) is then finite, so W and every argument domain of σ are finite. Conversely those finite domains make At(B_σ), then D_σ, then At(B_(σt)) finite, giving a counting state. This is an exact recursive ceiling with represented, internal finiteness throughout.

In particular,

    faithful probability on B_((et)t)
      iff Fin(W) and Fin(D_e).                               (6)

The right side is incompatible with the retained quantified Infinity_e. Therefore the **single event-type instance (et)t** is already impossible over B₀. An all-relational-type state schema is not needed for the contradiction. The original stronger-background argument already isolated this instance; the improvement is removal of Choice and the direct finite-fibre proof, not a new discovery of that event type. In (6) the event algebra's elements are properties of individual properties; its atoms are W×D_et. This must not be confused with the lower event algebra B_et, whose atoms are W×D_e and whose state can coexist with infinite individuals.

## Dependency audit and sources

The original §8 used full Choice to select infinitely many distinct worlds or individuals. That selection has been removed, not hidden: the finite-fibre Cantor lemma uses finite blocks, a least-number sequence, and a canonical order only on subsets of N. The retained requirements are the core interpretation, quantified Infinity_e, comprehension/finite recursion, and represented atomic completeness. No external-standardness or full-powerset assumption is introduced.

Sources: original `faithful-probability-countable-worlds.md`, §§7–8; original `structural-world-representation.md`, §§4 and 15; and the preceding refinement notes. These are unpaginated local research sources. The finite-fibre Cantor argument, the choice-free ceiling, and the single-instance obstruction are proved here. No new model or database result is asserted.
