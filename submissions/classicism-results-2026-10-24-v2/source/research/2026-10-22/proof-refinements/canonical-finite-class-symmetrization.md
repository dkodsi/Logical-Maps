# Canonical symmetrization over finite world classes

22 October 2026. Ordinary mathematical refinement by OpenAI Codex; direct source `misc`. No independent or formal verification claim. This strengthens [probability under world partitions](probability-under-world-partitions.md), refining the original [world-symmetry theorem](../notes/probability-and-world-symmetry.md).

Use B₀=C+□Plenitude+quantified Infinity_e, with the choice-free internal mathematics and graph conventions of [finite-fibre probability](choice-free-faithful-probability.md). Let R be a represented rigid equivalence on the atom field W. The represented permutations considered below fix every R-class setwise.

## 1. Averaging removes the enumeration

Suppose a faithful finitely additive probability μ is given and every R-class is internally finite. Put c(a)=μ(a), and define

    c_R(a) := [Σ(b∈[a]_R)c(b)] / |[a]_R|.                     (1)

This is a unique finite sum and a positive finite cardinality, so the graph of c_R is admitted without choosing class representatives, enumerations, or numerical labels. It is positive and constant on each class.

For any finite K⊆W, its saturation R[K] is finite. This is proved by internal induction on K, taking at each step the union with the represented finite class of the added atom. No family of witnesses is chosen: the classes themselves are defined by R. On each complete finite class C,

    Σ(a∈C)c_R(a) = Σ(a∈C)c(a).

Consequently

    Σ(a∈K)c_R(a) ≤ Σ(a∈R[K])c_R(a)
                  = Σ(a∈R[K])c(a) ≤ 1.                     (2)

The last inequality follows from finite additivity of μ on distinct atoms. The finite-budget lemma therefore defines completely additive atomic sums V_c and V_(c_R).

Finite R-saturated sets are cofinal among finite atom subsets: K is contained in R[K]. On such saturated sets the two sums agree. It follows, by taking suprema, that

    V_(c_R)(⊤) = V_c(⊤) = μ_at(⊤) > 0.                       (3)

Define the canonical symmetrization

    S_R(μ)(p) := V_(c_R)(p) / μ_at(⊤).                       (4)

It is faithful and completely additive. Every represented class-preserving permutation preserves c_R and bijects the finite atom subsets below p with those below its image F_P(p). Reindexing the finite sums proves invariance of (4). No Choice or countability argument occurs.

## 2. Preserved mass, uniqueness, and idempotence

Call p R-saturated when a≤p and R(a,b) imply b≤p. For a finite K below such p, R[K] is also below p. The same cofinality argument used in (3) gives

    V_(c_R)(p) = μ_at(p),
    S_R(μ)(p) = μ_at(p)/μ_at(⊤).                              (5)

Thus the construction preserves the normalized atomic mass of every saturated event. In particular a finite class C, regarded as its finite join, receives μ(C)/μ_at(⊤). If μ was already completely additive, then μ_at=μ and the construction preserves its exact mass on every saturated event.

There is exactly one completely additive class-invariant probability with those class masses. Transpositions make its individual atom masses equal within each finite class, so its value at a∈C must be

    μ(C) / (|C| μ_at(⊤)) = c_R(a)/μ_at(⊤).

A completely additive charge on an atomic algebra is determined by its atom masses, since each event is the represented join of its atoms. This proves uniqueness. Applying (4) again leaves the atom weights unchanged and the total atomic mass equal to 1, so S_R(S_R(μ))=S_R(μ).

This uniqueness statement uses complete additivity. An arbitrary finite-additive charge can have an additional nonzero remainder vanishing on every atom, and its masses are not determined by (1).

## 3. Exact invariant-state criterion without Choice

Over B₀, the following are equivalent:

* a faithful probability exists that is invariant under all represented class-preserving permutations;
* a faithful probability exists and every R-class is internally finite;
* W admits a finite-fibre numerical labelling and every R-class is internally finite.

In every case the invariant state can be chosen completely additive.

For the first implication, transpositions within a class force a common positive atom mass. Internal Archimedeanness supplies a positive numerical lower bound 1/n; finite additivity bounds that whole class by n elements. The second implication back to invariant existence is the explicit construction (4). The equivalence with the third condition is the choice-free probability theorem.

If countable Choice for finite fields is added, finite-fibre labelling becomes numerical countability and this recovers the earlier partition criterion. The earlier proof's geometrically weighted enumeration is therefore unnecessary even in its original stronger background.

For universal R the criterion gives exactly internally finite W and the normalized counting state. For equality R it gives canonical atomic regularization. For the finite pattern cells of finitely many propositional parameters it recovers the original finite-parameter obstruction, with its original term-definability and fixed-core-output qualifications intact.

## Dependency audit

The original partition refinement assumed F and used a numerical injection to construct an invariant state. Here boxed Functional Choice is removed, and a given state is symmetrized by a unique formula preserving its class masses. No choice assumption is moved into a representative-selection lemma. Finite-class counting, finite images, finite sums, the atom-sum supremum, and the represented world-permutation construction remain explicit dependencies. Existing joins are sufficient for the abstract argument; B₀ supplies all represented joins for the Classicism application.

Sources: `probability-and-world-symmetry.md`, §§1–2; `represented-world-permutations.md`, §§1–3; `canonical-atomic-probability.md`, §§1–3; and `choice-free-faithful-probability.md`. All are unpaginated local notes. Formula (4), its mass preservation, and the choice-free criterion are the argument of this note.
