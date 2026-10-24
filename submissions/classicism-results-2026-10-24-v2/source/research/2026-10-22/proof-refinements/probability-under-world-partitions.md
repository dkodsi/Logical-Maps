# Faithful probability under a represented partition of worlds

22 October 2026. Ordinary mathematical refinement by OpenAI Codex; direct source `misc`. No independent referee or formal verification claim. Original: [probability and world symmetry, §§1–2](../notes/probability-and-world-symmetry.md). Use the same F = C + □Functional Choice plus quantified Infinity_e and internal reals as that note.

## Exact extension of the symmetry theorem

Let W be the proposition atom field and R a represented equivalence relation on W in the extensional graph-coded interpretation. In the C presentation take its rigid graph. An R-preserving permutation means an admitted bijection P:W→W with R(a,P(a)) for every a: it fixes each R-class setwise. Let F_P be its induced Boolean automorphism, as constructed in [represented world permutations, §§1–2](../notes/represented-world-permutations.md).

The following are equivalent:

1. There exists a faithful finitely additive probability invariant under every represented R-preserving permutation.
2. There exists a faithful finitely additive probability whose atom weights are equal within each R-class.
3. W is internally N_e-countable and every R-class is internally finite.
4. There exists a faithful **completely additive** probability invariant under every represented R-preserving permutation.

Complete additivity has the represented-family meaning of [the finite-budget lemma](canonical-atomic-probability.md#2-one-finite-budget-lemma). It makes no external-fullness assertion. The theorem includes the original symmetry result by taking R universal, and ordinary faithful probability by taking R to be equality.

For an actual group action this is a finite-orbit criterion **only if its orbit equivalence is represented**. No orbit field is inferred merely from an externally specified collection of automorphisms. The theorem uses the explicitly given R and all its represented class-preserving permutations.

## Proof

**(1) ⇒ (2).** If R(a,b), their transposition is represented by the equality-defined graph, is R-preserving, and sends atom a to atom b. Invariance gives equal weights. In fact (2) is equivalent to invariance under these single transpositions: a transposition changes any event only by removing a and adding b, or vice versa, or leaves it fixed. Finite additivity and equality of their weights preserve its measure. This argument does not require the event itself to be finite.

**(2) ⇒ (3).** Faithfulness and the finite-mass/countability argument in [§4 of the companion note](canonical-atomic-probability.md#4-countability-the-precise-remaining-selection) give an admitted injection W→N_e. The countable finite-choice instance used there is supplied by F.

For a fixed a, all atoms in [a]_R have the same positive weight c=μ(a). Internal Archimedeanness gives n>0 with c≥1/n. The finite-budget lemma bounds the entire class by n elements. Since a was arbitrary every class is internally finite. No representatives were chosen simultaneously and no externally uniform bound on class sizes is claimed.

**(3) ⇒ (4).** Fix an admitted injection j:W→N. For each a define

    ℓ(a) := min {j(b) : R(a,b)},
    m(a) := the internal finite cardinality of [a]_R,
    c(a) := 2^(−ℓ(a)−1) / m(a).                              (10)

The class contains a, so its least label exists and m(a)>0. Both are unique and constant on the class. Their graphs, and c, are admitted by comprehension and finite counting. No representative or class-size enumeration is chosen. Distinct classes have distinct least labels, since j is injective.

For a finite K⊆W, partition K by its finitely many R-classes. In each encountered class with least label n and size m, K contains at most m elements, so its contribution is at most 2^(−n−1). The distinct encountered n form an admitted finite subset of N. The finite geometric bound therefore gives

    Σ(a∈K)c(a) ≤ 1.

Apply the finite-budget lemma to c and normalize its atomic sum. The result is faithful and completely additive. If P preserves every class, then c(P(a))=c(a). For every p, the image operation K↦P[K] is a bijection between its admitted finite atom subsets and those of F_P(p), and preserves their sums. Its graph is given by finite image comprehension; the inverse uses P⁻¹. Equality of the suprema in the definition of V_c proves

    V_c(F_P(p)) = V_c(p).

Normalization preserves invariance, establishing (4). Finally **(4) ⇒ (1)** is immediate. ∎

There is also a canonical route directly from (2) to (4): apply the atomic-part construction to μ. Reindexing finite atom subsets as above proves that μ_at, and hence its normalization, is invariant. This route needs no numerical injection or countable selection. Condition (3) describes the cardinality forced by the original background; it is not necessary machinery for regularizing a state already given.

## Recovering and sharpening the original consequences

For universal R there is one class, so (3) says exactly that W is internally finite. If |W|=m, finite atomic decomposition and equal atom masses force each mass to be 1/m. Thus the original unique normalized counting state is recovered. This proof also explains why invariance under pairwise transpositions already suffices for the **existence** conclusion.

For finitely many propositional parameters p₁,…,pₖ, take R to identify atoms with the same membership pattern below those propositions. There are at most 2^k classes; k is the external finite length of the parameter tuple. A pure operation term with these parameters and parameters from the original hereditary mathematical core has equal atom weights on every class: a within-cell transposition fixes every parameter and every core real output, and the lifted application-preserving automorphism therefore gives μ(a)=μ(b). This is exactly the term-substitution and core-fixity argument of the original note and the represented-permutation theorem, with no stronger definability assumption.

Each nonempty class is internally finite by the common-weight estimate. Their finite union is internally finite, by internal finite induction. This gives the original finite-parameter obstruction directly, and more generally gives the same conclusion for any represented R with internally finitely many classes and a faithful state constant on its classes.

At the other extreme R is equality: all classes are singletons and the theorem reduces to internal countability of W. Between them, countably many internally finite classes can support a faithful invariant state, with unbounded finite class sizes permitted. Formula (10) supplies it explicitly.

## Obligations retained

The background F and quantified Infinity_e are retained for the Classicism statement. The only simultaneous selection in the proof occurs in deriving an injection W→N from a faithful charge. The forward common-weight bound and both invariant-state constructions do not use that selection. Existence of the internal arithmetic, finite counting, real suprema, and graph-coded functions is retained explicitly in the companion note.

We do not infer that an arbitrary given finite-additive state with class-constant atom weights is itself invariant under every infinite class-preserving permutation. Its residual charge, zero on atoms, is not determined by those weights. What is proved is invariance under single transpositions for that state, and full represented invariance of its **canonical atomic replacement**. Likewise the finite-parameter conclusion is about operation terms with fixed-core outputs, not arbitrary descriptions involving designated current truth.

Sources: original unpaginated research notes `probability-and-world-symmetry.md`, §§1–2; `represented-world-permutations.md`, §§1–3, 5; `faithful-probability-countable-worlds.md`, §§1–4. The background finite-transposition construction is attributed there to the database proof `c5-and-atomicity-imply-no-pure-contingency`; no new authorship attribution is made for it. The partition criterion and explicit state (10) are the refinement proved here.
