# Finite pointed profile rank under pure Strong Possibility

22 October 2026. Original ordinary mathematical deductions by OpenAI Codex; not human checked or formalized. Direct source of the new theorem: misc, this note. No main database edits. The fixed framework is Bacon–Dorr Classicism C with its relational types. The background pure Maximalism and Strong Possibility definitions are those in the topic records (Classicism, 16 May 2023 draft, §§2.4 and 2.6, pp. 35–36 and 42). The restricted profile-root model is the separate original construction in `.reproduction/classicism-research/profile-root-construction-20261022.md`, §§1–3; do not attribute that variation or this rank theorem to the published paper.

## 1. Statement

Fix a closed pure proposition A and a fresh individual constant a. Let S_A be the space of complete consistent theories extending C(a)+A, in the language containing a and no other nonlogical constants. Only ordinary finitary sentences occur. The assertion that S_A has k members is external; k below is a fixed finite natural number.

Define `Width_k(A)` to say that there are no k+1 pairwise disjoint nonzero subpropositions of A. Explicitly it is the universal finite-Boolean-identity sentence

    forall p_0,...,p_k [ (all_i p_i<=A and all_i<j p_i and p_j=bottom)
                         -> some_i p_i=bottom ].

For k=0 this is A=bottom. For k>=1, exact Boolean rank k means Width_k(A) and the existence of k pairwise disjoint nonzero subpropositions whose join is A. Equivalently, the interval [bottom,A] is the finite Boolean algebra with k atoms and 2^k elements.

**Theorem.** Max(C)+Width_k(A) is consistent if and only if S_A has at most k members. Consequently:

1. If S_A has exactly finite k members, pure SP forces the interval below A to have exactly k atoms and 2^k elements.
2. If S_A is infinite, pure Max already forces failure of Width_k(A) for every fixed finite k.

These conclusions do not assert consistency of SP. They classify its forced finite interval ranks conditional on a model existing; the Max-consistency biconditional itself is established by explicit models and deductions.

## 2. Necessity and all-Max lower bounds

Suppose S_A contains k+1 distinct complete theories T_0,...,T_k. A finite family of sentences separates them: for each pair choose a sentence on which they disagree, and collect these finitely many sentences. Their complete Boolean truth assignments yield pairwise contradictory formulas chi_i(a), with A and chi_i(a) consistent for every i. Replace the constant a by a free individual variable x.

Pure Max entails the unary Possibility+ theorem: every C-consistent pure phi(x) is possible of every actual individual. Therefore, at any actual b, all propositions

    A and chi_0(b), ..., A and chi_k(b)

are nonzero. Their pairwise meets are bottom because the corresponding incompatibilities are C-theorems, and they lie below A. Thus every Max model refutes Width_k(A). This proves necessity, and proves the infinite case for each finite k.

## 3. Finite pointed completions yield a profile-root witness

Suppose S_A has exactly m<=k members. If m=0, C+A is inconsistent and A=bottom is a C-theorem; the conclusion is immediate from any Max model. Assume m>=1.

Finitely many complete theories can be separated and isolated by finitely many sentences. Choose chi_1(a),...,chi_m(a) such that C(a)+A proves their pairwise incompatibility and their disjunction, and C(a)+A+chi_i(a) is complete and consistent for every i. To justify completeness of each isolated extension: any further consistent sentence extends to a completion by ordinary completeness/compactness, and isolation leaves only the ith completion.

Use the singleton pure-term-profile root. Its proposition domain is `2 x B_t`, where B_t consists of pure one-individual profiles T(x) modulo their values across a C-complete family of pointed component worlds. A root proposition has an arbitrary actual bit and one such profile.

For any p with profile T(x), the restriction A and chi_i(x) decides T(x) in its complete pointed theory. Consequently the profile of p and A is the union of some subset of the m profile cells

    b_i := [A and chi_i(x)].

Each b_i is nonzero by consistency, and these cells are pairwise disjoint and exhaust [A]. They are atoms in the restricted profile Boolean algebra because their theories decide every pure one-individual term. Here profile equality means equality of the whole component intensions, not merely agreement in actual truth at one component. Completeness of C(a)+A+chi_i(a) gives a C-theorem A and chi_i(a) -> T(a), or its negated version. The theorem may be necessitated, and modalized extensionality then gives the required identity of restricted profiles at every future component point.

It remains essential to check the free actual bit: A must be false at the root. In fact A is false in EVERY Max model when S_A is finite. If some Max model satisfied A at an actual b, one of the chi_i(b) would hold there. The consistent recursively enumerable complete theory C(a)+A+chi_i(a) would then entail every pure Max axiom: completeness decides each axiom, while its negation is excluded by the given model. This contradicts the no-consistent-r.e.-extension-of-C-containing-Max theorem. That theorem remains valid with one added individual constant, because the expanded theory is r.e., the C-search still concerns closed PURE identities, and consistency prevents proving a disequality when C proves its opposite identity.

Hence A has actual bit 0 at the profile root, and so does every root subproposition of A. There is no additional root-only atom below A. The interval [bottom,A] is precisely the m-cell finite Boolean algebra just described. It satisfies Width_m(A), hence Width_k(A), proving sufficiency.

The recursion-theoretic input here is the same established obstruction used in the profile note's atom classification: no consistent r.e. extension of C can contain all pure Max axioms, since dovetailing a C proof of a pure identity with a proof of its Max disequality would decide C theoremhood. Church undecidability is used only through that already supplied argument; no complexity or novelty claim is added here.

## 4. Exact SP decomposition

Width_m(A) is a universal Boolean identity sentence and is individually Max-consistent by §3. Universal identity reflection under distinctness-preserving possibility therefore makes it a consequence of pure SP. Section 2 gives, already under Max, m nonzero disjoint cells A and chi_i(b) for every actual b. The C-theorem that their join is A makes them exhaustive. With m nonzero cells and Width_m(A), each cell must be an atom: a proper nonzero split of one cell together with the other m-1 cells would produce m+1 nonzero disjoint pieces. Thus the interval has exactly 2^m elements.

For m=1 this recovers the pointed-completeness classification of atomic pure A. For A equal to a finite disjunction of the mutually incompatible finite extensional propositions `Fregean and Exactly_n(e)`, the number m is the number of displayed positive integers, so SP forces the expected finite disjoint atomic sum. No stronger finite-rank conclusion is asserted when the pointed completion space is infinite.

## 5. Scope and limitation

This theorem does not remove the Henkin obstruction. Every finite-rank constraint here is already simultaneously realized in the profile root, which still has arbitrary actual extension coordinates and does not satisfy SP. The new result is an exact classification of ALL finite Boolean interval ranks of closed pure propositions, extending the previously established rank-one/atom classification.
