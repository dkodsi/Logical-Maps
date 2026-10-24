# A canonical atomic part of a finitely additive probability

22 October 2026. Alternative ordinary mathematical argument by OpenAI Codex; direct source `misc`. No independent referee or formal verification claim. Original: [faithful probability, §§1–4 and 6–8](../notes/faithful-probability-countable-worlds.md).

## Statement and improvement

The original theorem works over F = C + □Functional Choice plus quantified Infinity_e. It proves that faithful finite-additive and countably additive probabilities exist exactly when the atom field is internally N_e-countable. Its construction passes through a chosen enumeration and assigns fresh geometric weights.

There is a shorter direct replacement: retain a given charge's atom weights and sum them by finite subsets. This produces its **canonical completely additive atomic part**, below the original charge. If the charge is faithful and the algebra is atomic, normalizing that part gives a faithful completely additive probability. No choice of enumerations or orderings enters this construction. The common finite-mass estimate also isolates the precise countable selection used in the cardinality argument.

“Completely additive” throughout means additive over **represented** disjoint families with existing joins, with the sum defined by the supremum of finite subsums. It is stronger than the represented countable-additivity assertion. It never means additivity over every external family.

## 1. Internal setting and representation obligations

For the Classicism application retain the original F + quantified Infinity_e background and its internal Dedekind reals over N_e. The event algebra B can be any relational-type Boolean algebra. Use the graph-coded extensional interpretation of [world representation, §15](../notes/structural-world-representation.md#15-canonical-reverse-representation-what-is-immediate-and-what-requires-coding), exactly as in the original probability note. All fields and maps below are admitted there.

The abstract argument itself needs only:

* a Boolean algebra B, its represented atom field A, and the joins explicitly mentioned;
* internal Peano numbers, finite subsets/sequences at the relevant fixed code types, and induction, including finite-set images and finite sums;
* internal Archimedean Dedekind reals with suprema for represented nonempty bounded real fields;
* comprehension and graph-coded unique-value definitions for the fields and functions used.

No Choice axiom is needed for the finite-budget lemma and atomic-part construction in §§2–3 once these resources are supplied. The countability assertions, including the final countability-based observation in §3, use the selection isolated in §4. The supplied resources are substantive interpretation hypotheses, not conclusions about bare C. The corollaries in C retain F; this note does **not** replace its whole background by a weaker unproved core-existence assertion. Every “finite” or “natural number” below is internal and may be externally nonstandard.

Finite subsets of A can be represented as predicates with an internal finite enumeration; finite sequences are graphs on initial segments of N. A finite sum of nonnegative weights is independent of the chosen enumeration, by finite induction and commutativity. Thus its defining relation has a unique real value; no simultaneous choice of enumerations is required. All families of such finite subsets, their images, and the real fields used below are obtained by comprehension at fixed code types.

## 2. One finite-budget lemma

Let c:A→R be nonnegative, and suppose every admitted finite K ⊆ A satisfies

    Σ(a∈K)c(a) ≤ 1.                                           (4)

Define, for p∈B,

    V_c(p) := sup { Σ(a∈K)c(a) : K finite, K ⊆ A, ∀a∈K(a≤p) }. (5)

The set includes 0 and is bounded by 1, so the real exists uniquely. Comprehension for its least-upper-bound graph gives the admitted function V_c. This is an internal supremum, not an external sum over A.

**Lemma.** V_c is nonnegative and finitely additive, V_c(a)=c(a) on atoms, and 0≤V_c(⊤)≤1. For every represented disjoint family (p_i) whose join p exists,

    V_c(p) = sup { Σ(i∈J)V_c(p_i) : J a finite set of indices }. (6)

**Proof.** Monotonicity follows by inclusion of the sets in (5). The only atoms below an atom a are a itself, so V_c(a)=c(a), and V_c(⊥)=0.

If p∧q=⊥, every atom below p∨q is below exactly one of p,q. Partitioning any finite K accordingly gives V_c(p∨q)≤V_c(p)+V_c(q). In the other direction, finite atom subsets below p and q have disjoint union below p∨q. For any ε>0 choose each finite subsum within ε/2 of its supremum. Their union gives V_c(p)+V_c(q)≤V_c(p∨q)+ε. The real order, for all ε>0, proves the reverse inequality. Only two existential witnesses were chosen.

An atom a below a join of a represented family lies below some family member: otherwise a∧p_i=0 for every i, so ¬a bounds every p_i and hence their join, contradicting a≤p. In a disjoint family its index is unique.

For finite K of atoms below p, those unique indices form an admitted finite set J. Partition K by its index to obtain

    Σ(a∈K)c(a) ≤ Σ(i∈J)V_c(p_i).

This proves the ≤ direction in (6) after taking the supremum over K. Conversely finite additivity gives

    Σ(i∈J)V_c(p_i) = V_c(∨(i∈J)p_i) ≤ V_c(p).

The subsums in (6) are therefore bounded and their supremum exists. This proves (6). Unique-index graphs and finite images use no Choice. ∎

For an N-indexed family, every internally finite set of indices has a finite upper bound. Therefore the supremum in (6) equals the supremum of initial partial sums. Thus (6) includes the original countable-additivity law, including for nonstandard N.

If B is nontrivial and atomic and c(a)>0 for every atom, then V_c(⊤)>0 and

    p ↦ V_c(p)/V_c(⊤)                                        (7)

is a faithful completely additive probability: a nonzero p has some atom a≤p, so V_c(p)≥c(a)>0.

## 3. Canonical replacement and decomposition

Given a nonnegative normalized finitely additive charge μ, put c(a)=μ(a). Distinct atoms are disjoint, so finite additivity and monotonicity give (4). Define

    μ_at := V_c,              ρ := μ − μ_at.                  (8)

For every finite atom subset K below p,

    Σ(a∈K)μ(a) = μ(∨K) ≤ μ(p).

Consequently μ_at≤μ pointwise. The lemma proves that μ_at is completely additive. Also μ_at(a)=μ(a), so ρ is a nonnegative finitely additive charge with ρ(a)=0 for every atom. Neither summand is asserted to be normalized.

When B is atomic, μ_at is the greatest nonnegative completely additive charge λ with λ≤μ. Indeed p is the join of its represented family of atoms: if an upper bound u failed to contain p, the nonzero p∧¬u would contain an atom. Complete additivity therefore yields

    λ(p) = sup(K finite atoms below p) Σ(a∈K)λ(a)
         ≤ sup(K finite atoms below p) Σ(a∈K)μ(a) = μ_at(p).

It also proves uniqueness of the decomposition into a completely additive part and a nonnegative charge zero on atoms: such a part has the same atom weights as μ and is determined by them.

If B is nontrivial and atomic and μ is faithful, μ_at(⊤)>0 and μ* := μ_at/μ_at(⊤) is the required faithful completely additive probability. The unnormalized μ_at preserves **exact** atom weights; μ* preserves their ratios. Although μ_at≤μ, the normalized μ* need not be below μ. This is a replacement of μ, not a proof that μ itself is countably additive.

The largest-minorant assertion is about **complete** additivity. It must not be weakened to countable additivity on an arbitrary uncountable atom field. In the original faithful-probability setting the field becomes internally countable by §4; there, countable additivity does determine a measure by its atom weights. To see this, use an injection A→N to list at most one atom at each index, inserting ⊥ at unused indices. Every p is the join of the resulting sequence of its atoms. Hence, in that setting,

    μ is countably additive iff μ=μ_at iff μ_at(⊤)=1.

For the last equivalence, the nonnegative remainder ρ has total mass zero iff it is identically zero.

## 4. Countability: the precise remaining selection

The following is the shared finite-mass estimate. If c satisfies (4), then

    A_n := {a∈A : c(a)≥1/n},       n>0,

has at most n elements. Otherwise an admitted (n+1)-element subset has weight at least (n+1)/n>1. The elementary assertion that a field with no (n+1)-element subset injects into n is proved by internal induction: at the successor step remove one element if nonempty, apply the predecessor case, and add that element back. No enumeration of an infinite field is used.

If c(a)>0, internal Archimedeanness gives n with c(a)≥1/n. Thus A=⋃(n>0)A_n. This is a **countable union of internally finite fields**, without Choice so far. It is not yet an injection A→N in a choiceless setting.

For each n, the field I_n of injections A_n→{0,…,n−1} is nonempty and internally finite. Finiteness follows by finite induction from the finiteness of domain and codomain; it is a field of graphs at one fixed type. The only nonunique simultaneous selection needed is

    choose i_n∈I_n for each positive n.                        (9)

Full Choice supplied by F suffices; represented countable Choice for finite fields is already sufficient for (9). Give each a its least eligible n and the label i_n(a). Numerical pairing gives an injection A→N. We do not claim that (9) is necessary for every alternative proof, or that it follows from C.

Conversely an admitted injection j:A→N immediately supplies c(a)=2^(−j(a)−1). Any finite set of labels is bounded by some k, and its sum is at most Σ(n<k)2^(−n−1)≤1, by internal finite induction. The lemma supplies (7). This direction requires no choice of inverse at unoccupied labels and no further Choice.

Thus the original equivalence is recovered, while its two tasks are separated: **regularizing a given faithful charge is canonical and uses no Choice beyond the supplied internal mathematics; enumerating its atoms uses (9).** The atom-countability/ccc equivalence is left to the original cited proof and is not recounted here.

## Sources and scope

Original research source: `faithful-probability-countable-worlds.md`, §§1–4, 6–8; coding dependency: `structural-world-representation.md`, §15. These are unpaginated local research notes. The Classicism background is Bacon–Dorr, draft 16 May 2023, §2.3, pp. 31–33, via `necessary-functional-choice-r-implies-necessary-plenitude-r` and the recorded completeness/Choice consequences. The new finite-subset construction and dependency separation are attributed to this note, not to that paper. No database or Lean status is changed.
