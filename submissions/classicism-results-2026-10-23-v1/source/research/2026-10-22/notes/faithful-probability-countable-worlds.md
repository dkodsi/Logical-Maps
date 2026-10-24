# Faithful probability exactly characterizes internally countable worlds

Research bridge, 22 October 2026. Ordinary mathematical proof; direct source would be `misc`. No database edit, formal verification, external-fullness claim, or claim of literature novelty. The countable-chain-condition equivalence itself was proved independently by the infinity lane; the new proposed bridge here is its probabilistic characterization and its precise compatibility boundary with world-profile richness.

## 1. Framework and definitions

Put F = C + □Functional Choice and additionally assume the **quantified Axiom of Infinity at e**. The latter is not replaced by the Infinity schema. Let N=N_e be the corresponding internal Frege natural-number domain. Under F, arithmetic has its ordinary extensional interpretation and is Peano; N need not be externally standard.

The real numbers used below are the **internal Dedekind reals over this N**, constructed in the extensional interpreted mathematics. They are not an independently supplied external real field. One may use the graph-coded Henkin Gallin expansion in `structural-world-representation.md`, §15, whose C-reduct is unchanged, or the supported extensional core together with graph codes. Rationals and Dedekind cuts are coded fields at allowed relational types; comprehension gives their admitted cuts, and their least-upper-bound theorem is internal. All operations and functions below mean admitted graphs/operations, and all quantification is over these admitted fields. This is a definitional coding extension, not the addition of arbitrary external subsets, maps, or types to a model.

Let B be the Boolean algebra of **all current ambient propositions**, with zero bottom and unit top. It is not the two-element logical truth sort of the extensional interpretation. Let W=Atoms(B). F gives Atomicity, Boolean Completeness, necessary distinctness, BF, and the needed Choice. The canonical representation identifies each p with its admitted set of atoms {a:a≤p}; every admitted join has the corresponding union of atoms.

Use exactly the existing relative-countability definition Ctbl_(e,t): a label relation R(a,n) for n∈N such that two members share a label iff they are identical. Under the present Peano/Choice assumptions, this is equivalent to an admitted injection into N. For this conversion, take the least label of each member; different members have disjoint label sets. Conversely an injection supplies the label relation. Empty fields are countable.

A **faithful probability** is an admitted real-valued function μ on B satisfying

    μ(bottom)=0,  μ(top)=1,  μ(p)≥0,
    p∧q=bottom  ⇒  μ(p∨q)=μ(p)+μ(q),
    p≠bottom  ⇒  μ(p)>0.

The last clause is often called strict positivity. Countable additivity, when required, means for every admitted N-indexed pairwise disjoint family p_n,

    μ(join_n p_n) = sup_k sum_(n<k) μ(p_n).

All sums and suprema in this display are internal. No external sequence absent from the model is quantified over.

## 2. Exact theorem

Over F + AxiomOfInfinity_e the following are equivalent:

1. There exists a faithful finitely additive probability on B.
2. There exists a faithful countably additive probability on B.
3. W is internally countable relative to N_e.
4. Every admitted antichain of nonzero propositions is internally countable relative to N_e.

Thus a short natural additional principle is: **Every genuine possibility has positive probability under some probability assignment to all propositions.** Its exact formal form is (1), with one common normalized finitely additive assignment. It is not a statement that every possible probability assignment is faithful.

The equivalence (3)⇔(4) is the infinity lane's Atomicity-only theorem in `world-cardinality-ucp-20261022.md`, §18. Its label-relation proof uses neither Choice nor Boolean Completeness. The present extra assumptions support ordinary internally infinite counting and the probability construction.

## 3. Faithful finite additivity forces countably many atoms

Let μ satisfy (1). For positive n∈N form the admitted atom field

    W_n = {a∈W : μ(a)≥1/n}.

There are at most n members of W_n. Here “n+1 distinct atoms” means an admitted injection from the internal initial segment of length n+1, not a variable-length external tuple. Their images are pairwise disjoint, so induction from finite additivity gives measure at least (n+1)/n>1 to their join, contradicting monotonicity and μ(top)=1. The elementary finite-set lemma that a field with no n+1 distinct members has an injection into the initial segment of length n follows by induction on n; it works for internal n as well.

Every atom belongs to some W_n. Its measure is positive, and the internal Archimedean theorem for Dedekind reals gives a positive natural n with 1/n≤μ(a). This is an internal assertion: it does not say that some externally standard integer always works.

For each n choose an injection of W_n into {0,...,n−1}. These injections are represented graphs at one fixed code type, so the ordinary Choice supplied by F applies to this N-indexed family. Give a∈W the pair consisting of its least eligible n and its chosen index in W_n. This is injective into N×N. The ordinary primitive-recursive pairing injection N×N→N gives an admitted numerical injection of W. Hence (3). Only finite additivity was used; no countable additivity of the original μ was assumed.

## 4. Countably many atoms give a faithful countably additive probability

Suppose j:W→N is an admitted injection. Define positive weights

    c(a)=2^(-j(a)-1).

For p∈B and k∈N, let s_k(p) be the finite sum of c(a) over atoms a≤p with j(a)<k. Because j is injective, this is a finite sum over at most k objects. Equivalently sum over n<k, giving contribution 2^(-n-1) if an atom with label n lies below p and 0 otherwise. The unique labeled atom, when present, needs no additional arbitrary selection.

The partial sums are increasing and bounded by 1. Let s(p)=sup_k s_k(p), an internal Dedekind real. Since B is nontrivial and atomic, W is nonempty, so 0<s(top)≤1. Put

    μ(p)=s(p)/s(top).

The defining real is unique; comprehension and unique choice give the admitted function p↦μ(p). It is normalized and nonnegative. For disjoint p,q the atoms below p∨q are the disjoint union of their atom sets, so finite sums and their increasing suprema give finite additivity. If p≠bottom, Atomicity gives a≤p, and μ(p)≥c(a)/s(top)>0. Thus μ is faithful.

For countable additivity let p_i be an admitted disjoint family and p its join. An atom lies below p iff it lies below exactly one p_i. The forward existence uses the atom–join lemma: otherwise every p_i is below ¬a and so their join is below ¬a. For each finite number k of atom labels, the finitely many atoms counted in s_k(p) have their unique indices i. These indices have an internal finite maximum m. Hence

    s_k(p) ≤ sum_(i≤m) s(p_i).

Taking the supremum over k gives s(p)≤sup_m sum_(i≤m)s(p_i). Conversely each finite disjoint union of p_i is below p, so finite additivity gives the reverse inequality. Dividing by s(top) proves the displayed countable-additivity law. This is internal finite approximation and induction; it requires no external enumeration and no interchange of absent external suprema.

Therefore (3)⇒(2). The implication (2)⇒(1) is immediate, completing the theorem.

A faithful finitely additive probability need not itself be countably additive. For example, in the full P(N) algebra, half a geometric atomic probability plus half the {0,1}-valued charge of a free ultrafilter is faithful and finitely additive but not countably additive. The theorem replaces a given faithful charge by a suitable probability; it does not upgrade that same charge.

## 5. Genuine independence and a compatibility boundary

In the ZFC metatheory, take the full constant-domain Gallin model with E=N and world set W=N. It satisfies F, quantified Infinity_e and Infinity_t. The proposition algebra is P(N), and

    μ(p)=sum_(n∈p) 2^(-n-1)

is an admitted faithful countably additive probability. Thus the proposed strengthening is consistent relative to this familiar full-model metatheory, including infinite individuals and infinitely many possibilities.

Now take the full Gallin model with E=N and W=P(N). It also satisfies F and the two quantified Infinity axioms, but no faithful finitely additive real probability exists: by §3 it would make the uncountable atom set P(N) countable. Here internal naturals and reals are the ordinary full ones, so Cantor's theorem gives the separation directly. No CH, measurable-cardinal hypothesis, or other unsettled set-theoretic conjecture is used.

The second model realizes every binary N-profile of a suitable family of propositions: put P_n={S⊆N:n∈S}. In general the represented full-profile principle WR(N) gives an admitted surjection W→P(N), as proved in the infinity lane's §27. Consequently, over the present background, WR(N) is incompatible with faithful probability: numerical injection of W and the profile surjection would give a numerical enumeration of all admitted subsets of N, contradicted by the internal Cantor diagonal.

This is an exact tradeoff between two independently consistent simple strengthenings of F. Faithful probability allows infinitely many possibilities, but it excludes realization of every infinite binary pattern. Merely realizing every finite pattern remains compatible: the full countable-world model admits binary-digit coordinate propositions and the geometric probability above.

## 6. Scope and proposed definition improvement

It is enough to demand positivity on **atoms**, not on every nonzero proposition. Atomicity and monotonicity make the two formulations equivalent. It is also enough to ask for a bounded strictly positive additive weight with 0<μ(top)<∞; normalization divides by μ(top). Thus a concise algebraic definition is: the proposition Boolean algebra admits a strictly positive real-valued additive state.

The statement is propositional, not an all-type requirement. An all-type analogue can fail for simple cardinal reasons even when the propositional instance holds. The theorem's counting base is fixed to e and its reals are built from N_e. Replacing e by another counting base is legitimate only after the corresponding quantified Infinity and interpreted arithmetic are supplied explicitly.

The necessary and fixed-witness modal variants have not been conflated with this actual existential assertion. Likewise none of the equivalences means that arbitrary external antichains or external countable families are represented in a Henkin model.

## 7. Type-local factorization: probability on individual-state events

The proof of §§3–4 applies unchanged to the Boolean algebra B_tau of any relational type tau: replace proposition atoms by atoms of B_tau. Thus a faithful real state on B_tau exists iff its atom field is N_e-countable. Again existence of a finite-additive state and existence of a countably additive state are equivalent.

Under F, the atomic normal form in `structural-world-representation.md`, §4, identifies these atoms exactly as

    h_(a,xbar)(ybar)=a∧(ybar=xbar),

where a∈W and xbar ranges over the actual argument tuple of tau. Hence the atom field is internally isomorphic to W×D_sigma1×...×D_sigmak. In the present Choice/Peano setting, a finite nonempty product is countable iff each factor is countable: one direction fixes default elements to embed each factor, and the other uses numerical pairing. All maps are represented.

In particular the following are equivalent:

* The Boolean algebra of individual properties, B_et, has a faithful real state.
* Both the world field W and the individual domain are internally N_e-countable.
* For every external finite arity k≥1, the Boolean algebra B_(e^k t) of k-ary individual relations has a faithful real state.

The last is an ordinary finite-arity schema, not a quantification over types or nonstandard arities. The state may be chosen countably additive at each arity.

This is a slightly stronger, equally natural probability axiom: regular probability is available on individual-state events, and therefore on every finite tuple of individuals together with a state. It is consistent with genuinely infinite individuals and worlds in the full E=W=N model. It strictly strengthens the propositional state axiom: full E=P(N), W=N has a faithful probability on propositions but none on individual properties, by the atom-product characterization and Cantor. Both models still satisfy F+quantified Infinity_e+quantified Infinity_t.

## 8. The higher-type ceiling

A faithful state on B_tt, the Boolean algebra of properties of propositions, is much stronger. Under the same background,

    faithful state on B_tt  iff  W is internally finite.

Here finite is ordinary internal finite cardinality in the interpreted Peano arithmetic, not externally finite.

For the reverse implication, finitely many atoms give only finitely many propositions: every proposition is the join of the atoms below it, and the usual finite-powerset induction applies. This internal finiteness theorem is independently detailed in the infinity lane's §20.C. Thus W×D_t is finite, so it admits a normalized positive counting state on B_tt by the preceding atom-product theorem.

For the forward implication, a state makes W×D_t countable and hence D_t countable. Suppose W were not finite. The Choice theorem that every infinite represented field contains an admitted N-sequence of distinct members gives atoms a_n. For any admitted numerical property X⊆N, Boolean Completeness gives

    p_X = join {a_n : n∈X}.

The atom–join lemma makes X↦p_X injective. Composing with a numerical injection of D_t would inject the full admitted numerical powerset into N. This contradicts the internal Cantor diagonal: invert that injection on its range, use the empty set off the range to obtain a surjection N→P(N), and form the admitted diagonal subset. Therefore W is finite.

The elementary Choice-to-countable-subset step is an internal theorem of the interpreted extensional Choice arithmetic: well-order the field and take its first n members by finite recursion; failure to reach a next member would make the whole field finite. It asserts an admitted N-indexed sequence and does not appeal to an external enumeration. See also the independent world-sequence proof in `structural-algebraic-core.md`, §17, and `world-cardinality-ucp-20261022.md`, §§23–25.

Consequently, with quantified Infinity_t, propositional faithful probability can hold but faithful probability one logical level higher, at tt, cannot. The full E=W=N model exhibits exactly this distinction. An unqualified all-relational-type state schema is even incompatible with quantified Infinity_e: it makes the individual-property domain D_et countable by applying the atom-product criterion at (et)t, while the admitted powerset of a numerical copy inside the infinite individual field injects into D_et, contradicting Cantor in the same way.

This is why the proposed probability principle should be stated at a specified event type. Finite individual arities form a coherent infinite package; unrestricted higher-type uniformity is a genuinely different and, with Infinity, inconsistent demand.

## Audit

The principles lane independently checked §§1–6 on 22 October 2026: threshold finiteness for internal n, the internal Archimedean step, graph-coded Choice, and countable-additivity by finite atom-label approximation. This is an AI-agent mathematical audit, not human review or formal verification. The rigidity lane independently checked §§1–8, including the atom-product factorization, finite-world ceiling, represented numerical powerset embedding, and internal Cantor diagonal. The choice lane also independently checked the companion symmetry theorem in `probability-and-world-symmetry.md`.
