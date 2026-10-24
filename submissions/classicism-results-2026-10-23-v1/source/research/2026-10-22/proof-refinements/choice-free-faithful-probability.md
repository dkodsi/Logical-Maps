# Faithful probability without Choice: finite fibres are the exact condition

22 October 2026. Ordinary mathematical refinement by OpenAI Codex; direct source `misc`. No independent or formal verification claim. Original: [faithful probability, §§1–4](../notes/faithful-probability-countable-worlds.md). This strengthens the dependency audit in [canonical atomic probability](canonical-atomic-probability.md).

## 1. Exact statement over the weaker background

Put B₀ = **C + □Plenitude + quantified Infinity_e**. Full boxed Functional Choice is not assumed. Let W be the atom field of the Boolean algebra of all current propositions. Reals and graphs have the internal interpretation specified in §2.

Say W has a **finite-fibre numerical labelling** when there is an admitted graph ℓ:W→N_e such that every fibre ℓ⁻¹(n) is internally finite. Here finite means admitting a graph bijection with an initial segment of this same N_e, and never means externally finite. This is weaker in form than an injection: several atoms may share a label. Equivalently W is covered by an admitted N_e-indexed family of internally finite fields. From a cover choose each atom's *least* covering index; this is unique-value definition, not Choice. Conversely the fibres give a cover.

**Theorem.** Over B₀, the following are equivalent:

1. A faithful finitely additive real probability exists on all propositions.
2. A faithful countably additive real probability exists.
3. A faithful completely additive real probability exists, for represented disjoint families.
4. W has a finite-fibre numerical labelling.

If represented **countable Choice for finite fields** is added in the interpreted mathematics, these are also equivalent to the original N_e-countability condition, namely an admitted injection W→N_e. Full Functional Choice is unnecessary for this conclusion.

The change from injection to finite fibres without Choice is essential to the statement. We have not proved that every countable union of finite fields is countable without a choice principle.

## 2. Why the internal mathematics is available without Functional Choice

The original [world-representation theorem, §15](../notes/structural-world-representation.md#15-canonical-reverse-representation-what-is-immediate-and-what-requires-coding) constructs an extensional Henkin graph-coded expansion already over C+□Plenitude. Its comprehension and unique-value application do not use Functional Choice. That principle occurs only in its separately stated **Choice correspondence**. The expansion retains the current proposition domain as a Boolean event algebra; it does not replace that algebra by its two-element logical truth sort.

The proved records give Atomicity_t and Boolean Completeness_t from □Plenitude. A represented family in the expansion translates to an admitted ambient relation, so these are the needed internal atomicity and completeness. Joins of represented families exist; no external subsets are added.

Quantified Infinity_e transfers to the extensional core without Choice. The [core-number isomorphism](infinity-core-number-isomorphism.md) now shows that its numbers agree, by an admitted bijection, with the original N_e, including represented numerical subsets. Thus changing to the graph-coded interpretation does not silently change the counting base. Its finite-sequence and arithmetic graphs are obtained by finite recursion and unique-value comprehension. Induction is available for every admitted predicate, with higher-type parameters.

Internal rationals are the usual integer-pair codes modulo their definable equivalence; graphs or canonical reduced codes may be used. Internal Dedekind reals are the admitted nonempty proper lower rational cuts without a greatest member. The union of a represented nonempty bounded family of cuts is again such a cut: nonemptiness follows from one member, properness from a common upper cut, and downward closure/no greatest member from the constituent cuts. This proves the needed internal supremum theorem without Choice. If ε>0, a positive rational q lies below ε; its denominator supplies a positive n with 1/n≤q<ε. This gives the Archimedean step **relative to the same internal N_e**, not an external standard-integer bound.

These are the same represented-number/real obligations as in the original probability note, now supported by boxed Plenitude rather than boxed Functional Choice. A state is an admitted **functional graph in this interpretation**, as permitted in the original coding convention. We are not claiming, without a representation argument, an operation of a newly invented C function type. Under B₀, graphs with original relational output codes can also be represented using Plenitude; this extra observation is unnecessary for the proof.

## 3. Probability supplies finite fibres

Let μ be faithful and finitely additive. For n>0, define

    W_n := {a∈W : μ(a)≥1/n}.

There are at most n atoms in W_n: an admitted finite subset of n+1 distinct atoms is disjoint and would have total mass at least (n+1)/n>1. The internal finite-set induction in the [finite-mass argument](canonical-atomic-probability.md#4-countability-the-precise-remaining-selection) converts this bound into internal finiteness. Faithfulness and internal Archimedeanness put each atom in some W_n.

Define ℓ(a) to be the least positive n with a∈W_n. Its graph is admitted and single-valued. Its n-fibre is a subset of W_n, hence has at most n members. This proves (1)⇒(4) with no simultaneous selection.

## 4. Finite fibres supply a probability

Given ℓ, let A_n=ℓ⁻¹(n), and let m_n be its internal finite cardinality. For a∈A_n define

    c(a) := 2^(−n−1)/m_n.                                    (1)

The denominator is nonzero on that fibre. Each m_n is uniquely determined; the graph n↦m_n is obtained by comprehension, not by choosing enumerations of the A_n. At empty fibres the formula is never evaluated on an atom.

If K⊆W is internally finite, partition it into its finitely many label fibres. The contribution of its n-piece is at most m_n·2^(−n−1)/m_n=2^(−n−1). The encountered labels form an internally finite numerical set and have an upper bound. The finite geometric-sum bound therefore gives

    Σ(a∈K)c(a) ≤ 1.

Every c(a) is positive. The [finite-budget lemma](canonical-atomic-probability.md#2-one-finite-budget-lemma) constructs

    V(p) := sup {Σ(a∈K)c(a) : K finite atoms below p},
    μ(p) := V(p)/V(⊤).

Atomicity makes V(⊤)>0 and μ faithful. The lemma proves complete additivity over represented disjoint families, and in particular countable additivity. Thus (4)⇒(3)⇒(2)⇒(1). No atom enumeration, ordering within a fibre, or countable Choice is used. ∎

## 5. The precise Choice boundary

To turn ℓ into an injection, for each n choose an injection i_n:A_n→{0,…,m_n−1}. The set of candidates is nonempty and internally finite. Countable Choice for these finite candidate fields gives the i_n. Then

    a ↦ pair(ℓ(a), i_ℓ(a)(a))

is an injection into N. Conversely an injection is already a finite-fibre labelling. Thus represented countable Choice for finite fields is sufficient for exactly the missing bridge in the original theorem.

There is a precise **uniform** converse in ordinary interpreted mathematics. The assertion that every represented finite-fibre numerically labelled field is numerically countable implies countable Choice for finite fields. Given nonempty finite X_n in one fixed represented sort, use the tagged field

    A := {(n,x) : x∈X_n}.

The first coordinate is a finite-fibre labelling. An injection j:A→N then picks from each X_n the unique x minimizing j(n,x). This is an admitted choice graph. All tags and graphs are fixed-type codes; no forbidden individual-output operation is required.

Equivalently the **uniform Boolean-algebra claim** that every represented atomic complete Boolean algebra admitting a faithful state has countable atoms implies this finite Choice principle: apply it to the represented powerset algebra of A. Its atoms are the admitted singletons, and §4 supplies its faithful state. This does not assert that the single proposition-algebra instance at type t alone implies all those Choice instances.

## 6. Full Gallin model with finite-pair worlds

Here is a model illustration with an explicit metatheoretic condition, not a new consistency proof for that condition. Assume ZF and a sequence (A_n) of disjoint two-element sets having no choice function. Tagging an initially nondisjoint family supplies disjointness. Put W=⋃_n A_n and take the individual set to be the ordinary N. Choose one designated world from A_0; this single existential choice is not a choice function for the sequence.

Use the full constant-domain Gallin interpretation: propositions are P(W), and every allowed relational function domain is the full set of functions between the previously constructed domains, ending in P(W). Application is evaluation, equality is the constant proposition W or ∅ according to object identity, and quantifiers and Boolean operations are evaluated world by world. Set separation/replacement construct these operations and every lambda abstraction; constant functions give nonempty higher domains. H-equivalent formulas agree at every world, so their abstractions agree as functions, verifying the Logical Equivalence requirement of C.

Boxed Plenitude holds without metatheoretic Choice: at any fixed world, a total single-valued relation determines its unique-output function by replacement, and that function is in the full domain. No simultaneous choice of a function at every world is required. The individual N gives quantified Infinity_e. Its full Frege number and Dedekind-real interpretation is the ordinary one in this metatheory; the ordinary numeral field is itself an admitted inductive field, excluding additional number objects from the impredicative N_e.

For p⊆W define

    μ(p) = Σ_(n∈N) 2^(−n−1) · |p∩A_n|/2.                   (2)

The increasing bounded partial sums define a Dedekind real in ZF. The function is admitted in the full graph-coded hierarchy. The world labelling by n has two-element fibres; the proof of §4 shows (2) is faithful and completely additive, with μ(W)=1. No point in A_n was selected to define it.

Yet W has no injection into N. Such an injection would choose from each A_n its member with the smaller numerical label, contradicting the metatheoretic premise. Fullness makes this exactly failure of the internal N_e-countability condition as well. Thus **conditional on the stated choiceless metatheory**, this is a model of B₀ with faithful probability and without countable worlds in the injection sense. The finite-fibre replacement is substantive; the old injection conclusion cannot simply be retained after dropping its choice resource.

This is a full-model construction from a supplied family, not an analysis of new forcing or an assertion that the family exists in ZFC. It is not a database model entry. The probability formula and the distinction between a single designated world and simultaneous pair choice are part of the construction just given.

## Dependencies removed and retained

Boxed Functional Choice is removed from the main four-way equivalence, with **no replacement choice assumption**. Boxed Plenitude, quantified Infinity_e, represented graph comprehension, and internal real completeness remain. To retain the original injection/countability conclusion, only the displayed countable finite-choice principle is added. The conditional model in §6 illustrates the distinction; no consistency proof for its metatheory or database verdict change is claimed.

Sources: original probability note, §§1–4; original world representation, §15; original Gallin core, §7; the two companion refinements linked above. These are unpaginated research sources. Recorded background: Bacon–Dorr, Classicism, draft 16 May 2023, §2.3, pp. 31–33, for boxed Plenitude and its atomicity/completeness consequences. The finite-fibre characterization and the weaker dependency package are proved here, not attributed to that paper.
