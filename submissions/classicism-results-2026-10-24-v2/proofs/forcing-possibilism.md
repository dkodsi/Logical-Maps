# Forcing Possibilism, Choice and Infinity

Ordinary proofs developed with OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026; direct source `misc`. Previously recorded constructions and arguments retain their attribution.

Forcing Possibilism (FP) here has exactly the database’s strict-smallness formulation:
For each admitted carrier type σ, every represented complete Boolean algebra (X,R) satisfying Dedekind-finiteness OR an injection into the proposition domain with no reverse injection is order-isomorphic to [0,p] for some p≠top. Quantifiers, cardinal comparisons, completeness, and isomorphisms are unboxed. Degenerate one-element BAs are allowed, using p=bottom. The type system is C's relational system, including e as a carrier and allowing στ only for τ≠e.

Write I_e,I_t for the quantified Frege-cardinality infinity axioms; S_e,S_t for their finite lower-bound schemata; FC/IC for Functional/Intensional Choice. Except in the explicitly marked socks argument, constructions below use ordinary external ZFC. This is the metatheory of the countermodels, not an extra premise inserted into C.

## 1. The cardinal lemma and the reason internal notions are controlled.

Every infinite complete Boolean algebra B in ZFC contains a countably infinite pairwise disjoint family (b_n) of nonzero elements. If it has infinitely many atoms, choose countably many. If it has finitely many atoms, their join cannot be 1 unless B is finite; its nonzero complement is atomless. Repeatedly split a nonzero remainder into two nonzero pieces, retaining one and continuing in the other. Completeness then gives an injection P(N)→B by S↦∨_{n∈S}b_n: meeting with b_k detects whether k∈S. Hence |B|≥c, where c=2^aleph0.

In all uses of this lemma below, the evaluation point has every external actual relation on each admitted domain: every subset, order, injection graph, and isomorphism graph is the actual extension of an entity. Therefore internal CBA completeness tests every external subset, internal relational injection means actual set injection, and internal Dedekind-finiteness means ordinary finiteness in external ZFC. This justification is essential. We are not assuming the same equivalence for arbitrary Henkin or choiceless models.

## 2. Full countable S5: FP with the preferred package, and the CH countermodel.

Take worlds W=N, constant individuals D_e=N, D_t=P(W), and full admitted function domains D_{στ}=D_τ^{D_σ}. Evaluate a proposition by membership of the current world. Logical operations and quantifiers operate pointwise, equality is genuine identity of domain entities, and necessity is equality to top. This is the standard full constant-domain S5 model of C (the existing full-infinite-s5 construction, specialized to W=N, with infinitely many fixed individuals).

For each world and serial relation U, external Choice chooses an output for every input, and the selecting function belongs to the full function domain. Thus every FC instance holds at every world: □FC. In particular □Rigid Comprehension and IC hold. These can also be seen directly: rigidify an actual relation by giving it that same extension at every world; for necessarily instantiated F, choose one instance at each world and form the intension having those singleton extensions.

Both genuine infinity axioms hold at every world. Full higher domains make the impredicatively defined finite cardinalities exactly the standard finite-successor orbit, and no standard finite cardinality counts the infinite e or t domain. This is stronger than merely validating S_e,S_t.

There are c propositions. By the cardinal lemma, any qualifying CBA is finite: the strictly-smaller clause rules out every infinite CBA, and Dedekind-finite is finite here. A finite BA with n atoms is isomorphic to P(p)=[0,p] for any n-element subset p of N. Such p is proper. The degenerate case takes p=∅. The required mixed-type isomorphism graph exists by fullness. This works at every carrier type and every world, so even □FP holds.

Non-contingency of CH holds as well. Every internally complete ordered field at any world is an externally complete ordered field, because all its subproperties and operation graphs are present. Using the intended standard completeness condition on nonempty bounded subsets, it is isomorphic to the ambient real field. Relations used by second-order analysis and CH are also full. Consequently all such structures at all worlds agree on CH with the ambient universe. If ambient CH holds, the necessary-CH disjunct holds; if it fails, the necessary-not-CH disjunct holds. This does not decide CH.

It follows that the exact encoded conjunction
□Rigid Comprehension + IC + FP + Non-contingency of CH
has a model. The recorded incompatibility concluding false is REFUTED AS ENCODED. The missing step in its suggested forcing proof is the existence of a qualifying CH-altering forcing algebra: strict FP requests only finite BAs in this model. Preserve the source attribution and distinguish the source appendix's different non-strict bound; do not hedge the verdict on the exact displayed strict formula.

Replacing D_e=N by a singleton preserves □FC, IC, FP, and I_t while refuting S_e and I_e. Thus FP does not force individual infinity, even with FC or IC added.

## 3. Independence over the preferred package and the exact ZFC S5 classification.

Let B=RO(2^N), the regular-open algebra of Cantor space. It is complete and atomless. A countable basis codes its opens by reals, giving |B|≤c. Pairwise disjoint cylinders [0^n1] give P(N)→B by their regular-open joins, giving |B|=c. These particular cardinal bounds are choice-free.

Now take full S5 with W=P(N), D_e=N. Its proposition algebra is P(W), of cardinal 2^c>c. Represent B on a subset of D_t, with its order and all tested subproperties present by fullness. It is internally a strictly small CBA. Yet every interval [0,p]=P(p) is atomic when nontrivial, or degenerate when p=∅. None is isomorphic to the atomless B. Thus FP fails, while □FC+I_e+I_t still holds.

Together with §2, this establishes relative independence of FP over C+□FC+I_e+I_t. The negative half was ALREADY in the inspected upstream database: full-permutation-group-infinite-set-individuals-fixed-infinite and its Σ-true-atom variant satisfy the package and refute FP via forcing-possibilism-continuum-arrows. The new positive countable-S5 specialization supplies the missing half.

More generally, for infinite W in ZFC:

$$
\mathrm{FullS5}(W)\models\mathrm{FP}\quad\Longleftrightarrow\quad 2^{|W|}=2^{\aleph_0}.
$$

If equality holds, the finite-only argument applies. If the cardinal is larger, the Cohen algebra qualifies and atomicity refutes FP. This is not equivalent to “W is countable”: the continuum function can have a plateau. Individual cardinality and the specified Σ interpretations do not affect this pure FP classification. Do not attach a uniform FP verdict to the existing arbitrary-infinite-W family.

## 4. A new ordinary countermodel: FP does not imply IC, even with both infinity axioms.

Use two existing C components:
A = symmetry-constrained-full-all-maps, the all-maps model on three individuals. Its proposition BA has 32 elements: the five orbits of maps under permutation correspond to the five kernel partitions of a three-element set.
B = full countable-world S5 with a singleton individual domain.

In A, fix an individual a and put F_A=λx.(x≠a). This is necessarily instantiated: at an arrow h its extension is the two individuals other than h(a). No necessarily unique subproperty G≤F_A exists. At a constant arrow c_j, any such G must have a singleton extension inside the other two individuals, but the transposition swapping those two fixes c_j and symmetry requires that singleton to be invariant, impossible. Alternatively the record's explicit type-t IC witness gives the same obstruction.

Add a fresh root o using the free-root construction already proved in research/2026-10-22/notes/homogeneity-amalgamation-lane.md §8.2 (line 191 onward). Choose D_e(o)=N (or a singleton) and arbitrary maps into the distinguished individual domains of A and B. For each relational τ=σ_1…σ_k t set
D_τ(o)=P(D_{σ_1}(o)×…×D_{σ_k}(o)) × D_τ(A) × D_τ(B).
For t the first coordinate is a truth bit. There is a distinguished arrow into each component and all composites, with no arrows back. Transport is component projection, application slices the root extension and applies the projected component, and abstraction/quantifiers/equality have their actual root interpretations and corresponding component values.

This is a C model: β and η hold by slicing and componentwise interpretation; all H axioms hold at the root by ordinary actual truth and equality and in the components by assumption. Every lambda-denotation is admitted, since its root truth set is unrestricted and its component denotations exist. H-provably equivalent formulas have equal root extensions and equal abstractions in each C component, establishing Logical Equivalence. This uses only admitted relational types and imposes no surjectivity requirement on the e maps.

At the root:
D_t(o)=2×32×P(N) ≅ P({*}⊔5⊔N) ≅ P(N).
All actual root relations are present. Thus the cardinal lemma applies internally at the root, and strict FP holds by realizing finite BAs as finite proper intervals.

Lift F_A to F whose actual root extension is universal and whose B component is universal. Its existential proposition is top in every coordinate, so F is necessarily instantiated. Any root IC selector would project into A to a necessarily unique subproperty of F_A, contradiction. Therefore IC FAILS at o.

With root D_e=N, actual fullness also gives both quantified infinity axioms at o. Thus FP+I_e+I_t does not imply IC (and in particular FP+S_e does not imply IC). Do not assert boxed FP for this model: the finite bad component itself fails FP. This construction and its type/quantifier/transfer details were independently checked by the root and two collaborating agents as ordinary mathematics; no human-check or Lean status is asserted.

## 5. The infinity-schema separations: ordinary compactness/Henkin proofs.

For each n≥1 take full S5 with n worlds, n individuals, and full finite domains. Then |D_e|=n and |D_t|=2^n. It satisfies □FC and IC, but □¬I_e and □¬I_t: the n-th and 2^n-th finite cardinalities respectively count their entire domains at every world.

Every finite collection of lower-bound instances from S_e and S_t holds in all sufficiently large factors. Many-sorted Henkin compactness (equivalently a nonprincipal Henkin ultraproduct in ZFC) therefore produces a C model of
□FC + S_e + S_t + □¬I_e + □¬I_t.
The varying numeral witnesses become nonstandard internal finite cardinalities. The limit is Henkin, not externally full. Hence S_e→I_e and S_t→I_t both fail, even with IC or □FC and the other infinity schema added.

The mixed separator uses W=N fixed, with n individuals in the nth full S5 factor. Every factor has □FC+□FP+□I_t+□¬I_e. Compactness/ultraproduct preserves each fixed finitary typed schema instance and yields additionally all of S_e. Thus
I_t+S_e does not imply I_e,
even after adding □FC and strict FP. The first finite-world ultraproduct does not establish this mixed separation, since it falsifies I_t.

## 6. The socks variants: FP fails by a choice-free argument.

In the recorded ZF+socks variants, W is the union of a numbered sequence of pairwise disjoint two-element sets P_n having no choice function. The map S⊆N ↦ ⋃_{n∈S}P_n injects P(N) into P(W). There is no injection P(W)→P(N): compose one with w↦{w}, then use the ordinary lexicographic linear order on reals to choose the lesser image in each pair, contradicting the socks hypothesis.

The Cohen algebra above has cardinal c in ZF by its explicit basis/cylinder injections and Cantor–Bernstein. Thus it injects into P(W), while P(W) cannot inject into it. Represent it at type t by the available full relation domains. It is strictly small, but no interval of P(W) can represent its atomless algebra. Hence FP fails in all these socks S5 variants, irrespective of individual-domain or Σ-true-atom settings.

Do NOT carry this conclusion over to ZF+¬AC_ω(R), where the group's convention sets W=N. The three inspected models with these assumptions remain unsettled by this audit. Two separate issues block importing the ZFC proof: possible infinite CBAs strictly smaller than the reals, and FP's separate Dedekind-finite disjunct, which can admit carriers not even injecting into the reals. No uniform proof or countermodel for those stated assumptions was supplied, and no literature-openness claim is made.

## 7. Existing records, scope and unresolved cases

The strict-FP/CH incompatibility was already refuted by the recorded full-action models and the earlier lottery audit. The countable S5 model is an additional witness, not a new refutation of the source appendix’s different non-strict principle. The negative independence direction in §3 was also recorded. The new contributions include the positive preferred-package witness, the exact full-S5 classification, the free-root separation from Intensional Choice, and the Infinity-schema separations.

The screenshot review supplies counterexamples to eleven displayed core entailments and eighteen previously unwitnessed pairwise compatibilities; neither number counts independent discoveries. Recorded free-monoid models already refute FP implying Functional Choice, including the specified individual-infinity variants. Singleton-individual countable S5 gives the further failures of individual Infinity described above. The arbitrary-infinite-world families require §3’s cardinal qualification. The socks variants fail FP by §6; the three no-countable-choice-for-reals cases remain unresolved by this audit, without a claim of literature openness.

The inspected database is the local 23 October upstream checkout, not a fresh remote-head fetch. Relevant records are forcing-possibilism, forcing-possibilism-countably-many-arrows, forcing-possibilism-continuum-arrows, full-infinite-s5, full-permutation-group-infinite-set, and necessary-rigid-comprehension-intensional-choice-and-forcing-possibilism-incompatible-with-non-contingency-of-ch. Research-task reviews are not human checked_by endorsements. No database verdict or Lean status is changed by these ordinary proofs.
