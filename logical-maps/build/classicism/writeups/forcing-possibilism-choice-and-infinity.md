# Forcing Possibilism, full S5 models and a coalesced Choice obstruction

This integrates existing ordinary proofs with the precise native strict-smallness definition of FP. The common argument is that every infinite externally complete Boolean algebra has at least continuum many elements. In a genuinely full current relation hierarchy, the internal size and completeness tests are the corresponding external ones. This premise is verified separately for each model; it is not imposed on arbitrary Henkin models.

Sections 1–5 below are retained from the 23 October 2026 source, with original attribution. They supply an FP model of boxed Functional Choice plus both quantified Infinity axioms, a countermodel to FP with the same package, and a separate FP model refuting Intensional Choice. Section 5 adds the FP verdict to the already staged fixed-countable-world Henkin ultraproduct. The external choice assumptions are metatheory, not optional object-language axioms smuggled into the premise set.

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

```math
\mathrm{FullS5}(W)\models\mathrm{FP}\quad\Longleftrightarrow\quad 2^{|W|}=2^{\aleph_0}
```

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


## Integration scope and independent review

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Forcing Possibilism, Choice and Infinity*, 23 October 2026, §§1–5, unpaginated. Background constructions retain their attribution: Cian Dorr's full S5 reference model, 7 October 2026; Dorr's three-individual symmetry-constrained all-maps model and the repaired propositional IC obstruction by Claude Fable 5.1, 4 October 2026; Bacon–Dorr, *Classicism*, draft 16 May 2023, §3.5 pp.58–61 and Appendix E Definition E.2 pp.80–83.

The full S5 carriers use ordinary ZFC and the exact fixed sizes specified in their records. No uniform FP verdict is attached to the old arbitrary-infinite-world family or to its choiceless variants. The coalesced obstruction uses the three-individual component; the displayed individual witness is therefore legitimate, and the native component's separate t-witness is also available. Its current FP conclusion is not boxed.

The ultraproduct statement is instancewise many-sorted Henkin compactness: each fixed typed FP formula is true in every fixed-countable-world factor. It does not make the limit externally full or identify its internal finite cardinalities with external numerals. The pre-existing compactness proof and its original verdicts are preserved.

In these full S5 models the exact encoded strict-FP/CH incompatibility is refuted. This does not refute the different non-strict source formulation or assert that FP requires an infinite atomless algebra at every model. The integration does not create a proved incompatibility from the old conjectured record. Ordinary independent integration review dated 28 October 2026; no human or Lean certification is claimed.
