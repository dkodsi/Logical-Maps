# Effective parametrization of completion spaces and fresh-constant conservativity

OpenAI Codex (GPT-6), 22 October 2026. Follow-up to `exact-completion-model-spectra-20261022.md`; ordinary mathematics only. Main records unchanged.

## 1. Decisive topology verdict

**Do not claim that an arbitrary fixed binary DNR^A selector d computes a homeomorphism from Cantor space onto the full completion space Comp(T).** In the positive and Max cases under audit, that is generally false. It would force A′≤_T d, whereas relative-low PA degrees over A need not compute A′.

The correct exact threshold is:

> For each fixed consistent A-c.e. T satisfying the finite-output hypothesis (2.1) in `exact-completion-model-spectra-20261022.md`, an oracle X computes a continuous surjection 2^ω→Comp(T) if and only if A′≤_T X. This is also equivalent to X computing a homeomorphism with X-computable inverse.

For the theories here, A is ∅ or 0′, so parametrizing **all** completions has threshold 0′ or 0′′ respectively. Computing one completion or model has the weaker PA-over-A threshold. The spaces are topologically Cantor spaces, but the effectiveness of a parametrization is a separate question.

## 2. Why even a surjection computes theoremhood

Suppose F is an X-computable total map from 2^ω onto Comp(T). An output coordinate is the characteristic bit for one original sentence φ. Its computation halts for every input real, and each such halting computation asks only finitely many input bits.

For the fixed output coordinate, enumerate all finite input strings whose oracle computations determine that coordinate using only the specified bits. They give basic clopen cylinders with their computed output bits. Dovetail until the cylinders found cover Cantor space. Whether a finite family of cylinders covers Cantor space is decidable, and compactness plus totality guarantees this search terminates. Thus X can determine whether the output bit is 1 for at least one input real, or is 0 for every input real.

By surjectivity,

    ∃x∈2^ω F(x)(φ)=1
       iff some Γ∈Comp(T) contains φ
       iff T+φ is consistent.

Consequently X decides the consistency of every one-sentence extension. Equivalently, it decides theoremhood, since T⊢ψ iff T+¬ψ is inconsistent. The audited effective-inseparability reduction makes Th(T) A-c.e.-complete under ordinary computable many-one reductions. Hence A′≤_T X.

Only a forward total surjection was needed. Adding an effective inverse cannot remove this lower bound. The claim also rules out a merely d-computable homeomorphism onto Comp(T) when d is a relative-low PA-over-A degree strictly below A′.

This compactness argument concerns computation on the compact represented input space 2^ω; it does not use full higher-order model compactness.

## 3. A′ suffices for a homeomorphism and its inverse

Let ψ_0,ψ_1,… enumerate all original sentences. A′ decides whether T+Δ is consistent for each finite Δ, because a contrary proof is A-c.e. Every consistent finite extension remains incomplete, by the ordinary computable independent-sentence splitter proved in the companion supplement.

Construct a full binary tree of consistent finite conditions. At a node, suppose all ψ_i below index m have been assigned signs in its finite condition Δ. Search j=m,m+1,… in order. At each j use A′ to test consistency after each sign of ψ_j.

* If only one sign is consistent, add that forced sign and continue.
* At the first j for which both signs are consistent, create the two children by adjoining the respective signs, and stop this node's search.

The search must stop. Otherwise every sentence would be decided by T+Δ, contradicting its incompleteness. Each child advances the decided prefix strictly, so along any infinite branch every sentence is eventually decided. The branch gives a unique complete consistent Γ extending T. Conversely every Γ∈Comp(T) follows a unique branch, because the intervening forced signs hold in every completion through that node and the split sentence selects exactly one child.

Reading a branch therefore computes its completion in A′. Reading Γ computes its branch in A′, by performing the same finite searches and querying Γ at each split sentence. Both procedures are total and continuous. They are inverses, giving an A′-computable homeomorphism. An oracle X≥_T A′ can perform the same construction.

This proves the sharp threshold in §1, not just a sufficient upper bound.

## 4. What a fixed DNR selector really does provide

Fix a binary DNR^A function d. In the companion exact-degree construction, use d for the ordinary sentence-decision step and an arbitrary input real X for the subsequent independent-sentence bit choice. This gives a d-computable continuous injection

    F_d : 2^ω → Comp(T).

Its inverse on its image is ordinary computable: reconstruct each ordinary decision from the output completion, compute the next independent sentence, and read the encoded X-bit. Thus F_d is a homeomorphism onto its compact, hence closed, image. The image is a Cantor subspace of Comp(T), and it is effectively closed relative to d by effective compactness.

One should not replace “onto its image” by “onto Comp(T).” In particular, the d-guided ordinary decisions may discard entire open regions of Comp(T).

If desired, encode X⊕d rather than X in the independent-sentence steps. The resulting embedding remains d-computable, its inverse onto X is computable on its image, and every output completion has exact degree deg(X⊕d): its decoder recovers both X and d. This produces a closed Cantor subspace all of whose members compute the fixed selector. It is useful for a degree-controlled family, without implying a global parametrization.

## 5. Fresh constants preserve the fixed H/C framework

**PASS:** the Γ-preserving Henkin construction only needs fresh constants of already admitted types. It does not need new type constructors, functions with output e, a strengthened Logical Equivalence rule, or a new necessitation rule.

For each finite H-proof involving new nonlogical constants c̄, first rename bound and generalized variables to avoid collisions, then replace the constants by distinct fresh free variables z̄ of the same types. Because the constants have no axioms and appear only as arbitrary terms, every H-axiom and rule instance remains an H-instance. Its usual variable restrictions are preserved by the freshness and renaming. The translated final formula is therefore an H-theorem with parameters z̄; its universal closure is also an H-theorem.

In particular, an expanded-language Logical Equivalence instance comes from an H-theorem φ(c̄)↔ψ(c̄). Replacing c̄ by z̄ gives the corresponding parameterized H-theorem in the old pure language. Applying C's fixed Logical Equivalence schema gives the identity of the corresponding lambda abstractions with free parameters z̄, and universal closure makes that identity valid for every parameter assignment in every old C-model. Interpreting c̄ by any chosen tuple of entities then yields the desired expanded instance. No optional Γ sentence was promoted to an H-theorem.

Every old BBK C-model consequently expands by arbitrary interpretations of the fresh constants to a model of the entire fixed expanded C schema. This is the conservativity fact used in the existential-closure consistency test. The additional Henkin witness axioms are not asserted to be logical C-theorems; their consistency is established by interpreting each fresh constant as the required witness.

All witness constants must be outside Γ's original language. At each witness step the selected constant must also be absent from the current finite commitment set and from the existential formula being witnessed. These are effective finite checks against the fixed disjoint constant supply. The complete original Γ is pure here, so it cannot secretly constrain a witness constant. If the theorem is extended to a fixed nonpure original language, the witness supply must be disjoint from that whole language, and the existential closure is taken only over newly adjoined constants.

The proof establishes conservativity for these fresh constants. It should not be generalized without checking to new nonlogical axioms, arbitrary language-changing inference rules, or prohibited individual-output types. None of those is needed by the construction.

## 6. Status

The topology threshold and fixed-selector subspace claims above are proved from the audited finite-output and theoremhood results. The parameter-elimination argument checks the mild language expansion required by the Γ-preserving model construction. No assertion about an effective parametrization of the copies of a fixed model is made.

Validation: no main records were edited. The bundle validator is run after saving this report; its result is reported in the parent update.
