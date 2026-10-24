# Observer separation over H

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026.

An observer is an admitted operation on propositions. A separation principle says that distinct propositions—or, at full scope, distinct relations—can be distinguished by the truth values reported by suitably qualified observers. Changing what observers must preserve gives the branching map studied here.

Start with the [dedicated results page and thematic diagrams](GRAPH.md). The [theorem tables](MAP.md) give exact equivalences, countermodels and the remaining questions; each result links to its proof. [Main Results](../../MAIN-RESULTS.md#h-observer-separation) gives the shorter synthesis.

## Fixed framework

Use H in the existing relational type system: e and t are base types, and arrow types have relational codomain. Observers have type tt. All types index schemas externally; no object-language quantification over types is introduced. Every observer qualification uses a finite list of quantified types. Top and Bottom retain the fixed abbreviations a∨¬a and a∧¬a, where a=∀p p.

The principal separation form is

$$
S[R]:=\forall p,q\, .\,p=q\leftrightarrow\forall E\, .\,R(E)\to(Ep\leftrightarrow Eq).
$$

Preservation means full identity of composite operations unless a comparison tier is explicitly labelled material or pointwise. Acceptance of Top, fixing Top, rejection of Bottom, and fixing Bottom are distinct conditions. Primitive connectives and their classically equivalent derived versions remain distinct until an identity has been proved. The same applies to primitive and derived quantifiers.

Propositional and full relational separation are recorded separately. Optional principles, including Functionality, identity bivalence, NI, ND, BF, and C, belong in the premises of individual claims. Ordinary H does not license modal normality, C's Intensionality, or the guard-normalization theorem proved over C.

## Reading the map

The primitive-package classification fixes both the preservation tier and the separation scope. It treats conjunction, disjunction, negation and quantifiers as independent primitives; its exact order does not transfer unchanged to a presentation defining one from the others. A common class preserving two operations can be stronger than two separate classes that each separate.

The three preservation tiers are agreement in truth, identity of outputs at every input, and identity of whole composite operations. The map calls them material, pointwise and whole-operation preservation. Comparisons between them retain their stated admission, finiteness or Functionality premises. Internal Frege finiteness of an observer's image is distinct from finiteness of the entire proposition domain.

For complete logical observers, a qualified right inverse means an admitted same-list observer $F$ with $E\circ F=I$; a qualified left inverse means $F\circ E=I$. These are whole-operation identities. Right-inverse separation is exactly reversible separation. Left-inverse separation lies strictly between reversible separation and ordinary logical separation (OS), and is incomparable with ☐OS. Under internal Frege finiteness of all propositions, left-inverse, reversible and endpoint separation coincide. The theorem compares separation principles, not the individual classes of observers.

The [upper logical region](GRAPH.md#9-the-larger-region-above-c--bf) connects these results to C, BF, C5, Atomicity, No Pure Contingency and Extensionality. The [model table and frontier](GRAPH.md#10-models-open-comparisons-and-research-status) distinguish established non-implications from unresolved comparisons. Only the finite primitive-package family has a complete classification; the wider H investigation remains active.

The [Zorn theorem](zorn-affine-character-extension.md) supplies admitted infinite affine characters and extends partial characters, using the preorder instance at type tt as an explicit H premise. [Plenitude](partial-reversible-normalization.md) separately supplies involutive separating witnesses for negation and each affine operation; whole-operation identities retain their Functionality premises.

The [component-shift model](component-shift-symmetry-reversible-gap.md) satisfies C5 + ☐SplitMono + No Pure Contingency but fails reversible separation. Its obstruction uses an individual parameter and a first-order relation whose tuple values are endpoints. This complements the earlier finite-block model, whose obstruction is a closed pure sentence. Reversible separation forces noncontingency for the specified endpoint-relation parameter formulas as well; arbitrary higher-type parameters are not covered.

The [lattice-character theorem](zorn-lattice-character-extension.md) extends the Zorn route to admitted prime filters and partial lattice characters, giving exact material lattice and Boolean converses. [Compatibility identities](negation-affine-compatibility.md) connect negation with an affine operation, or link two affine operations, over H; Plenitude then supplies the corresponding involutions. Quantifier preservation is not inferred from these connective results.

The [left-inverse decomposition](left-inverse-separation-decomposition.md) is a theorem over C + BF for each fixed output type and finite list containing t. Its full-H form is a schema of disjunctions, not a single choice between two full theories. The [two-colour model](finite-pinning-dedekind-propositions.md) separates internal Frege finiteness from the weaker condition that every admitted injective proposition operation is onto: that condition equates the inverse orientations but does not imply endpoint separation.

Current OS plus [Plenitude at (t,t)](plenitude-endpoint-bridge.md) is exactly endpoint separation; full Plenitude gives the same equivalence. The independent admission theorem is C + BF (type t) + Plenitude at (t,t) iff C5 + Actuality.

[Surjective observers](surjective-logical-observers.md) have every proposition as an output. This does not itself supply an admitted operation choosing preimages. Over C5, a definable kernel and fibre representative do supply a qualified right inverse, so C5 + surjective separation is exactly Rev. Over H, surjective and left-inverse separation are incomparable: the [omega-chain classification](omega-chain-surjective-observers.md) and the finite-block model give the two directions, even over C + ☐BF + ☐OS.

The [linear/circular fibre model](linear-circular-fibre-left-inverse-gap.md) satisfies C5 + ☐OS, has atomless propositions and makes every admitted proposition injection onto, yet fails left-inverse separation. A closed pure sentence about ordering infinite amorphous cells proves the failure.

The [order-action theorem](reversible-semilattice-order-actions.md) gives a positive atomless region over H: an admitted order-primitive action on the interior of a bounded dense chain, with an interior truth contrast, supplies reversible meet separation. The maximal invariant truth-compatible congruence is the exact obstruction. A rational-chain full-function model has joint reversible meet/join separation and Functionality while C fails.

The [fixed-point criterion](fixed-point-symmetry-left-inverse-separation.md) gives one uniform qualified left-inverse pair from a specified infinite sequence fixed by a source symmetry group. At the trivial-symmetry object of the qualitative-contrast model it establishes C5 + SplitMono without ☐OS or ☐SplitMono. Thus SplitMono and ☐OS are incomparable even over C5.

[Full cancellative monoid models](full-cancellative-monoid-observers.md) have ☐SurjSep; a specified infinite sequence of distinct units also gives ☐SplitMono. The monoid ℤ×ℕ has both while C5 and Rev fail. Consequently SurjSep + SplitMono lies strictly below Rev and strictly above each factor, even when the two conjuncts below Rev are separately boxed.

The [truth-gap characterization](reversible-truth-gap-chains.md) identifies reversible chain separation with gap-density and transitivity on adjacent pairs, assuming a greatest false and a least true proposition. Plenitude at (t,t) and the stated order quantifiers supply that truth cut. The complete split interval is atomless and preserves both quantifier families reversibly while C fails; negation preservation is absent.

[Convex-block and finite-factor reductions](reversible-semilattice-local-global.md) give exact criteria for specified admitted actions: transitivity on blocks or factors, together with separation by the stabilizer of the crossed block or true factor. The lexicographic-chain and finite-product models extend the atomless examples beyond primitive actions and beyond chains.

[Individual surjectivity persists](root-truth-profile-surjective-separation.md) over C + BF (type t), but full SurjSep gives neither ☐OS nor ☐SurjSep, even with ☐BF and ☐Functionality. The root truth-profile extension provides the countermodel. Thus Rev ⇒ ☐SurjSep ⇒ SurjSep and ☐SurjSep ⇒ ☐OS are strict; SurjSep does not imply ☐BF, with failure at every admitted type in the integer-shift predecessor model.

[Canonical adjoints and image factorization](canonical-adjoints-and-image-factorization.md) construct admitted order adjoints L ⊣ E ⊣ R for every Good-t observer over C5. Their preservation laws characterize injection, surjection and reversibility; the image floor equals native necessity exactly for endpoint-valued observers. For a Boolean observer over C5, commuting with native necessity or possibility is exactly injectivity, without a quantifier-preservation premise.

The [integer-shift predecessor](integer-shift-predecessor-contingent-barcan.md) satisfies full typed SurjSep and current BF while ☐BF fails at every admitted type. It combines finite-pin approximation by split epimorphisms, invertible integer translations and the root truth-profile construction. This settles SurjSep ⇒ ☐BF negatively.

**Lean certified:** H + OS ⇒ C + BF with explicit endpoint identities. [Certificate scope and evidence](../../evidence/RESULT-INDEX.md#logical-observers).
