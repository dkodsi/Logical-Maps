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

[Native necessity and injective separation](native-box-logical-observers.md) adds BoxSep and InjSep to the map. BoxSep gives ☐BF, ☐Functionality and .2; the .2 theorem already needs only propositional separation by Bottom-fixing observers commuting with native necessity over C. Over C5, Rev ⇒ InjSep ⇔ BoxSep ⇒ OS has both implications strict. Outside C5, BoxSep is incomparable with InjSep and SplitMono over C + BF, and with ☐OS even over C + ☐BF. The full consequence bundle does not recover BoxSep.

[Boolean transversals](injective-observers-and-boolean-transversals.md) classify qualified left inverses of an injective observer over C5 by a single admitted selector proposition, with an explicit bijection. The regular-open model has an injective fully logical observer with no qualified left inverse, but fails OS itself. InjSep versus SplitMono therefore remains open, both over H and over C5.

[Idempotent observers commuting with necessity](idempotent-native-box-observers.md) give a strict strengthening of BoxSep; adding C5 gives exactly Extensionality. In full models on finite rooted posets they separate exactly when all pairwise joins exist. The two-antichain family has exact thresholds; its seven-point member refutes the lower-bundle converse to BoxSep, and the diamond has ☐IdemBoxSep but fails .3 and C5. A three-point preorder refutes persistence of IdemBoxSep.

[Injective separation decomposes](injective-separation-decomposition.md), over C5, as Rev or OS plus a single injective observer whose image floor sends a true proposition to Bottom. The single propositional Good-t instance represents the full schema here, so the finite J-versus-K alternative is justified under C5. It sharpens the open InjSep ⇒ SplitMono comparison without resolving it.

[Modal reflection](native-box-reflection.md) makes current universally closed modal laws necessary under the specified BoxSep instance. It extends to the stated equality-free predicate-universal fragment, retaining both kinds of inner object quantifier and their exact variable-use restrictions. The conclusions .3 ⇒ ☐.3 and 5 ⇒ ☐5 remain conditional; ☐.2 already follows from C + BF (type t) + .2. The ordinary-separation countermodel does not separate reflection from the entire lower modal bundle.

[Fixed finite stabilization](bounded-stabilization-native-box-observers.md) gives the strict hierarchy $B_1\Rightarrow B_2\Rightarrow\cdots\Rightarrow\mathsf{BoxSep}$, with $B_1=\mathsf{IdemBoxSep}$. Every step is strict, including for the separately boxed schemas. One infinite full model has ☐BoxSep but fails every fixed bound on the same proposition pair. The coordinate-reader and join theorems extend to rooted posets of fixed finite external width. With C5, Rev or End, each $B_r$ is exactly Extensionality.

[Finite generation over an observer's image](finite-relative-image-generation.md) characterizes Rev over C5: for every fixed external $n\ge0$, separation by logical observers whose images need at most $n$ additional Boolean generators is exactly reversible separation. Injectivity is unnecessary for the same-profile involution theorem; it is required for the controlled left inverse. The condition is distinct from finite range and internal Frege finiteness.

[A true image gap without a true split kernel](injective-gap-without-split-kernel.md) refutes $J\Rightarrow K$ over C5, even when the displayed J observer has a qualified left inverse. It is a new verdict in the existing regular-open model, which fails OS. The comparison OS + J ⇒ Rev or K remains open. Finite relative generation supplies the positive case: K is exactly J with one additional image generator, equivalently any fixed positive finite bound.

[Exterior-arm posets](exterior-arm-posets-native-box-nonpersistence.md) show that BoxSep and every fixed $B_r$ with $r\ge2$ can fail to persist even on finite full posets. One ten-point model witnesses all these failures while retaining ☐OS, ☐BF, ☐Functionality, ☐Atomicity (type t) and ☐.2. Idempotence is hereditary within the poset family by the join criterion; its general preorder nonpersistence remains distinct.

[Canonical local support](local-transversal-support.md) has exact composition, patching and compatible-gluing laws. Over C5, separation by observers with full support, with currently true support, or in the range of the canonical normalization is exactly Rev. These individual qualifications are broader than fixed finite relative generation; full support need not itself be local or make an observer invertible.

[Selection from support](zorn-local-transversal-selection.md) uses the explicit additional current premises Boolean Completeness (type t) and Zorn's Lemma at t. For injective Good $E$, a qualified left inverse exists exactly when $L_Es_E=\top$; one killing $c$ exists exactly when $L_E(s_E\land\neg c)=\top$. Boolean Completeness supplies actual current chain joins, and Zorn supplies a maximal local transversal. The preceding maximal-support theorem does not require injection.

[Admitted local homogeneity](local-homogeneity-and-split-observers.md) gives a separate positive criterion: C5 + OS + a currently true homogeneous principal interval implies SplitMono, without J. Relative isomorphisms and their inverses must be admitted; an external decomposition does not suffice. The general OS + J ⇒ Rev or K question remains open.

[Bounded fibre degree](bounded-fibre-degree-logical-observers.md) gives another exact Rev characterization over C5: each fixed degree bound forces full local support and an involution with the observer's entire current profile. Degrees multiply under composition and add under Boolean patching. With both Boolean Completeness (type t) and Zorn at t, degree at most $n$ is exactly a partition into $n$ local sheets, and $\mathrm{FG}_k$ is equivalent to degree at most $2^k$. The bounds are fixed externally.

[Finite-image native-necessity separation](finite-image-native-box-observers.md), together with Actuality, is equivalent over C to internal finiteness of all propositions plus BoxSep, at every fixed relational output and finite list. Full scope recovers C over H. In full rooted-poset models with singleton individuals, FinBoxSep holds exactly when the frame is finite and has BoxSep; Actuality is not removed from the abstract theorem.

[Central logical observers](central-logical-observers.md) commute with every same-list Good observer. Their separation is Extensionality over C5. In the full finite rooted-poset family with singleton individuals it holds exactly on a singleton or two-point chain; CentreSep is incomparable with Rev and End over H. This is stronger than asking for a chosen pairwise commuting family.

[Finite colour patterns and completeness](finite-colour-propositional-completeness.md) gives ☐Boolean Completeness at t in the existing atomless two-colour model, together with ☐Rev, but without Actuality, completeness at tt or Zorn at t. Completeness at tt already gives Plenitude at (t,t) and Actuality over C5. C5 + OS reflects each assumed Boolean Completeness instance into necessity; this does not raise its type or settle the joint Boolean-Completeness/Zorn question.

**Lean certified:** H + OS ⇒ C + BF with explicit endpoint identities. [Certificate scope and evidence](../../evidence/RESULT-INDEX.md#logical-observers).

## Reversibility and finite bounds

- [Reversible separation and fixed propositions](reversible-fixed-proposition-characterization.md): over C5, Rev is exactly the assertion that only ⊥ and ⊤ are fixed by every reversible logical observer.
- [Invariant components and local support](invariant-components-and-local-support.md): the same invariant algebra is recovered from all logical observers on their local supports, with an admitted orbit-closure operation.
- [Central separation](central-separation-and-four-propositions.md) and [the reversible group centre](centre-of-reversible-logical-observers.md): two distinct exact four-proposition theories, both persistent, whose conjunction is Extensionality.
- [Bounded exponents](bounded-exponent-reversible-observers.md): a uniform power identity on every reversible observer gives an exact finite bound, with a common-refinement and cycle construction.
- [Finite-image reflection](finite-image-box-reflection.md): finite-image native-necessity separation forces internal finiteness; Actuality is a consequence at full scope.

## Group identities and finite observer families

- [Group identities](group-identities-reversible-observers.md): with Rev, every fixed nontrivial group law gives a sharp finite proposition bound; commutativity gives four and the metabelian law gives eight.
- [Invariant components](invariant-components-and-group-identities.md): over C5 without Rev, the same group law is exactly a bound on disjoint regions with overlapping orbit joins.
- [Internally finite families](internally-finite-observer-families.md): an internally finite family separates only an internally finite proposition class, already over H. With Rev, finiteness of the reversible observer class is equivalent to C5 plus finiteness of all propositions.

The main unresolved question is whether injective logical separation entails separation by logical observers with logical left inverses, over H or C5. See [Conjectures](../../CONJECTURES.md#observer-strength).
