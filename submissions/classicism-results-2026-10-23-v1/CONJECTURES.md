# Questions, progress and negative results

Established answers, unresolved questions and mathematical obstructions.

[Main results](MAIN-RESULTS.md) · [Catalog](CATALOG.md) · [Evidence](evidence/RESULT-INDEX.md)

<a id="tr-rp-wrp"></a>
## Does TR + RP entail WRP?

**Position:** Refuted by a certified full C countermodel.

The finite compression model has full root TR and RP but fails WRP_et. The older colour-collapse example is independently certified, but fails RP at the next property type.

**Lean certified:** [`FINITE-COMPRESSION-SEPARATION`](evidence/RESULT-INDEX.md#finite-compression-separation). [`COLOUR-COLLAPSE-SCOPE`](evidence/RESULT-INDEX.md#colour-collapse-scope). [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications).

<a id="rc-tc"></a>
## Does Relational Choice entail Transversal Choice?

**Position:** Unresolved; sharper positive and negative criteria.

RC plus completeness gives Actuality and TC. The history construction reduces local TC to finite ambiguity in at least one missed cell. Finite code orbits obstruct symmetry-based countermodels. Class-code iteration preserves ambiguity, and orbit exhaustion is exactly Actuality.

Derive a suitable coherent chooser from RC alone, or construct a genuine full RC countermodel meeting the closure and code-orbit restrictions.

**Lean certified:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness): RC + BC ⇒ TC; the sharp Actuality theorem, Actuality-based TC, and the same-type RC + BC and CBC + CCC consequences. [`COEXTENSION-OPERATIONS`](evidence/RESULT-INDEX.md#coextension-operations): Orbit averaging and finite code towers; orbit/Actuality equivalence at t and inhabited unary types.

<a id="fc-finite-basis"></a>
## Can Functional Choice or ☐Functional Choice have a finite equivalent fixed-type basis?

**Position:** Negative ordinary results established.

Neither full Functional Choice nor its boxed form has an equivalent finite list of arbitrary pure fixed-type sentences over C. The Boolean-valued construction supplies ordinary separating models. The previously stated fixed-input and selector hierarchies remain in the supporting proofs.

**Lean certified:** [`CHOICE-NO-FINITE-BASIS`](evidence/RESULT-INDEX.md#choice-no-finite-basis).

<a id="max-atomicity"></a>
## Can pure Maximalism coexist with Atomicity (type t)?

**Position:** Refuted and certified.

The inconsistency theorem has no additional non-theoremhood or model-existence premise.

**Lean certified:** [`MAX-ATOMICITY`](evidence/RESULT-INDEX.md#max-atomicity).

<a id="pure-sp"></a>
## Is pure Strong Possibility consistent?

**Position:** Unresolved; exact criteria and construction obstructions.

Universal-identity and restricted-disjunction criteria are established. In the specified two-axiom test any required full-term embedding must leave every target arithmetic counterexample above its entire source number image.

Construct the genuine endpoint embedding or otherwise settle joint consistency. A noncofinal omitted-cut requirement rules out routes, not the theory.

**Lean certified:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria): The universal-core equivalence and the stated conditional disjunction criterion.

<a id="signature-sp"></a>
## Is SP consistent for one unary predicate constant and no individual names?

**Position:** Unresolved; first-stage sufficient criterion.

Nonempty K₁ already implies full signature SP consistency and is equivalent to weak named existence for the marked Max theory. Finite Herbrand extraction fails; the singleton-profile root is deleted. A successful fixed-domain kernel must be perfect and nonhyperarithmetic, with exact stabilization ordinal ω₁CK.

Prove weak named existence or give a globally empty witness open. Failure of K₁ or the stronger fixed-domain construction would not alone refute SP.

**Lean certified:** [`SP-SIGNATURE-CONFLICT`](evidence/RESULT-INDEX.md#sp-signature-conflict): The signature-splitting lemma.

<a id="lambda-equivalence"></a>
## Can fixed C be reconstructed without primitive lambda?

**Position:** Exact open-sequent equivalence established and certified.

An explicit classical lambda-free applicative calculus has exactly C’s consequences in its original language, including open contexts and finite lists of assumptions. A conservative named extension reconstructs arbitrary C terms and full contextual beta eta delta conversion.

**Lean certified:** [`LAMBDA-FREE-TRANSLATION`](evidence/RESULT-INDEX.md#lambda-free-translation). [`BETA-ETA-CONVERSION`](evidence/RESULT-INDEX.md#beta-eta-conversion).

<a id="observer-strength"></a>
## What relationships between observer separation and the established principles have been proved?

**Position:** Strict hierarchy and exact characterizations.

Over H, OS entails C + BF; full typed endpoint separation is equivalent to C5 + Atomicity (type t), and full typed factive separation is equivalent to Extensionality. Over C, the strict hierarchy is Extensionality ⇒ C5 + Atomicity (type t) ⇒ ☐OS ⇒ OS ⇒ BF. Atomicity (type t) + ☐BF implies OS. Over C5 + Actuality, OS, ☐OS and Atomicity (type t) are equivalent. Over C5, ☐OS + ◇Actuality entails ☐Plenitude; replacing ☐OS by OS does not suffice. Over C, necessary qualification is equivalent to qualification. ☐Boolean separation + ☐BF still fails to imply quantifier separation. No conjunction of the audited 132 catalog conditions characterizes OS. Given OS, uniqueness of the qualified logical observer is equivalent to Extensionality. OS does not entail ☐BF or ☐Functionality, witnessed by the finite-support natural-numbers/singleton model. Endpoint separation is equivalent to C5 + ☐OS + one atom. Reversible separation entails No Pure Contingency without atoms. Reversible separation is strictly stronger than C5 + ☐OS even among atomless models, witnessed by the finite-block symmetry construction and its contingent pure MC6 sentence. Qualified right-inverse separation is exactly Rev; qualified left-inverse separation is strictly weaker, even with C5 and its own boxed schema, and entails neither C5 nor necessary logical separation, BF or Functionality. The unrestricted N/Q and V/Q reductions are refuted by the ternary Cantor model, even with the three separate connective/quantifier separation schemas together and their boxes. Finite-domain and finite-image affine normalization are established; Plenitude at (t,t) supplies the stated normalization on infinite domains. Both arrows Rev ⇒ SplitMono ⇒ OS are strict, and SplitMono is incomparable with ☐OS. Internal finiteness of all propositions makes full SplitMono, Rev and endpoint separation equivalent. Zorn at tt gives infinite affine character extension; Plenitude gives the stated negation/affine involutive normalization. A component-shift model refutes C5 + ☐SplitMono + No Pure Contingency ⇒ Rev. Rev implies noncontingency for pure formulas with the stated finite individual and endpoint-valued first-order relation parameters. The fixed-list left-inverse decomposition isolates the reversible alternative or one qualified left-inverse pair with a true kernel element; its full-H form is a schema of local alternatives. Every admitted injection being onto equates full SplitMono and Rev, but the two-colour atomless model refutes the endpoint consequence. Zorn at tt supplies lattice/Boolean material converses and partial lattice-character extension; exact translation identities characterize the linked affine branches over H. Over H, endpoint separation is equivalent to OS + Plenitude at (t,t), OS + full Plenitude, C5 + OS + Actuality, C5 + OS + Boolean Completeness, and C5 + Atomicity (type t). Already C + BF (type t) + Plenitude at (t,t) is equivalent to C5 + Actuality. Over C5, each currently surjective Good observer at a finite list containing t has a definable admitted same-list qualified right inverse; hence Rev is equivalent over H to C5 + full surjective logical separation. Both chains Rev ⇒ SurjSep ⇒ OS and Rev ⇒ SplitMono ⇒ OS are strict. SurjSep and SplitMono are incomparable even over C + ☐BF + ☐OS, witnessed by the full omega-chain and the C5 finite-block model. Within C5, SurjSep is Rev and does imply SplitMono. The linear/circular fibre model satisfies C5 + ☐OS + D_t with atomless propositions but fails SplitMono at the explicit propositional list {t,e,et,eet,(et)t,((et)t)t}; a contingent closed pure sentence about infinite amorphous cells proves the obstruction. For an admitted group G of whole meet automorphisms over H, its common truth-profile relation is the largest admitted invariant truth-compatible equivalence and is a meet congruence; separation is exactly the absence of a nontrivial such congruence. On chains the obstruction is convex. An admitted order-primitive action on the interior of a bounded dense chain, together with an interior true/false pair, gives reversible meet separation. The rational-chain full-function model has joint reversible meet/join separation and all Functionality while C fails, with no atoms or truth extrema. Order primitivity is strictly weaker than order 2-homogeneity for admitted actions. A specified countably infinite sequence fixed by a source symmetry group in the all-bijections finite-pinning framework gives one qualified left-inverse pair with a true kernel element, normalizing ordinary separators at that source. At the trivial-symmetry object of the qualitative-contrast model, C5 + SplitMono holds but ☐OS and ☐SplitMono fail. Thus SplitMono and ☐OS are incomparable even over C5. Every full cancellative-monoid action model with singleton individuals satisfies separately boxed full SurjSep. A specified infinite sequence of distinct units also gives separately boxed full SplitMono, with one common qualified left inverse. A nonunit refutes C5. The concrete monoid ℤ×ℕ therefore refutes ☐SurjSep + ☐SplitMono ⇒ Rev, even over C + ☐BF. SurjSep + SplitMono lies strictly below Rev and strictly above each factor; its two witness families may be different. Over H, a bounded meet chain with a greatest false and a least true proposition and a specified admitted whole-meet automorphism group G has S[G] exactly when every nontrivial interval contains an adjacent pair and G is transitive on adjacent pairs. Plenitude at (t,t) plus Q_t/P_t supplying the admitted order bounds gives that truth cut, without C or Functionality. The full-function complete split interval is atomless and satisfies full reversible endpoint-fixing M,V,Q_Δ,P_Γ separation for every finite list while C fails; its observers need not preserve negation. For a specified admitted invariant convex block relation on the interior of a bounded dense chain, with each block without endpoints, global separation is exactly one crossed block, transitivity on blocks and separation by its admitted stabilizer. For a specified external finite central partition of a bounded distributive lattice preserved by G, global separation is exactly transitivity on factor units and stabilizer separation inside the unique true factor. Lexicographic rational-chain and finite-product atomless models give joint reversible M/V separation with all Functionality below C. Over C + BF (type t), Onto(E) implies ☐Onto(E), with E a free parameter; Good qualification is persistent over C. Full SurjSep nevertheless gives neither ☐OS nor ☐SurjSep, even with ☐BF and ☐Functionality. A root truth-profile extension of a fixed/free symmetry tail supplies this countermodel, with failure already at the future propositional Boolean instance. Thus Rev ⇒ ☐SurjSep ⇒ SurjSep and ☐SurjSep ⇒ ☐OS are strict. SurjSep does not imply ☐BF, with failure at every admitted type in the integer-shift predecessor model. Over C5, every admitted Good-{t} observer E has admitted order adjoints L ⊣ E ⊣ R, with Rq=∃p[(Ep≤q)∧p] and Lq=¬R(¬q). With k=RBottom and a=¬k, R(Ep)=p∨k and L(Ep)=p∧a, giving a Boolean order isomorphism from [Bottom,a] onto the admitted image. Injectivity is equivalent to RBottom=Bottom or LTop=Top; onto is equivalent to join preservation by R or meet preservation by L; bijectivity is equivalent to R=L or negation preservation by either adjoint. The admitted image floor ER and ceiling EL are idempotent, with ER≤I≤EL and mutual absorption. ER is an auxiliary S5 interior and equals native Box exactly when E is endpoint-valued. The endpoint-fixing envelopes T−q=(a∧Rq)∨(k∧q) and T+q=Lq∨(k∧q) preserve M/all Q and V/all P respectively, and coincide exactly when E is onto. Already for a Boolean E over C5, commuting with native Box or Diamond is exactly injectivity, without Q_t. The integer-shift predecessor model satisfies C + full typed SurjSep + BF while ☐BF_σ fails at every admitted type σ. In the finite-pinning tail over ℕ×ℤ and {∗}×ℤ, split epimorphisms approximate finite pins and invertible integer translations supply prescribed-coordinate kernel pairs. The root truth-profile extension combines all-type evaluation readers with those onto tails. A future object has nononto transport at every type and refutes every BF instance. Hence SurjSep ⇒ ☐BF is refuted with exact all-type scope.

Infinite nonprincipal material-versus-pointwise M/V separation outside the proved sufficient hypotheses; bare-H infinite affine character existence without an admission premise; further partial-signature reversibility and an intrinsic atomless-meet characterization beyond the primitivity, gap, convex-block and finite-factor theorems; further relationships with separately boxed inverse restrictions; an exact converse for Rev beyond its modal and endpoint-parameter noncontingency consequences.

**Lean certified:** [`LOGICAL-OBSERVERS`](evidence/RESULT-INDEX.md#logical-observers): H + OS ⇒ C + BF with explicit endpoint identities. Their omission is justified by the linked ordinary reduction proof. [`FULL-IDENTITY-OBSERVERS`](evidence/RESULT-INDEX.md#full-identity-observers): The propositional Atomicity characterization at quantifier type t, and the construction of observers at each fixed quantifier type. [`DIAGONAL-CHARACTERS`](evidence/RESULT-INDEX.md#diagonal-characters).

<a id="full-gallin"></a>
## Do internal completeness or bounded infinitary joins recover full standard models?

**Position:** Negative bounds and exact semantic characterization.

C5 plus propositional Atomicity and Arbitrary Atomic Joins characterizes full standard hierarchies. Infinitary Comprehension gives the same characterization with C5 and no separate Atomicity premise. A support construction separates every fixed parameter bound even with unrestricted formula size. The specified uniformly Σ₁-admissible set-coded calculus cannot be complete.

This is not an unrestricted impossibility theorem for every calculus. Full second-order validity remains the identified semantic benchmark.

**Lean certified:** [`INFINITARY-COMPREHENSION`](evidence/RESULT-INDEX.md#infinitary-comprehension): For universe-0 categorical premodels, term-denotation closure + unrestricted original-closed-type Infinitary Comprehension + ☐ND (type t) imply faithful full-standard representation; full standard models satisfy the corresponding infinitary axioms.

<a id="infinitary-sp"></a>
## Does countable named exhaustion follow from SP with infinitary resources?

**Position:** Proved for a specified semantic reference; conditional otherwise.

A single admitted non-name predicate gives reflection. The profile construction supplies Max(Td)-eligibility, so SP(Td) entails countable actual exhaustion. A numeral abstraction conflicts with Max referenced to original finitary C.

For a proposed syntactic C∞, supply the closed-identity separation bridge. Consistency of SP(Td) is not proved.

**Lean certified:** [`SP-INDIVIDUAL-CARDINALITY`](evidence/RESULT-INDEX.md#sp-individual-cardinality): The conditional monism/reflection lemma.

<a id="abstract-forcing"></a>
## Do the proposed abstract modal axioms alone give the forcing CH alternatives?

**Position:** Strict-smallness database formulation refuted by existing models; source correspondence unresolved.

The explicit full modalized cloud has the stated model-specific forcing-transfer argument. Separately, under metatheoretic Choice, existing countable-arrow full-action models satisfy the three abstract modal premises with strict-smallness Forcing Possibilism and CH non-contingency. The strict size condition demands only finite Boolean algebras in those models. The exact strict FP principle is independent over C + ☐Functional Choice with both quantified Infinity axioms; the full-S5 cardinal classification and FP-without-Intensional-Choice model are supplied separately.

Fix the exact source size convention and background type language, and establish the relevant transfer or extra forcing-algebra availability. The stronger non-strict formulation is not settled by this audit. Equivalence of the two lottery presentations remains under review.

<a id="pr-choice"></a>
## Does strong profile richness force full Functional Choice?

**Position:** Negative ordinary constructions supplied.

Supported nominal models realize exact individual profiles and arbitrarily high finite supported ranks while failing FC. Raw profile representation and rigid-profile PR have different boundaries.

**Lean certified:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra): The finite-profile and atomic-profile results.

<a id="full-choice-arithmetic"></a>
## Does ☐Functional Choice add ordinary arithmetic over ☐Plenitude?

**Position:** Resolved by an existing source-based ordinary proof; full Lean formalization absent.

Over C with quantified Infinity at e and t, replacing boxed Plenitude by full boxed Functional Choice adds no ordinary first-order arithmetic theorems. Both have the arithmetic consequences of C plus numerical noncollapse at e, and this remains true after adding boxed quantified Infinity at every admitted type.

The proof uses McLarty’s number-preserving interpretation.

<a id="max-arithmetic-equality"></a>
## What exactly is the ordinary arithmetic theory of pure Maximalism?

**Position:** Exact equality has an ordinary written proof; full Lean certificate absent.

The source proves both inclusions in

$$
\operatorname{Th}_{\mathrm{arith}}(\operatorname{Max}(C))=\operatorname{Cn}\bigl(T_{\mathrm{arith}}\cup\mathrm{True}_{\Pi_1}\bigr).
$$

It also states the specified extensions by current graph-choice principles and quantified Infinity at their separate scopes.

Independent review of the upper inclusion.
