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
## Does injective logical separation imply logical left-inverse separation?

**Position:** Unresolved over H and over C5.

Separation by logical observers with logical left inverses (SplitMono) entails separation by injective logical observers (InjSep). The converse asks whether a separating family can be replaced by one whose members have logical left inverses; it does not require each original observer to have such an inverse. Over C5, the exact decompositions are

$$
\begin{aligned}
\mathrm{InjSep}&\longleftrightarrow\mathrm{Rev}\lor(\mathrm{OS}\land J_t),\\
\mathrm{SplitMono}&\longleftrightarrow\mathrm{Rev}\lor(\mathrm{OS}\land K_t).
\end{aligned}
$$

Here $J_t$ says that some injective logical observer $E$ and currently true $c$ satisfy $\forall p(Ep\le c\to p=\bot)$. The condition $K_t$ says that logical observers $E,F$ and currently true $c$ satisfy $F\circ E=I$ and $Fc=\bot$. Both use the same qualification at type t; C5 reduces the full schemas to these finite instances. See the [injective](proofs/h-observer-space/injective-separation-decomposition.md) and [left-inverse](proofs/h-observer-space/left-inverse-separation-decomposition.md) decompositions.

The regular-open countermodel refutes $J_t\Rightarrow K_t$, but fails OS, so it does not settle the separation question. Finite relative generation gives a positive case. With $\mathrm{BC}_t+\mathrm{Zorn}_t$, the stated support-coverage equation supplies the required logical inverse; a currently true admitted homogeneous interval is another sufficient condition. The [theorem map](proofs/h-observer-space/MAP.md#10-explicit-frontier) records their exact premises.

The established hierarchy includes H + OS ⇒ C + BF and endpoint separation ⇔ C5 + Atomicity (type t). Reversible separation has an exact invariant-proposition characterization; the [group-law and finite-family theorems](proofs/h-observer-space/GRAPH.md#any-nontrivial-group-equation) give further exact regions without resolving this comparison.

The main C5 question is exactly whether

$$
\mathrm{C5}+\mathrm{OS}+J_t\ \vdash\ \mathrm{Rev}\lor K_t.
$$

Over H the corresponding question is InjSep ⇒ SplitMono. A countermodel must satisfy the full injective separation schema, rather than merely contain an injective observer lacking a logical left inverse.

Other unresolved comparisons are collected in the [research frontier](proofs/h-observer-space/MAP.md#10-explicit-frontier): the joint effect of $\mathrm{BC}_t$ and $\mathrm{Zorn}_t$ with OS; the remaining infinite connective and affine admission questions; the general atomless meet classification; the endpoint-parameter noncontingency converse for Rev; further inverse/necessity comparisons; and removing Actuality from the C-based FinBox theorem for empty or individual-only qualification lists.

**Lean certified:** [`LOGICAL-OBSERVERS`](evidence/RESULT-INDEX.md#logical-observers): H + OS ⇒ C + BF with explicit endpoint identities. Their omission is justified by the linked ordinary reduction proof. [`FULL-IDENTITY-OBSERVERS`](evidence/RESULT-INDEX.md#full-identity-observers): Simultaneous propositional separation for every finite list of closed quantifier types under C5 + Atomicity (type t), including its necessary schema; the converses and equivalence of the two schemas under C5 + Actuality. [`DIAGONAL-CHARACTERS`](evidence/RESULT-INDEX.md#diagonal-characters).

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
\mathrm{Th}_{\mathrm{arith}}(\mathrm{Max}(C))=\mathrm{Cn}\bigl(T_{\mathrm{arith}}\cup\mathrm{True}_{\Pi_1}\bigr).
$$

It also states the specified extensions by current graph-choice principles and quantified Infinity at their separate scopes.

Independent review of the upper inclusion.
