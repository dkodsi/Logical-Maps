# Questions, connections and resolved conjectures

Open questions and established answers, grouped by mathematical family. The background is C unless stated otherwise. “Unresolved” refers to the cited evidence, not necessarily to the literature.

[Main results](MAIN-RESULTS.md) · [Catalog](CATALOG.md) · [Evidence](evidence/RESULT-INDEX.md)

Open questions come first. Established answers follow the three parts of Main Results: database connections, further results about established principles, and extensions.

- [Open questions and claims awaiting review](#open-questions)
- [I. Resolved database questions and connections](#database-connections)
- [II. Further results about established principles](#established-principles)
- [III. Extensions and new directions](#extensions-and-new-directions)

<a id="open-questions"></a>
## Open questions and claims awaiting review

[Remaining central questions](#remaining-questions) · [Arithmetic equality awaiting review](#arithmetic-review)

<a id="remaining-questions"></a>
### Remaining central questions

<a id="rc-tc"></a>
#### Does Relational Choice entail Transversal Choice?

**Position:** Unresolved; sharper positive and negative criteria.

Relational Choice plus Boolean Completeness gives Actuality and TC. The history construction reduces Transversal Choice at the evaluation point to finite ambiguity in at least one missed cell. Finite code orbits obstruct symmetry-based countermodels. Class-code iteration preserves ambiguity, and orbit exhaustion is exactly Actuality.

Derive a suitable coherent chooser from RC alone, or construct a genuine full RC countermodel meeting the closure and code-orbit restrictions.

**Lean certified:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness): RC + BC ⇒ TC; the sharp Actuality theorem, Actuality-based TC, and the same-type RC + BC and CBC + CCC consequences. [`COEXTENSION-OPERATIONS`](evidence/RESULT-INDEX.md#coextension-operations): Orbit averaging and finite code towers; orbit/Actuality equivalence at t and inhabited unary types.

<a id="pure-sp"></a>
#### Is pure Strong Possibility consistent?

**Position:** Unresolved; exact criteria and construction obstructions.

Universal-identity and restricted-disjunction criteria are established. In the specified two-axiom test any required full-term embedding must leave every target arithmetic counterexample above its entire source number image.

Construct the genuine endpoint embedding or otherwise settle joint consistency. A noncofinal omitted-cut requirement rules out routes, not the theory.

**Lean certified:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria): The universal-core equivalence and the stated conditional disjunction criterion.

<a id="signature-sp"></a>
#### Is SP consistent for one unary predicate constant and no individual names?

**Position:** Unresolved; first-stage sufficient criterion.

Nonempty K₁ already implies full signature SP consistency and is equivalent to weak named existence for the marked Max theory. Finite Herbrand extraction fails; the singleton-profile root is deleted. A successful fixed-domain kernel must be perfect and nonhyperarithmetic, with exact stabilization ordinal ω₁CK.

Prove weak named existence or give a globally empty witness open. Failure of K₁ or the stronger fixed-domain construction would not alone refute SP.

**Lean certified:** [`SP-SIGNATURE-CONFLICT`](evidence/RESULT-INDEX.md#sp-signature-conflict): The signature-splitting lemma.

<a id="observer-strength"></a>
#### Does injective logical separation imply logical left-inverse separation?

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

<a id="arithmetic-review"></a>
### Arithmetic equality awaiting review

<a id="max-arithmetic-equality"></a>
#### What exactly is the ordinary arithmetic theory of pure Maximalism?

**Position:** Proposed equality; upper inclusion awaits independent review.

The proposed equality is

$$
\mathrm{Th}_{\mathrm{arith}}(\mathrm{Max}(C))=\mathrm{Cn}\bigl(T_{\mathrm{arith}}\cup\mathrm{True}_{\Pi_1}\bigr).
$$

An ordinary proof is supplied for both inclusions, but the difficult upper inclusion still awaits independent review. Here $T_{\mathrm{arith}}$ is the common arithmetic theory of the positive Choice and Plenitude packages. See the [statement and proof](evidence/RESULT-INDEX.md#max-arithmetic-equality).

<a id="database-connections"></a>
## I. Resolved database questions and connections

[Choice and comprehension](#choice-and-comprehension) · [Rigidity](#rigidity) · [Modal stability and noncontingency](#modal-stability) · [Maximalism and Strong Possibility](#maximalism-and-possibility) · [Infinity and forcing](#infinity-arithmetic-forcing)

<a id="choice-and-comprehension"></a>
### Choice and comprehension

<a id="actuality-and-bf-imply-inextensible-comprehension"></a>
#### Does Actuality + BF imply Inextensible Comprehension?

Yes. BF need not be strengthened to ☐BF.

[Proof](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/writeups/actuality-and-bf-imply-inextensible-comprehension.md).

**Lean certified.**

<a id="relational-choice-and-boolean-completeness-imply-transversal-choice"></a>
#### Does Relational Choice + Boolean Completeness imply Transversal Choice?

Yes. The same premises also imply Actuality; Relational Choice alone remains open.

[Proofs and certificates](evidence/RESULT-INDEX.md#choice-completeness).

**Lean certified:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness): RC + BC ⇒ TC; the sharp Actuality theorem, Actuality-based TC, and the same-type RC + BC and CBC + CCC consequences.

<a id="choice-necessity-boundaries"></a>
#### Functional Choice does not give its own necessity

The atom-plus-atomless Boolean-valued model satisfies C5 + Functional Choice + Actuality while refuting ☐Actuality and ☐Functional Choice. The two-object retract satisfies Functional Choice and ☐Actuality but refutes C5 and ☐Functional Choice.

**Evidence:** [choice.24](CATALOG.md#choice.24).

<a id="choice-without-plenitude"></a>
#### Substantial Choice without Plenitude

The generic Boolean Henkin model satisfies C5, ☐Relational Choice and ☐Intensional Choice while remaining atomless and refuting Plenitude and Functional Choice at (t,t). The separate countable-support nominal model has ☐Intensional Choice and propositional Dedekind infinity while failing Relational Choice and Functional Choice.

**Evidence:** [world_algebra.22](CATALOG.md#world_algebra.22) · [model_interpretation.03](CATALOG.md#model_interpretation.03).

<a id="intensional-relational-choice"></a>
#### Intensional Choice, Relational Choice and infinity separate

In the atom-world permutation hierarchy, ☐Intensional Choice holds at every type while operational Dedekind infinity at t necessarily fails. The paired-individual hierarchy also separates all-type Intensional Choice from Relational Choice, with the exact support-cardinal condition retained in the proof.

**Evidence:** [World orbits determine propositional Dedekind infinity](evidence/RESULT-INDEX.md#nominal-orbits) · [world_algebra.26](CATALOG.md#world_algebra.26).

**Lean certified:** [`NOMINAL-ORBITS`](evidence/RESULT-INDEX.md#nominal-orbits).

<a id="restricted-transversals"></a>
#### What does suffice for Transversal Choice?

Relational Choice supplies transversals for internally finite cells, and for the stated finite exceptional covers of infinite cells. ND plus matching Countable Boolean Completeness and Relational Choice suffice for internally countable cells. Admitted class labels plus Relational Choice, or an admitted well-ordered cover without Choice, give further positive cases. As all-type schemas, quotient-respecting Relational Choice is exactly Transversal Choice.

**Evidence:** [rigidity.23](CATALOG.md#rigidity.23) · [rigidity.24](CATALOG.md#rigidity.24) · [rigidity.25](CATALOG.md#rigidity.25) · [rigidity.26](CATALOG.md#rigidity.26).

<a id="completeness-reductions"></a>
#### Completeness and choice

Directed Boolean completeness is equivalent to Boolean Completeness over C. With the matching Relational Choice instance, completeness for well-ordered chains already gives Boolean Completeness. Completeness for subfamilies of an admitted order-dense family also suffices; the countable version retains its stated countability-inheritance hypothesis. Coextension-invariant choice of comparable suprema is equivalent to Transversal, the coextension-representative principle.

**Evidence:** [rigidity.17](CATALOG.md#rigidity.17) · [rigidity.18](CATALOG.md#rigidity.18) · [rigidity.22](CATALOG.md#rigidity.22) · [rigidity.28](CATALOG.md#rigidity.28).

<a id="rigidity"></a>
### Rigidity

<a id="necessary-atomicity-completeness-bf-imply-rigid-comprehension"></a>
#### Does ☐Atomicity + Boolean Completeness + BF imply Rigid Comprehension?

No. The ultralimit-fork model satisfies even ☐Boolean Completeness, ☐BF and ☐Actuality, but fails Rigid Comprehension at type tt.

[Countermodel](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/ultralimit-fork.yaml).

<a id="rigid-rigidity-implies-rigid-power"></a>
#### Does Rigid Rigidity imply Rigid Power?

No. A coalesced sum of two extensional models disagreeing about arithmetic satisfies Rigid Rigidity and refutes Rigid Power.

[Countermodel](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/coalesced-two-extensional-arithmetics-root.yaml).

<a id="tr-rp-wrp"></a>
#### Does Tame Rigidity + Rigid Power entail Weakly Rigid Power?

**Position:** Refuted by a certified full C countermodel.

No. The finite compression model satisfies Tame Rigidity and Rigid Power but fails Weakly Rigid Power at type et. The earlier colour-collapse example fails Rigid Power at the next property type and does not by itself settle this question.

**Lean certified:** [`FINITE-COMPRESSION-SEPARATION`](evidence/RESULT-INDEX.md#finite-compression-separation). [`COLOUR-COLLAPSE-SCOPE`](evidence/RESULT-INDEX.md#colour-collapse-scope). [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications).

<a id="nd-completeness-rigidity"></a>
#### The rigidity equivalence under ND and completeness

Over C + ND + Boolean Completeness, Inextensible Comprehension, Rigid Comprehension, Tame Rigidity and Weakly Rigid Power are equivalent. ND and Boolean Completeness alone do not imply them: the old/new model also refutes ☐Boolean Completeness at type et.

**Evidence:** [Four rigidity principles coincide over ND and Boolean Completeness](evidence/RESULT-INDEX.md#rigidity-nd-bc) · [ND and Boolean Completeness do not give Rigid Comprehension](evidence/RESULT-INDEX.md#oldnew-separation).

**Lean certified:** [`RIGIDITY-ND-BC`](evidence/RESULT-INDEX.md#rigidity-nd-bc). [`OLDNEW-SEPARATION`](evidence/RESULT-INDEX.md#oldnew-separation).

<a id="weak-power-positive"></a>
#### Positive routes to Weakly Rigid Power

Atomicity + Rigid Comprehension entails Weakly Rigid Power. ND (type t) + Inextensible Comprehension also suffices; more sharply, Inextensible Comprehension at τt gives Weakly Rigid Power at τ. These assumptions are unboxed.

**Evidence:** [Rigidity has exact power, uniformization and algebraic descriptions](evidence/RESULT-INDEX.md#rigidity-classifications) · [rigidity.09](CATALOG.md#rigidity.09).

**Lean certified:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications).

<a id="rigidity-closures"></a>
#### Boolean closure characterizes ND and C5

At argument type σ, ND is equivalent to intersection, difference or symmetric-difference closure of rigid properties, and to their pointwise endpoint-valued membership; the same holds for weakly rigid properties. Complement closure is stronger: for weakly rigid σt properties it is exactly ND at σ + BF at σ, and for rigid properties exactly ND at σ + ☐BF at σ. Either all-type complement-closure schema characterizes C5; the tt test already suffices.

**Evidence:** [rigidity.06](CATALOG.md#rigidity.06) · [rigidity.07](CATALOG.md#rigidity.07).

**Lean certified:** [rigidity.06](CATALOG.md#rigidity.06): The intersection, difference, symmetric-difference and membership-bivalence characterizations at weak and rigid levels.

**Lean certified:** [rigidity.07](CATALOG.md#rigidity.07): Exact weak ND+BF versus rigid ND+boxed-BF complement characterizations, tt/C5 equivalence, and all-type C5 consequences with tuple laws.

<a id="rigidity-type-descent"></a>
#### Rigidity principles descend one property type

For relational τ, each of Tame Rigidity, Rigid Power, Weakly Rigid Power, Rigid Comprehension, Weak Rigid Comprehension and Inextensible Comprehension descends from τt to τ. Their nullary instances are C-theorems. Tame Rigidity is equivalently closure of rigid relations under existing represented joins.

**Evidence:** [rigidity.01](CATALOG.md#rigidity.01) · [rigidity.03](CATALOG.md#rigidity.03) · [rigidity.05](CATALOG.md#rigidity.05).

**Lean certified:** [rigidity.01](CATALOG.md#rigidity.01): Nullary proof bodies establish WeakRigid(p) iff top/bottom iff Rigid(p), with the stated nullary TR/RP/WRP/Rigid Rigidity/Weakly Rigid Weak Rigidity/RC/WeakRC theorems and indicated necessary versions. No internally finite-power theorem is inferred.

**Lean certified:** [rigidity.05](CATALOG.md#rigidity.05): Existing represented joins preserve weak rigidity; Tame Rigidity iff rigid-join closure, without optional completeness or a rigid indexing family.

<a id="fixed-point-boundary"></a>
#### Comprehension and choice do not force ☐Tame Rigidity

One fixed-point entrance model satisfies Atomicity, Boolean Completeness, Rigid Comprehension, Relational Choice, Tame Rigidity, Rigid Power and Weakly Rigid Power, together with ☐Strong Actuality and BF at e. It refutes ☐Tame Rigidity at (tt)t, BF at every relational argument type, ND at t and Strong Leibniz Biconditionals at every relational type.

**Evidence:** [Comprehension, completeness and choice do not force ☐Tame Rigidity](evidence/RESULT-INDEX.md#fixed-point-entrance).

**Lean certified:** [`FIXED-POINT-ENTRANCE`](evidence/RESULT-INDEX.md#fixed-point-entrance).

<a id="modal-stability"></a>
### Modal stability and noncontingency

<a id="c5-and-atomicity-imply-no-pure-contingency"></a>
#### Does C5 + Atomicity imply No Pure Contingency?

Yes. Atomicity at type t already suffices. The atom-swapping argument extends through every relational type and fixes all closed pure terms.

[Proof and certificate](evidence/RESULT-INDEX.md#npc-atomicity).

**Lean certified:** [`NPC-ATOMICITY`](evidence/RESULT-INDEX.md#npc-atomicity).

<a id="necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-relational"></a>
#### Does ☐Strong Leibniz Biconditionals + Rigid Comprehension imply ☐BF at relational types?

Yes, and Strong Leibniz Biconditionals need not be boxed. The unboxed premises also imply ☐Strong Leibniz Biconditionals, ☐Rigid Comprehension and ☐Boolean Completeness. BF at type e is not claimed.

[Proofs and certificates](evidence/RESULT-INDEX.md#modal-propagation).

**Lean certified:** [`MODAL-PROPAGATION`](evidence/RESULT-INDEX.md#modal-propagation).

<a id="vicinity-implies-five-implies-two-hat"></a>
#### Does Vicinity make 5-necessity imply two-hat necessity?

Yes. Sun’s argument derives the implication from a strongest 5-necessary proposition, without assuming BF or Actuality.

[Proof](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/writeups/vicinity-implies-five-implies-two-hat.md).

<a id="logical-necessity-boundaries"></a>
#### Logical Necessity does not force Actuality or Vicinity

For the one-predicate signature, Logical Necessity + ☐BF + ☐Relational Choice has a countermodel to both Actuality and Vicinity. A separate symmetric-surjection/free-word construction has Logical Necessity with ☐Boolean Completeness, ☐BF, ☐Tame Rigidity and ☐Weakly Rigid Power, but is atomless and fails Actuality, Vicinity and Relational Choice.

**Evidence:** [Logical Necessity and strong selection laws do not force Actuality](evidence/RESULT-INDEX.md#logical-necessity-separation) · [F08](CATALOG.md#f08).

**Lean certified:** [`LOGICAL-NECESSITY-SEPARATION`](evidence/RESULT-INDEX.md#logical-necessity-separation).

<a id="propagation-type-boundary"></a>
#### Propositional Strong Leibniz does not give the all-type propagation theorem

The stitched middle-world model has ☐Strong Leibniz Biconditionals at t, Rigid Comprehension, ☐BF at e and t, and ☐Relational Choice and ☐Actuality. Nevertheless ☐Rigid Comprehension and ☐Boolean Completeness fail at et. The all-relational Strong Leibniz premise in the positive theorem cannot simply be replaced by its propositional instance.

**Evidence:** [F06](CATALOG.md#f06).

<a id="maximalism-and-possibility"></a>
### Maximalism and Strong Possibility

<a id="maximalist-distinctness-incompatible-with-rigid-comprehension"></a>
#### Can pure Maximalism coexist with Rigid Comprehension?

No. Rigid Comprehension entails Countable Boolean Completeness and hence the Necessity of Arithmetic, which is incompatible with pure Maximalism.

[Proof](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/results/maximalist-distinctness-incompatible-with-rigid-comprehension.yaml).

<a id="max-atomicity"></a>
#### Can pure Maximalism coexist with Atomicity (type t)?

**Position:** Refuted and certified.

The inconsistency theorem has no additional non-theoremhood or model-existence premise.

**Lean certified:** [`MAX-ATOMICITY`](evidence/RESULT-INDEX.md#max-atomicity).

<a id="signature-sp-pure"></a>
#### Does signature Strong Possibility entail pure Strong Possibility?

**Position:** Exact consistency reduction established; consistency remains unresolved.

For every map-admitted signature Σ, SP(Σ) entails SP(pure) exactly when SP(Σ) is inconsistent. More strongly, SP(pure) is incompatible with Max(Σ). The reverse entailment holds exactly when SP(pure) is inconsistent. The signature must contain a relational constant, and each Max schema retains its own reference language. See the [proof](evidence/RESULT-INDEX.md#sp-signature-conflict).

This settles the relation between the two questions without deciding either consistency question.

**Lean certified:** [`SP-SIGNATURE-CONFLICT`](evidence/RESULT-INDEX.md#sp-signature-conflict): The signature-splitting lemma.

<a id="sp-bf-functionality"></a>
#### Finite-signature SP refutes BF and Functionality

For every finite signature $\Sigma$, including the empty signature,

$$
\mathrm{SP}(\Sigma)\vdash\neg\mathrm{BF}_{\alpha}\;\land\;\neg\mathrm{Functionality}_{\alpha,\beta}
\qquad(\beta\ne e).
$$

This holds at every admitted input type α and relational output type β, with explicit counterpredicates and counterfunctions. With infinitely many relational constants but finitely many individual names, the type-e BF failure and input-e Functionality failures still follow. The all-input result retains the finite-signature restriction. These are consequences of SP, not a proof of its consistency.

**Evidence:** [Finite-signature SP refutes BF and Functionality at every input type](evidence/RESULT-INDEX.md#sp-barcan-functionality).

<a id="sp-named-domain"></a>
#### SP determines the finite individual domain

With exactly u finitely many individual names, SP(Σ) forces exactly max(1,u) individuals; when u is positive the names enumerate them bijectively. Pure SP therefore forces one actual individual, refuting the individual Infinity schema and quantified Axiom of Infinity, despite its possible larger domains.

**Evidence:** [SP fixes the actual domain from the number of individual names](evidence/RESULT-INDEX.md#sp-individual-cardinality).

**Lean certified:** [`SP-INDIVIDUAL-CARDINALITY`](evidence/RESULT-INDEX.md#sp-individual-cardinality): The conditional monism/reflection lemma.

<a id="sp-strong-worlds"></a>
#### Pure SP excludes strong worlds

Pure SP rules out arbitrary actual strong-world entities at every relational type. It also permits distinctness-preserving atomless splitting of each fixed finite current Boolean diagram. This does not refute Actuality or weak atoms. At relational input and output types, the BF/Functionality failures can be strengthened to closed pure persistent counteroperations and arbitrarily large finite families of distinct entity-coextensive operations.

**Evidence:** [sp_supplement.07](CATALOG.md#sp_supplement.07) · [sp_supplement.08](CATALOG.md#sp_supplement.08).

<a id="independence-boundary"></a>
#### Signature Independence is compatible with Extensionality and strong Choice

For Σ = {c:et}, the full one-world countermodels satisfy Independence together with Extensionality and the stated Atomicity and Choice packages. They refute the proposed Infinity implications at the precise individual and propositional scopes listed in the proof.

**Evidence:** [Independence coexists with extensionality and strong Choice](evidence/RESULT-INDEX.md#signature-independence).

**Lean certified:** [`SIGNATURE-INDEPENDENCE`](evidence/RESULT-INDEX.md#signature-independence).

<a id="infinity-arithmetic-forcing"></a>
### Infinity and forcing

<a id="possible-infinity-implies-axiom-of-infinity"></a>
<a id="possible-infinity-e-implies-axiom-of-infinity-e"></a>
<a id="possible-infinity-t-implies-axiom-of-infinity-t"></a>
#### Does Possible Infinity imply the corresponding Axiom of Infinity?

No, at either e or t. A singleton-individual coalesced root refutes the type-e implication; the two-object chain with a free loop refutes the type-t implication.

[Type-e countermodel](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/coalesced-single-individual-root.yaml) · [Type-t countermodel](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/full-two-object-chain-free-loop.yaml) · [Further Infinity separations](evidence/RESULT-INDEX.md#infinity-schema-separation).

<a id="abstract-forcing"></a>
#### Do ☐Rigid Comprehension, Intensional Choice and Forcing Possibilism force CH contingency?

**Position:** Strict-smallness database formulation refuted by existing models; source correspondence unresolved.

No for the database’s strict-smallness formulation. Under metatheoretic Choice, countable-arrow full-action models satisfy all three premises together with Non-contingency of CH: the strict size bound requests only finite complete Boolean algebras in those models. This refutes the encoded conjecture; the source’s intended size convention and type language require separate comparison. See the [formulation audit](proofs/forcing-formulation.md).

Strict-smallness Forcing Possibilism is also independent over C + ☐Functional Choice + Axiom of Infinity (types e and t). The [full modalized cloud](evidence/RESULT-INDEX.md#forcing-transfer) has its own model-specific forcing-transfer argument.

The stronger non-strict formulation and its required forcing-algebra availability remain unresolved. Equivalence of the two lottery presentations remains under review.

<a id="quantified-infinity-bases"></a>
#### Quantified Infinity reduces to the base types

Over C, Axiom of Infinity at t implies it at every relational type; Axiom of Infinity at e and t implies it at every admitted type. Under the matching Functionality instances, a relational type containing no e is internally finite exactly when t is; a type containing e is finite exactly when both e and t are.

**Evidence:** [Finiteness is classified by the base types occurring in a type](evidence/RESULT-INDEX.md#finite-type-propagation).

**Lean certified:** [`FINITE-TYPE-PROPAGATION`](evidence/RESULT-INDEX.md#finite-type-propagation): Finiteness propagation, descent, and the exact classification by type. The four C5 base-infinity combinations and the stated two-stage model/finiteness/Functionality endpoints.

<a id="infinity-schema-boundaries"></a>
#### Infinity schemata do not imply the quantified axioms

Even C + ☐Functional Choice has a model of both finite lower-bound Infinity schemata that necessarily refutes both quantified Axioms of Infinity. Another model has ☐Functional Choice, ☐Forcing Possibilism, ☐Axiom of Infinity at t and the individual Infinity schema while necessarily refuting Axiom of Infinity at e.

**Evidence:** [Infinity schemata do not imply their quantified axioms, even with necessary Choice](evidence/RESULT-INDEX.md#infinity-schema-separation).

<a id="ch-structural-boundary"></a>
#### Strong boxed structural principles do not settle CH noncontingency

Assuming Con(ZFC), the coalesced CH model makes CH and its negation possible at the same type e while satisfying ☐Atomicity, ☐BF, ☐Strong Leibniz Biconditionals, ☐Rigid Rigidity, ☐Weakly Rigid Weak Rigidity, ☐Tame Rigidity and Modal Well-Ordering. In the full modalized cloud, the separate transfer argument realizes both CH alternatives at et.

**Evidence:** [CH can vary despite boxed structural principles](evidence/RESULT-INDEX.md#ch-coalesced) · [The full modalized cloud realizes both sides of CH](evidence/RESULT-INDEX.md#forcing-transfer).

**Lean certified:** [`CH-COALESCED`](evidence/RESULT-INDEX.md#ch-coalesced): Opposite-CH components at type e and their coalesced C countermodel with ☐BF, constructed in Lean’s ambient metatheory.

<a id="max-ch-answer"></a>
#### Maximalism refutes Non-contingency of CH

Assuming Con(ZFC), pure Maximalism + Non-contingency of CH is inconsistent. The argument uses the separate consistency of real structures satisfying CH and its negation.

**Evidence:** [Maximalism is incompatible with Non-contingency of CH](evidence/RESULT-INDEX.md#max-ch).

**Lean certified:** [`MAX-CH`](evidence/RESULT-INDEX.md#max-ch): Maximalism + Non-contingency of CH ⇒ ⊥, using constructed type-e components in Lean’s ambient metatheory.

<a id="forcing-choice-infinity"></a>
#### Forcing Possibilism is independent of necessary Choice and Infinity

Strict-smallness Forcing Possibilism is independent over C + ☐Functional Choice + Axiom of Infinity (types e and t). A free-root model also satisfies Forcing Possibilism and both quantified Infinity axioms while failing Intensional Choice. In full S5 on an infinite world set W, the exact criterion is $2^{|W|}=2^{\aleph_0}$, in external ZFC.

**Evidence:** [Strict-smallness Forcing Possibilism is independent of necessary Choice and Infinity](evidence/RESULT-INDEX.md#forcing-possibilism).

<a id="resolved-model-questions"></a>
### Resolved model-construction questions

The database also settles existence questions for these nineteen constructions. The summaries describe the base models; signature, individual-domain and metatheoretic variants are grouped with their construction, whose linked record gives the exact scope.

<a id="coalesced-models"></a>
#### Coalesced roots

- **Maximalist root.** Signature Maximalism coexists with Relational Choice and Actuality while BF (type t), Atomicity (type t) and Boolean Completeness (type t) fail. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/coalesced-maximalist-root.yaml).
- **Singleton-individual root.** Possibility⁺, Relational Choice and Actuality coexist with a singleton individual domain. The pure construction is established; its signature expansion requires at most one individual constant. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/coalesced-single-individual-root.yaml).

<a id="finite-support-models"></a>
#### Finite-support action models

- **Dyadic roundings.** Actuality and Atomicity coexist with failures of BF and Boolean Completeness. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-dyadic-roundings.yaml).
- **Identity-or-collapse surjections.** Actuality and BF coexist with failures of Atomicity and Boolean Completeness. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-identity-or-collapse-surjections.yaml).
- **Identity-or-collapse maps.** Actuality, Tame Rigidity and Rigid Power coexist with failures of Atomicity, BF and Boolean Completeness. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-identity-or-collapse.yaml).
- **Monotone maps.** Atomlessness, Tame Rigidity and Rigid Power coexist with failures of BF and Weak Inextensible Comprehension. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-monotone-maps.yaml).
- **Monotone surjections.** Atomlessness and BF coexist with failures of ND and Weak Inextensible Comprehension. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-monotone-surjections.yaml).
- **Permutations.** ND coexists with Atomlessness and failure of Weak Inextensible Comprehension. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-permutations.yaml).
- **Truncated shifts.** Actuality, Atomicity and BF coexist with failure of Boolean Completeness. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-truncated-shifts.yaml).
- **Truncations.** Atomicity, Tame Rigidity and Rigid Power coexist with failures of Actuality and Boolean Completeness. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-truncations.yaml).
- **Two-object all-maps construction.** BF and ☐Relational Choice coexist with failures of ☐BF, Inextensible Comprehension and Countable Boolean Completeness. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/finite-support-two-object-all-maps.yaml).

<a id="full-action-models"></a>
#### Full action models

- **Free monoid with glued constants.** Logical Necessity and Forcing Possibilism coexist with ☐Rigid Comprehension and ☐Atomicity while ND (type t) fails. The signature expansion is established. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/full-free-monoid-glued-constants.yaml).
- **Idempotent monoid.** ☐Atomicity and ☐Rigid Comprehension coexist with failure of Strong Leibniz Biconditionals (type t). [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/full-idempotent-monoid.yaml).
- **Involution group.** C5, ☐Atomicity, ☐BF and ☐Rigid Comprehension coexist with failure of the Fregean Axiom. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/full-involution-group.yaml).
- **Surjection monoid.** ☐Atomicity, ☐BF and ☐Rigid Comprehension coexist with failures of ND (type t) and Forcing Possibilism. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/full-surjection-monoid.yaml).
- **Two-object chain.** ☐Atomicity, ☐BF and ☐Rigid Comprehension coexist with failure of pure B, and hence of No Pure Contingency. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/full-two-object-chain.yaml).
- **Two-object retract.** ND, ☐Strong Actuality and ☐Rigid Comprehension coexist with failure of Strong Leibniz Biconditionals (type t). [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/full-two-object-retract.yaml).

<a id="henkin-symmetric-models"></a>
#### Henkin and symmetric models

- **Henkin model without a choice function.** Extensionality and Axiom of Infinity (type e) coexist with failure of Relational Choice. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/henkin-without-relational-choice.yaml).
- **Symmetric qualitative-contrast model.** C5, Actuality and Plenitude coexist with failures of Relational Choice and Atomicity. Thus Plenitude does not imply Functional Choice even under C5, Rigid Comprehension and Boolean Completeness. [Construction and variants](https://github.com/dkodsi/Logical-Maps/blob/12297812d21ed02a7d87cd4c642ba9adb8b4f7ff/logical-maps/topics/classicism/models/symmetric-qualitative-contrast.yaml).

<a id="previously-known-results-formalized"></a>
### Previously known results formalized

[Original attribution and certified scope](MAIN-RESULTS.md#previously-known-results-formalized).

- [C5 + Atomicity (type t) ⇒ No Pure Contingency](evidence/RESULT-INDEX.md#npc-atomicity)
- [C5 + ☐Rigid Comprehension ⇒ Second-Order Analytic Necessitism](evidence/RESULT-INDEX.md#analytic-rigidification)
- [Symmetric ideally-full model: old and new individuals](evidence/RESULT-INDEX.md#oldnew-separation)

<a id="further-questions"></a>
<a id="established-principles"></a>
## II. Further results about established principles

[Choice and completeness](#choice-and-completeness) · [Arithmetic and analysis](#arithmetic-and-analysis) · [Language, computation and construction limits](#further-negative-results)

<a id="choice-and-completeness"></a>
### Choice and completeness

<a id="fc-finite-basis"></a>
#### Can Functional Choice or ☐Functional Choice have a finite equivalent fixed-type basis?

**Position:** Negative ordinary results established.

Neither full Functional Choice nor its boxed form has an equivalent finite list of arbitrary pure fixed-type sentences over C. The Boolean-valued construction supplies ordinary separating models. The previously stated fixed-input and selector hierarchies remain in the supporting proofs.

**Lean certified:** [`CHOICE-NO-FINITE-BASIS`](evidence/RESULT-INDEX.md#choice-no-finite-basis).

<a id="inverse-characterizations"></a>
#### Choice, Plenitude and C5 through inverses

Functional Choice is Actuality plus pointwise sections of actual surjections; Plenitude is Actuality plus pointwise retractions of actual injections. Their stronger inverse formulations distinguish ☐Functional Choice and C5. Over C + ☐Plenitude, complete Boolean retractions characterize ☐Functional Choice.

**Evidence:** [Choice and Plenitude decompose into Actuality and inverse maps](evidence/RESULT-INDEX.md#sections-retractions) · [C5 is exactly strong retractions of actual injections](evidence/RESULT-INDEX.md#c5-strong-retractions) · [Complete Boolean retractions characterize ☐Functional Choice](evidence/RESULT-INDEX.md#boolean-retractions-choice).

**Lean certified:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions). [`C5-STRONG-RETRACTIONS`](evidence/RESULT-INDEX.md#c5-strong-retractions): The C5 forward rules for persistent injectivity and strong retractions at all admitted relational types, the low-type converses to ☐ND (type t), and the per-map necessary-injectivity/strong-retraction equivalence.

<a id="countable-completeness-boundary"></a>
#### Countable completeness at a countable Boolean type forces finiteness

Over C, an internally countable relational Boolean type is countably complete exactly when it is internally Frege-finite. Matching Countable Boolean Completeness therefore gives Actuality in this setting. Separately, the finite-fan model has arithmetic noncollapse at e but no Possible Infinity at e, even with the stated boxed comprehension, completeness and choice principles.

**Evidence:** [Countable completeness forces Frege finiteness at countable Boolean types](evidence/RESULT-INDEX.md#countable-boolean-finiteness) · [principles.34](CATALOG.md#principles.34).

<a id="arithmetic-and-analysis"></a>
### Arithmetic and analysis

<a id="full-choice-arithmetic"></a>
#### Does ☐Functional Choice add ordinary arithmetic over ☐Plenitude?

**Position:** Arithmetic conservation established.

Over C with quantified Infinity at e and t, replacing ☐Plenitude by ☐Functional Choice adds no ordinary first-order arithmetic theorems. Both have the arithmetic consequences of C plus numerical noncollapse at e, and this remains true after adding ☐Axiom of Infinity at every admitted type.

The proof uses McLarty’s number-preserving interpretation.

<a id="analytic-rigidification-answer"></a>
#### Rigid Comprehension stabilizes possible real structures

C5 + ☐Rigid Comprehension gives a rigid representative of any possible real structure at a fixed type, necessarily satisfying the real-number axioms. The represented-power construction works simultaneously at each prescribed finite list of arities.

**Evidence:** [Rigid Comprehension stabilizes a possible real structure](evidence/RESULT-INDEX.md#analytic-rigidification).

**Lean certified:** [`ANALYTIC-RIGIDIFICATION`](evidence/RESULT-INDEX.md#analytic-rigidification): Rigidification and simultaneous represented powers of every prescribed finite list of positive arities, at every closed admitted type and in arbitrary signatures.

<a id="max-arithmetic-obstructions"></a>
#### Maximalism and SP have different arithmetic obstructions

Pure Maximalism forbids a predecessor operation at every admitted counting type, although the relevant total single-valued graph exists. Pure SP proves every standard-true Π₂ sentence under the specified Frege translation; if consistent, it omits some true Π₃ sentence. Max also refutes the explicit guarded numerical join, and its interval below ¬Actuality is internally Dedekind and Frege infinite, without asserting that ¬Actuality is currently true.

**Evidence:** [Maximalism forbids a numerical predecessor operation](evidence/RESULT-INDEX.md#max-predecessor) · [Pure SP proves true Π₂ arithmetic, with a sharp conditional boundary](evidence/RESULT-INDEX.md#sp-arithmetic-reflection) · [Frege number structure and transfer can be separated from stronger model claims](evidence/RESULT-INDEX.md#arithmetic-foundations) · [principles.07](CATALOG.md#principles.07) · [principles.09](CATALOG.md#principles.09).

**Lean certified:** [`MAX-PREDECESSOR`](evidence/RESULT-INDEX.md#max-predecessor): The no-predecessor theorem at every closed counting type; the total unique graph and Plenitude failure at e. [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations): The displayed Frege noncollapse and finiteness equivalences, number-map/Hume-class results, and C5–Actuality transfer results.

<a id="further-negative-results"></a>
### Language, computation and construction limits

<a id="signature-extension-answers"></a>
#### Signature extensions and finite profile bounds

There is an exact boundary for conservative proper extensions of finite signatures, and an infinite reserve of names restores conservativity at the types receiving new constants. Pointed complete theories determine the finite Boolean intervals forced by SP. These metatheorems retain the reference language of each Max and SP schema.

**Evidence:** [An exact boundary for finite signature extensions](evidence/RESULT-INDEX.md#signature-finite-boundary) · [An infinite reserve of names restores conservativity](evidence/RESULT-INDEX.md#signature-infinite-reservoir) · [Pointed theories determine the finite Boolean intervals forced by SP](evidence/RESULT-INDEX.md#sp-finite-profile-rank).

<a id="computational-boundaries"></a>
#### Computational strength and model construction

Theoremhood, finite-condition consistency and adequate model construction have distinct jump thresholds. A supplied complete consistent pure theory has a model of exactly its computational degree; requiring externally standard natural numbers creates a stronger barrier. The completion-space comparisons separate finite descriptions and effective complexity.

**Evidence:** [Theoremhood and model construction have successive jump thresholds](evidence/RESULT-INDEX.md#computability-comparison) · [A complete theory has a model of exactly its computational degree](evidence/RESULT-INDEX.md#exact-model-degrees) · [Standard natural numbers impose a much stronger computational barrier](evidence/RESULT-INDEX.md#standard-number-models) · [Finite descriptions distinguish the completion spaces](evidence/RESULT-INDEX.md#completion-spaces).

<a id="failed-choice-constructions"></a>
#### Construction failures that leave the main questions open

The rational-shear and full rational-linear selector constructions fail after the required closure steps. The paired-individual example satisfies restricted Relational Choice fragments, not full Relational Choice, so it cannot settle Relational Choice ⇒ Transversal Choice. The one-block Cohen reservoir fails the required real-uniformization property; the separate ADℝ-relative separator retains its metatheoretic assumption.

**Evidence:** [rigidity.29](CATALOG.md#rigidity.29) · [rigidity.30](CATALOG.md#rigidity.30) · [F04](CATALOG.md#f04) · [F10](CATALOG.md#f10).

<a id="extensions-and-new-directions"></a>
## III. Extensions and new directions

[Abstraction and full standard models](#language-and-models) · [New characterizations and separation questions](#new-characterizations)

<a id="language-and-models"></a>
### Abstraction and full standard models

<a id="lambda-equivalence"></a>
#### Can fixed C be reconstructed without primitive lambda?

**Position:** Exact open-sequent equivalence established and certified.

An explicit classical lambda-free applicative calculus has exactly C’s consequences in its original language, including open contexts and finite lists of assumptions. A conservative named extension reconstructs arbitrary C terms and full contextual beta eta delta conversion.

**Lean certified:** [`LAMBDA-FREE-TRANSLATION`](evidence/RESULT-INDEX.md#lambda-free-translation). [`BETA-ETA-CONVERSION`](evidence/RESULT-INDEX.md#beta-eta-conversion).

<a id="full-gallin"></a>
#### Can endpoint separation and comprehension reconstruct full standard models?

**Position:** Resolved: a λ-free characterization in ZF.

Full typed endpoint separation plus boxed Infinitary Comprehension characterizes full standard relational hierarchies over the specified λ-free base of H. Finite instances reconstruct abstraction, while the translated observer equality clauses follow from the resulting C5 theory. The representation is provable in ZF. [Proof and exact formulation](proofs/lambda-free-endpoint-comprehension.md).

<a id="infinitary-sp"></a>
#### Does countable named exhaustion follow from SP with infinitary resources?

**Position:** Proved for a specified semantic reference; conditional otherwise.

A single admitted non-name predicate gives reflection. The profile construction supplies Max(Td)-eligibility, so SP(Td) entails countable actual exhaustion. A numeral abstraction conflicts with Max referenced to original finitary C.

For a proposed syntactic C∞, supply the closed-identity separation bridge. Consistency of SP(Td) is not proved.

**Lean certified:** [`SP-INDIVIDUAL-CARDINALITY`](evidence/RESULT-INDEX.md#sp-individual-cardinality): The conditional monism/reflection lemma.

<a id="new-characterizations"></a>
### New characterizations and separation questions

<a id="pr-choice"></a>
#### Does strong profile richness force full Functional Choice?

**Position:** Negative ordinary constructions supplied.

Supported nominal models realize exact individual profiles and arbitrarily high finite supported ranks while failing FC. Raw profile representation and rigid-profile PR have different boundaries.

**Lean certified:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra): The finite-profile and atomic-profile results.

<a id="evaluation-characterizations"></a>
#### Evaluation and coextension representatives

The evaluator hierarchy distinguishes truth-fibre classification, correct evaluation, necessary evaluation and complete evaluation. Uniform complete-evaluator selection measures well-orderability of atom fields and, at all types, ☐Functional Choice. Coextension-invariant operations characterize Actuality at their stated type scopes.

**Evidence:** [Actual-truth evaluators and current extensional cores](evidence/RESULT-INDEX.md#evaluators-cores) · [Uniform evaluator selection measures well-orderability and Choice](evidence/RESULT-INDEX.md#uniform-complete-evaluators) · [Canonical operations on coextension classes require Actuality](evidence/RESULT-INDEX.md#coextension-operations).

**Lean certified:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores): Actuality-core conversion and admitted-value lemmas. [`COEXTENSION-OPERATIONS`](evidence/RESULT-INDEX.md#coextension-operations): Orbit averaging and finite code towers; orbit/Actuality equivalence at t and inhabited unary types.

<a id="observer-characterizations"></a>
#### Logical separation and its stronger forms

Over H, logical separation gives C + BF, endpoint separation is C5 + Atomicity at t, and factive or unique-observer separation is Extensionality. The inverse and native-modality restrictions yield further strict hierarchies. The comparison between injective and logical left-inverse separation remains open; the exact reductions and countermodel boundaries are in the observer atlas. With OS assumed over H, existence of a correct actual-truth evaluator is exactly what upgrades separation to endpoint separation. Over C, endpoint separation is equivalent to every possible world having its own unique correct evaluator, while a single evaluator that remains correct at every world is equivalent to Extensionality. See the [evaluation bridge](proofs/logical-observers.md#actual-truth-evaluation-and-endpoint-separation).

**Evidence:** [Logical observer separation: a strict hierarchy from BF to Extensionality](evidence/RESULT-INDEX.md#logical-observers) · [Full identity observers have atomic and symmetry representations](evidence/RESULT-INDEX.md#full-identity-observers) · [Stable atoms are exactly what diagonal separation requires](evidence/RESULT-INDEX.md#diagonal-characters) · [Observer separation over H: primitive packages, representation and higher types](evidence/RESULT-INDEX.md#h-observer-space).

**Lean certified:** [`LOGICAL-OBSERVERS`](evidence/RESULT-INDEX.md#logical-observers): H + OS ⇒ C + BF with explicit endpoint identities. Their omission is justified by the linked ordinary reduction proof. [`FULL-IDENTITY-OBSERVERS`](evidence/RESULT-INDEX.md#full-identity-observers): Simultaneous propositional separation for every finite list of closed quantifier types under C5 + Atomicity (type t), including its necessary schema; the converses and equivalence of the two schemas under C5 + Actuality. [`DIAGONAL-CHARACTERS`](evidence/RESULT-INDEX.md#diagonal-characters). [`H-OBSERVER-SPACE`](evidence/RESULT-INDEX.md#h-observer-space): The foundational implication H + OS ⇒ C + BF, with explicit endpoint identities.

<a id="worlds-probability"></a>
#### World representations and probability

Profile realization, complete Boolean maps and admitted world maps have exact representation theorems. Faithful probability is characterized by the stated finite-fibre numerical labelling condition, with a further countability conclusion under finite-field Choice and a finiteness obstruction at higher types.

**Evidence:** [Profile Realization and the Boolean structure of worlds](evidence/RESULT-INDEX.md#profile-world-algebra) · [Faithful probability has an exact finite-fibre condition and type ceiling](evidence/RESULT-INDEX.md#probability).

**Lean certified:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra): The finite-profile and atomic-profile results. [`PROBABILITY`](evidence/RESULT-INDEX.md#probability): Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.
