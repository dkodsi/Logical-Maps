# Main results — 24 October 2026 (v2)

Draft. The background is finitary relational **Classicism C** unless stated otherwise.

[Full statements, proofs and certificates](evidence/RESULT-INDEX.md) · [Previously known results formalized](#previously-known-results-formalized) · [Questions and negative results](CONJECTURES.md) · [Notation](#notation)

<a id="central-results"></a>
## Headline results

- [Max + Atomicity (type t) ⇒ ⊥](#max-atomicity). **Lean certified.**
- [Relational Choice + Boolean Completeness ⇒ Actuality and Transversal Choice](#choice-completeness). **Lean certified.**
- [SP(Σ) entails SP(pure) exactly when SP(Σ) is inconsistent](#sp-signature-conflict). **Lean certified signature-splitting lemma.**
- [☐Functional Choice and ☐Plenitude have the same ordinary arithmetic](#arithmetic-comparison).
- [Pure SP proves true Π₂ arithmetic, with a conditional Π₃ boundary](#sp-arithmetic-reflection).
- [Lambda-free reconstruction and contextual beta eta conversion](#lambda-free-translation). **Lean certified.**
- [Logical observer separation and its strict hierarchy](#logical-observers). **Lean certified H + OS ⇒ C + BF step.**
- [Infinitary Comprehension + C5 characterizes full standard models](#infinitary-comprehension).

<a id="categories"></a>
## Contents

| Part | Sections |
|---|---|
| [I. Resolved database questions and connections](#database-connections) | [Maximalism and Strong Possibility](#maximalism-and-possibility); [Choice and rigidity](#choice-and-rigidity); [Infinity](#infinity-connections); [Continuum Hypothesis and forcing](#continuum-hypothesis-and-forcing); [Previously known results formalized](#previously-known-results-formalized). |
| [II. Further results about established principles](#established-principles) | [Choice and completeness](#choice-and-completeness); [Arithmetic and analysis](#arithmetic-and-evaluation); [Strong Possibility and language](#possibility-and-language); [Model theory and computational complexity](#model-theory-and-computational-complexity). |
| [III. Extensions and new directions](#extensions-and-new-directions) | [Abstraction and infinitary extensions](#abstraction-and-infinitary-extensions); [Evaluation and separating operators](#operators-and-evaluation); [Logical observers](#h-observer-separation); [Worlds, profiles and probability](#worlds-and-probability). |

<a id="database-connections"></a>
## I. Resolved database questions and connections

<a id="maximalism-and-possibility"></a>
### Maximalism and Strong Possibility

<a id="max-atomicity"></a>
#### Max + Atomicity (type t) ⇒ ⊥

C + pure Maximalism + Atomicity (type t) is inconsistent.

The substantial construction turns the Jech–Shelah rigid atomless algebra into a finite closed pure code; only then can a Max instance supply the contradiction with Atomicity.

**Lean certified.** · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#max-atomicity).

<a id="sp-signature-conflict"></a>
#### Strong Possibility depends on the signature

For every map-admitted signature Σ, SP(Σ) entails SP(pure) exactly when SP(Σ) is inconsistent. More strongly, SP(pure) is incompatible with Max(Σ). The reverse entailment, from SP(pure) to SP(Σ), holds exactly when SP(pure) is inconsistent. The signature must contain a relational constant; the reference Max theories remain distinct.

The [signature-extension results](#signature-finite-boundary) identify when adding names preserves the old theory.

**Lean certified:** The signature-splitting lemma used in the incompatibility proof. · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#sp-signature-conflict).

<a id="sp-barcan-functionality"></a>
#### Finite-signature SP refutes BF and Functionality at every input type

For every finite signature Σ, including the empty signature, SP(Σ) refutes BF (type α) at every admitted α and every Functionality instance with input α and relational output β. Explicit counterpredicates and pairs of operations witness the failures. The extension to infinite relational signatures covers individual inputs only.

[Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#sp-barcan-functionality).

<a id="npc-atomicity"></a>
<a id="signature-independence"></a>
[Supplemental results in this category](evidence/RESULT-INDEX.md#supplement-maximalism-and-possibility) · [Back to contents](#categories)

<a id="choice-and-rigidity"></a>
### Choice and rigidity

<a id="choice-completeness"></a>
#### Choice and completeness produce Actuality and transversals

Relational Choice from t to t plus Boolean Completeness (type tt) implies Actuality. Relational Choice plus Boolean Completeness implies Transversal Choice. Relational Choice alone implying Transversal Choice remains unresolved.

The direct proof adapts Bourbaki–Witt inside C: represented joins preserve partial transversals, and guarded progress yields a fixed point without assuming Plenitude.

**Lean certified:** The stated Actuality and RC + BC ⇒ TC implications. · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#choice-completeness).

<a id="logical-necessity-separation"></a>
#### Logical Necessity and strong selection laws do not force Actuality

For the specified one-predicate signature, a supported-product model satisfies Logical Necessity, ☐BF and ☐Relational Choice while failing Actuality and Vicinity. Strong selection and modal laws therefore do not supply an actual-world truth selector by themselves.

**Lean certified.** · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#logical-necessity-separation).

<a id="rigidity-nd-bc"></a>
<a id="oldnew-separation"></a>
#### Four rigidity principles coincide over ND and Boolean Completeness

Over C + ND + Boolean Completeness, Inextensible Comprehension, Rigid Comprehension, Tame Rigidity and Weakly Rigid Power are equivalent. The old/new countermodel satisfies the base while refuting all four: the common extra strength is not already supplied by ND and completeness.

**Lean certified.** · [Proof length](#proof-length): medium.

[Equivalences](evidence/RESULT-INDEX.md#rigidity-nd-bc) · [Countermodel](evidence/RESULT-INDEX.md#oldnew-separation).

<a id="modal-propagation"></a>
#### Strong Leibniz Biconditionals and Rigid Comprehension force modal stability

Strong Leibniz Biconditionals plus Rigid Comprehension entails ☐Strong Leibniz Biconditionals, ☐BF (type τ, τ ≠ e), ☐Rigid Comprehension and ☐Boolean Completeness.

**Lean certified.** · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#modal-propagation).

<a id="rigidity-classifications"></a>
<a id="finite-compression-separation"></a>
#### TR + RP does not imply WRP

Weakly Rigid Power is equivalent to Tame Rigidity + Rigid Power + bounded future-tameness: every future weakly rigid subrelation of an actual rigid bound must be rigid. A finite compression model satisfies Tame Rigidity and Rigid Power but fails Weakly Rigid Power (type et), refuting the conjectured implication without the extra condition.

Compression and return maps remove label parameters from rigid subrelations, while approximate lifting supplies Rigid Power at every type.

**Lean certified.** · [Proof length](#proof-length): long.

[Characterization](evidence/RESULT-INDEX.md#rigidity-classifications) · [Countermodel](evidence/RESULT-INDEX.md#finite-compression-separation).

<a id="fixed-point-entrance"></a>
#### Comprehension, completeness and choice do not force ☐Tame Rigidity

A fixed-point entrance C-model with singleton individuals satisfies Atomicity, Boolean Completeness, Rigid Comprehension, Relational Choice, Tame Rigidity, Rigid Power and Weakly Rigid Power at every relational type, together with ☐Strong Actuality and BF (type e). It refutes ☐Tame Rigidity at type (tt)t, BF at every relational argument type, ND (type t), and Strong Leibniz Biconditionals at every relational type.

Attach a fixed-point entrance to a qualitative tail. Exact-image relations supply comprehension and the rigid powers; the root relation algebras are complete and atomic. The substantial model argument constructs admitted qualitative codes, proves their injectivity and verifies finite pinning, yielding a weakly rigid relation whose transport is not weakly inextensible.

**Lean certified.** · [Proof length](#proof-length): medium.

[Proof and certificate](evidence/RESULT-INDEX.md#fixed-point-entrance).

<a id="colour-collapse-scope"></a>
<a id="coextension-operations"></a>
<a id="choice-coherence"></a>
[Supplemental results in this category](evidence/RESULT-INDEX.md#supplement-choice-and-rigidity) · [Back to contents](#categories)

<a id="infinity-connections"></a>
### Infinity

<a id="finite-type-propagation"></a>
#### Quantified Infinity at all types reduces to two base types

Over C, Axiom of Infinity (type t) is equivalent to Axiom of Infinity at every relational type. Adding Axiom of Infinity (type e) gives the schema at every admitted type. These are ordinary consequences of the certified downward finiteness theorem.

Under the relevant Functionality instances, finiteness at a relational type is equivalent to finiteness at t when the type contains no e, and to finiteness at both e and t otherwise. The countermodels explain why upward finiteness needs the extra assumption.

**Lean certified:** Finiteness propagation, descent, and the exact classification by type. The four C5 base-infinity combinations and the stated two-stage model/finiteness/Functionality endpoints. · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#finite-type-propagation).

<a id="infinity-schema-separation"></a>
#### Infinity schemata do not imply their quantified axioms, even with necessary Choice

C + ☐Functional Choice has a Henkin model satisfying both finite lower-bound Infinity schemata while necessarily refuting both corresponding quantified Axioms of Infinity. A second model satisfies ☐Functional Choice, ☐FP, ☐Axiom of Infinity (type t) and the individual Infinity schema while necessarily refuting Axiom of Infinity (type e).

[Proof length](#proof-length): short.

[Proofs](evidence/RESULT-INDEX.md#infinity-schema-separation).

[Back to contents](#categories)

<a id="continuum-hypothesis-and-forcing"></a>
### Continuum Hypothesis and forcing

<a id="ch-coalesced"></a>
#### CH can vary despite boxed structural principles

Assuming Con(ZFC), CH varies in a model satisfying ☐Atomicity, ☐BF, ☐Strong Leibniz, ☐Rigid Rigidity, ☐Weakly Rigid Weak Rigidity, ☐Tame Rigidity and Modal Well-Ordering together. All the relational schemata hold at every admitted relational type; BF and Well-Ordering include e. The two possible real structures disagree at the same type e. The component construction needs neither transitive set models nor standard natural numbers.

The two leaves use their own set-theoretic real fields and disagree about CH. Free root components preserve the generic atomicity, Barcan, rigidity and well-ordering arguments.

**Lean certified:** Opposite-CH components at type e and their coalesced C countermodel with ☐BF, constructed in Lean’s ambient metatheory. · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#ch-coalesced).

<a id="max-ch"></a>
#### Maximalism is incompatible with Non-contingency of CH

Assuming Con(ZFC), the separate C-consistency of real structures satisfying CH and its negation gives

$$
\mathrm{Max}(C)+\text{Non-contingency of CH}\ \vdash\ \bot.
$$

Maximalism makes both real-structure assertions possible at the same type $e$.

**Lean certified:** Maximalism + Non-contingency of CH ⇒ ⊥, using constructed type-e components in Lean’s ambient metatheory. · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#max-ch).

<a id="forcing-transfer"></a>
#### The full modalized cloud realizes both sides of CH

In the specified full modalized-domain construction, finite relational types correspond to their Boolean-valued counterparts. The resulting lottery cloud makes both CH and its negation possible for real structures at the same type et. This is a theorem about that full construction, not a consequence established for the proposed abstract modal axioms alone.

[Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#forcing-transfer).

<a id="forcing-possibilism"></a>
#### Strict-smallness Forcing Possibilism is independent of necessary Choice and Infinity

With the database’s strict-smallness definition, FP is independent over C + ☐Functional Choice + Axiom of Infinity (types e and t). Countably many S5 worlds supply the positive model; the negative direction was already recorded. More generally, for infinite W in external ZFC,

$$
\mathrm{FullS5}(W)\models\mathrm{FP}\quad\Longleftrightarrow\quad 2^{|W|}=2^{\aleph_0}.
$$

A free-root model also satisfies FP and both quantified Infinity axioms while failing Intensional Choice. The cardinal criterion need not make W countable.

[Proof length](#proof-length): medium.

[Proofs](evidence/RESULT-INDEX.md#forcing-possibilism).

[Back to contents](#categories)

<a id="previously-known-results-formalized"></a>
### Previously known results formalized

These contributions formalize existing mathematics. The original attribution is retained.

#### C5 + Atomicity (type t) ⇒ No Pure Contingency

**Source:** Zachary Goodsell and Juhani Yli-Vakkuri; proof following Cian Dorr’s sketch.

The proof swaps two Boolean atoms, extends the swap by conjugation through every relational type, and proves that every closed pure term is fixed. The final contradiction is short once this invariance is established.

**Lean certified:** The full theorem for closed pure sentences.

[Proof length](#proof-length): medium. [Proofs and certificates](evidence/RESULT-INDEX.md#npc-atomicity).

#### C5 + ☐Rigid Comprehension ⇒ Second-Order Analytic Necessitism

**Source:** Zachary Goodsell and Claude Fable 5.1, prompted by Goodsell, following Bacon’s Corollary 5.1 and Appendix C.2.

Replace the relations of a possible real structure by rigid coextensions. C5 and Barcan transfer their first-order properties between worlds; applying Rigid Comprehension to arbitrary subproperties transfers completeness too. Rigid relations supported on the domain then supply the represented powers.

**Lean certified:** Rigidification and simultaneous represented powers of every prescribed finite list of positive arities, at every closed admitted type and in arbitrary signatures.

[Proof length](#proof-length): short. [Proofs and certificates](evidence/RESULT-INDEX.md#analytic-rigidification).

#### Symmetric ideally-full model: old and new individuals

**Source:** Claude Fable 5.1 and Claude Opus 5.5, prompted by Cian Dorr; Dorr’s symmetric ideally-full semantics.

Finite pinning and permutation symmetry control which intensions are admitted. Extending finite partial injections preserves distinctions and establishes ND. A new individual, excluded at one stage but carried back among the old individuals later, obstructs Inextensible Comprehension and the associated rigidity principles.

**Lean certified:** The construction, ND, and the previously recorded failures of Inextensible Comprehension, Rigid Comprehension and Tame Rigidity.

The all-type Boolean Completeness verdict is a separate correction and strengthening, presented above.

[Proof length](#proof-length): medium. [Proofs and certificates](evidence/RESULT-INDEX.md#oldnew-separation).

<a id="established-principles"></a>
## II. Further results about established principles

<a id="choice-and-completeness"></a>
### Choice and completeness

<a id="sections-retractions"></a>
<a id="boolean-retractions-choice"></a>
<a id="c5-strong-retractions"></a>
#### Choice and Plenitude through sections and retractions

Functional Choice is equivalent to Actuality plus pointwise sections of actual surjections; Plenitude is equivalent to Actuality plus pointwise retractions of actual injections. ☐Functional Choice is also equivalent to ☐Actuality plus the strong-section schema.

By contrast, requiring every actual injection between relational types to have a necessarily correct left inverse characterizes C5, without Actuality or Choice.

Over ☐Plenitude, ☐Functional Choice has an algebraic characterization: every admitted rigid Boolean subalgebra at every relational type, complete for families admitted by the model, has a [complete Boolean retraction](CANDIDATES_DK.md#complete-boolean-retractions). The necessary strong-section equivalence uses the Goodsell–Yli-Vakkuri No Pure Contingency theorem.

The reverse direction encodes witnesses into an actual surjection so that any section yields Choice. The necessary version also uses the substantial pure-term invariance proof behind No Pure Contingency.

**Lean certified:** The Functional Choice, Plenitude and ☐Functional Choice decompositions; the constituent directions of the C5/strong-retraction characterization. · [Proof length](#proof-length): long.

[Sections and retractions](evidence/RESULT-INDEX.md#sections-retractions) · [Boolean retractions](evidence/RESULT-INDEX.md#boolean-retractions-choice) · [Strong retractions and C5](evidence/RESULT-INDEX.md#c5-strong-retractions).

<a id="countable-boolean-finiteness"></a>
#### Countable completeness forces Frege finiteness at countable Boolean types

In C, a relational Boolean type that is countable in the model is countably complete exactly when it is Frege-finite. Countability in the model plus the matching Countable Boolean Completeness therefore implies Actuality, without Choice, Infinity, BF, ND or Plenitude.

[Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#countable-boolean-finiteness).

<a id="choice-no-finite-basis"></a>
#### Functional Choice and ☐Functional Choice have no finite fixed-type basis

Neither Functional Choice nor ☐Functional Choice is equivalent over C to any finite list of pure fixed-type sentences. Selector strength forms a strict hierarchy as the available types increase. The proposed axioms may be arbitrary pure sentences, not merely Choice instances. This does not exclude finite stronger theories or finitely many unbounded type schemata.

A coherent Boolean-valued type hierarchy supports lower-type selectors and a higher-type obstruction. Countable witness extraction recovers an ordinary C-model, and translation back to the original pure syntax yields the finite-basis obstruction.

**Lean certified.** · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#choice-no-finite-basis).

[Back to contents](#categories)

<a id="arithmetic-and-evaluation"></a>
### Arithmetic and analysis

<a id="arithmetic-comparison"></a>
#### ☐Functional Choice and ☐Plenitude have the same ordinary arithmetic

Over C with Axiom of Infinity (types e and t), replacing ☐Plenitude by ☐Functional Choice adds no ordinary first-order arithmetic theorems. Both have the arithmetic consequences of C plus numerical noncollapse at e, and this remains true after adding ☐Axiom of Infinity (type σ) at every admitted σ. This establishes arithmetic conservation, not higher-order or modal conservation.

The interpretation chain must preserve the arithmetic sort and the quantified Infinity axioms. Equiconsistency alone would not give conservation of individual arithmetic sentences.

[Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#arithmetic-comparison).

<a id="sp-arithmetic-reflection"></a>
#### Pure SP proves true Π₂ arithmetic, with a sharp conditional boundary

Under the specified pure Frege translation, pure SP proves every standard-true Π₂ arithmetic sentence. More generally, proofs in C plus numerical noncollapse of every standard numeral instance of P yield the universal numerical closure of P in SP. If SP is consistent, some true Π₃ sentence remains unprovable. This is a one-step reflection principle, not an iterated ω-rule for SP.

[Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#sp-arithmetic-reflection).

<a id="max-arithmetic-equality"></a>
#### Proposed exact arithmetic strength of pure Maximalism

The proposed equality says that pure Maximalism proves exactly the ordinary first-order arithmetic consequences of the positive packages’ common arithmetic theory together with all standard-true Π₁ sentences.

$$
\mathrm{Th}_{\mathrm{arith}}(\mathrm{Max}(C))=\mathrm{Cn}\bigl(T_{\mathrm{arith}}\cup\mathrm{True}_{\Pi_1}\bigr).
$$

Here $T_{\mathrm{arith}}$ is the [common arithmetic theory](#arithmetic-comparison), $\mathrm{True}_{\Pi_1}$ means standard-true Π₁ sentences, and $\mathrm{Cn}$ is first-order deductive closure. The upper inclusion still awaits independent review.

[Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#max-arithmetic-equality).

<a id="max-predecessor"></a>
#### Maximalism forbids a numerical predecessor operation

At every admitted counting type, pure Maximalism refutes an operation sending each Frege successor back to its predecessor, without an Infinity or consistency premise. Yet a total single-valued predecessor graph is available: a functional arithmetic relation need not be representable by an intensional operation.

**Lean certified:** The no-predecessor theorem at every closed counting type; the total unique graph and Plenitude failure at e. · [Proof length](#proof-length): short.

[Proofs and certificates](evidence/RESULT-INDEX.md#max-predecessor).

<a id="analytic-rigidification"></a>
#### Rigid Comprehension stabilizes a possible real structure

Over C5 plus ☐Rigid Comprehension, a possible real structure at a fixed type has a rigid representative that is necessarily a real structure. Represented powers can be supplied at any prescribed finite list of arities. The initial possibility premise is retained; completeness ranges over subproperties admitted by the model.

**Lean certified:** Rigidification and simultaneous represented powers of every prescribed finite list of positive arities, at every closed admitted type and in arbitrary signatures. · [Proof length](#proof-length): short.

[Proofs and certificates](evidence/RESULT-INDEX.md#analytic-rigidification).

<a id="arithmetic-foundations"></a>
[Supplemental results in this category](evidence/RESULT-INDEX.md#supplement-arithmetic-and-evaluation) · [Back to contents](#categories)

<a id="possibility-and-language"></a>
### Strong Possibility and language

<a id="sp-criteria"></a>
#### Strong Possibility is an exact universal-identity theory

Pure Strong Possibility is equivalent over C to all closed pure universal finite-Boolean-identity sentences individually consistent with Max. Assuming Max is consistent, SP is consistent exactly when Max has the specified restricted finite-disjunction property for existential finite-Boolean-identity sentences. The criterion is proved; the required disjunction property remains unresolved.

**Lean certified:** The universal-core equivalence and the stated conditional disjunction criterion. · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#sp-criteria).

<a id="sp-individual-cardinality"></a>
#### SP fixes the actual domain from the number of individual names

If Σ has exactly u < ∞ individual constant symbols, SP(Σ) entails exactly max(1,u) actual individuals; when u is positive, the names enumerate the domain bijectively. SP(pure) therefore entails one actual individual. This does not assert necessary exhaustion or exhaustion by infinitely many names.

**Lean certified:** The conditional monism/reflection lemma. · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#sp-individual-cardinality).

<a id="signature-finite-boundary"></a>
<a id="signature-infinite-reservoir"></a>
#### An exact finite-signature boundary and an infinite-reserve contrast

For a proper extension of finite signatures Σ ⊊ Σ′, Max(Σ′) preserves every Max(Σ)-consistent old-language condition exactly when Σ has no individual names and the extension adds one individual name and no relational constants.

If Σ already has infinitely many constants at every type where Σ′ adds them, both Max(Σ′) and SP(Σ′) are conservative over the old-language theories. The fresh-name supply changes the answer; this does not assert that every old model admits an expansion.

[Proof length](#proof-length): long.

[Finite extension classification](evidence/RESULT-INDEX.md#signature-finite-boundary) · [Infinite-reserve conservativity](evidence/RESULT-INDEX.md#signature-infinite-reservoir).

<a id="sp-finite-profile-rank"></a>
#### Pointed logical possibilities determine finite Boolean ranks

For a closed pure proposition A, consider the complete consistent theories extending C(a)+A, with one fresh individual name a. Max is consistent with “there are no k+1 disjoint nonzero subpropositions of A” exactly when there are at most k such theories. If there are exactly k, SP(pure) forces the Boolean interval below A to have k atoms and 2ᵏ elements.

This extends the atom classification to every finite rank. Here k is a fixed finite number; the result does not establish consistency of SP.

[Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#sp-finite-profile-rank).

<a id="pure-sp-bounded-image"></a>
<a id="signature-sp-survival"></a>
[Supplemental results in this category](evidence/RESULT-INDEX.md#supplement-possibility-and-language) · [Back to contents](#categories)

<a id="model-theory-and-computational-complexity"></a>
### Model theory and computational complexity

<a id="computability-comparison"></a>
#### Theoremhood and model construction have successive jump thresholds

The positive theories, Max and SP occupy three successive levels of computational strength.

| Pure theory | Theoremhood | Oracles computing some adequate countable model |
|---|---|---|
| C + ☐Plenitude + Axiom of Infinity (types e and t) | $\Sigma^0_1$-complete | PA degrees |
| C + ☐Functional Choice + Axiom of Infinity (types e and t) | $\Sigma^0_1$-complete | PA degrees |
| Max | $\Sigma^0_2$-complete | PA degrees over $0'$ |
| SP, **if consistent** | $\Sigma^0_3$-complete | PA degrees over $0''$ |

Adequate codes provide term interpretation and actual truth. PA degree over an oracle means the ability to compute a binary diagonally nonrecursive function relative to it; ordinary PA degrees use no oracle. The positive bounds already hold with the weaker Infinity schema at one admitted type. The theoremhood classifications persist under consistent extensions enumerable in the corresponding oracle.

[Proof length](#proof-length): long.

[Proofs](evidence/RESULT-INDEX.md#computability-comparison).

<a id="exact-model-degrees"></a>
#### A complete theory has a model of exactly its computational degree

Every supplied complete consistent pure theory Γ extending C has a countable model of exactly Γ’s Turing degree, uniformly constructed from Γ. The construction preserves its exact pure theory. Together with reversible coding into completions, this realizes every degree in the positive and Max classes in the preceding table. These are degrees across models of a theory, not copies of one fixed model.

[Proof length](#proof-length): long.

[Proofs](evidence/RESULT-INDEX.md#exact-model-degrees).

<a id="standard-number-models"></a>
#### Standard natural numbers impose a much stronger computational barrier

Requiring the Frege numbers to be exactly the standard numerals changes the comparison sharply. With numerical noncollapse, every adequate standard-number code computes every hyperarithmetical real and is itself nonhyperarithmetical. Yet, for the positive packages with the specified Infinity assumptions and for Max, some standard codes lie strictly below Kleene’s O, and there is no least solution degree. Exactly the hyperarithmetical reals are computable from every standard code.

For those standard-model classes, finite-condition satisfiability is $\Sigma^1_1$-complete and validity is $\Pi^1_1$-complete. These are semantic restrictions; the corresponding SP claims require a standard SP model, whose existence is unresolved.

[Proof length](#proof-length): long.

[Proofs](evidence/RESULT-INDEX.md#standard-number-models).

<a id="completion-spaces"></a>
#### Finite descriptions distinguish the completion spaces

In the space of complete consistent pure C-theories, Max forms a nonempty closed nowhere-dense set: every consistent finite description admits a refinement violating Max. C + ☐Plenitude forms a clopen set. For either C + ☐Plenitude or C + ☐Functional Choice, isolated completions are exactly the full Gallin theories with finite individual and world domains; removing those points leaves a perfect space with dense low completions. More generally, any consistent computably enumerable pure-complete extension of C fixes finite actual domains at every type, with recursively computable exact sizes and necessary finite bounds.

[Proof length](#proof-length): long.

[Proofs](evidence/RESULT-INDEX.md#completion-spaces).

[Back to contents](#categories)

<a id="extensions-and-new-directions"></a>
## III. Extensions and new directions

<a id="abstraction-and-infinitary-extensions"></a>
### Abstraction and infinitary extensions

<a id="syntax-and-translation"></a>
<a id="lambda-free-translation"></a>
<a id="beta-eta-conversion"></a>
#### Lambda-free reconstruction and contextual beta eta conversion

An explicit classical applicative calculus with equality, quantifier binders, primitive ☐, K, theorem-only necessitation, all-relational Intensionality and uniform strong comprehension has exactly C’s consequences in its original language, including open contexts and assumptions. A conservative named extension reconstructs arbitrary C terms. No Choice, BF or Infinity premise is added.

Separately, on raw typed lambda syntax, beta identity at every relational output type plus application congruence and the theorem-only fresh-variable rule derives eta, lambda congruence and all contextual beta eta conversion. Positive-arity Intensionality supplies that rule; nullary Intensionality is unnecessary for this separate conversion theorem.

The proof constructs bracket abstraction, substitution coherence and both term round trips, then conservatively erases the finitely many names used by each proof.

**Lean certified.** · [Proof length](#proof-length): long.

[Lambda-free reconstruction](evidence/RESULT-INDEX.md#lambda-free-translation) · [Beta eta conversion](evidence/RESULT-INDEX.md#beta-eta-conversion).

<a id="infinitary-comprehension"></a>
#### Infinitary Comprehension and C5 characterize full standard models

Every infinitary formula defines a relation with the same truth conditions at every accessible point.

$$
\exists R^{\sigma_1\cdots\sigma_n t}\,\Box\forall x_1\cdots x_n\,\bigl(R[\bar x]\leftrightarrow A\bigr).
$$

A is any classical formula built using arbitrary set-sized well-founded conjunctions and disjunctions, with any set-sized family of typed parameters; R is not free in A. Each instance holds for every simultaneous parameter assignment. The argument tuple is finite and may be empty.

With C5, this schema characterizes the full standard relational hierarchies; Atomicity follows from the infinitary resources. In ZFC it also gives ☐Functional Choice, while leaving the sizes of the individual and world domains unrestricted.

For every infinite regular κ, a one-world model satisfies C5, Atomicity and every instance with fewer than κ parameters, regardless of formula size, but fails the unrestricted schema. At κ = ω its individual predicates are exactly the finite and cofinite subsets.

For the related algebraic characterization, see [Arbitrary Atomic Joins](#full-standard-gallin).

**Lean certified:** For universe-0 categorical premodels, term-denotation closure + unrestricted original-closed-type Infinitary Comprehension + ☐ND (type t) imply faithful full-standard representation; full standard models satisfy the corresponding infinitary axioms. · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#infinitary-comprehension).

<a id="full-standard-gallin"></a>
#### Arbitrary Atomic Joins characterize full Gallin hierarchies

At every relational type, every family of atoms has a least upper bound, whether or not a property in the model collects that family. For each relational type $\tau$ and set $I$, take the instance

$$
\small\textstyle \forall(a_i^\tau)_{i\in I}\, .\, (\bigwedge_{i\in I}\mathrm{Atom}_\tau(a_i)) \to\exists b^\tau\, . [ (\bigwedge_{i\in I}a_i\le_\tau b)\land \forall c^\tau\, .\, ((\bigwedge_{i\in I}a_i\le_\tau c)\to b\le_\tau c) ].
$$

The type $\tau$ and set $I$ index the schema. Each instance uses the existing definitions of atoms and algebraic order, with set-indexed conjunctions and a block of quantifiers over all the $a_i$. These are sentences of an infinitary extension of the original language; assignments range over all families, not just named or property-coded ones.

Over C + C5 + Atomicity (type t), Arbitrary Atomic Joins is equivalent to fullness of the canonical standard hierarchy, or to representation of every subset of each typed domain. No Infinity premise is needed. Boolean Completeness covers only families already represented by properties. No fixed bound on family size forces fullness across arbitrary model sizes.

[Infinitary Comprehension](#infinitary-comprehension) gives the corresponding characterization without a separate Atomicity premise.

[Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#full-standard-gallin).

<a id="infinitary-resources"></a>
#### Infinitary formation changes named exhaustion and arithmetic

For a signature with countably many individual names, admitting a predicate that holds exactly of individuals different from every name supplies the named-exhaustion reflection argument. A separate construction proves the needed Max-eligibility for an explicit semantic reference theory T_d; the corresponding SP(T_d) entails exactly countably many actual individuals. It does not prove SP(T_d) consistent or give the same result for an unspecified infinitary calculus.

A different addition—one countable numeral abstraction—makes the Frege number field standard at points satisfying numerical noncollapse and conflicts with Max referenced to finitary C. Infinitary assertions, term formation and inference therefore have different consequences.

[Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#infinitary-resources).

[Back to contents](#categories)

<a id="operators-and-evaluation"></a>
### Evaluation and separating operators

<a id="evaluators-cores"></a>
#### Six strictly different strengths of actual-truth evaluation

For $E^{tt}$, correct evaluation means

$$
\mathrm{Eval}(E):=\forall p^t\, .\,(p\to Ep=\top)\land(\neg p\to Ep=\bot).
$$

The following requirements form a strict hierarchy over C, with each row stronger than the preceding one.

| Requirement | Equivalent principle |
|---|---|
| $\exists f^{tt}\, .\,\forall p^t\, .\,p\leftrightarrow fp=f\top$ | Actuality |
| $\exists E^{tt}\, .\,\mathrm{Eval}(E)$ | ND + Actuality |
| $\exists E^{tt}\, .\,\mathrm{Eval}(E)\land\bigl(\Box\forall p^t\, .\,Ep=\top\lor Ep=\bot\bigr)$ | Gallin Extensional Comprehension; equivalently ND + Strong Actuality |
| $\exists!E^{tt}\, .\,\mathrm{Eval}(E)$ | C5 + Actuality |
| $\Box\exists E^{tt}\, .\,\mathrm{Eval}(E)$, equivalently $\Box\exists!E^{tt}\, .\,\mathrm{Eval}(E)$ | ☐Plenitude |
| $\exists E^{tt}\, .\,\Box\mathrm{Eval}(E)$ | Extensionality |

The last two rows separate an evaluator available at each world from one fixed evaluator correct at every world. Uniqueness in the fourth row is among all evaluators correct at the current world. The third row already gives Boolean and quantifier identities for current predicates; the stronger ☐∀F law remains unresolved.

Actuality alone also interprets extensional Henkin higher-order logic over all current individuals. Represented relations and quantified Infinity transfer exactly, and Relational Choice supplies ordinary Choice in this interpretation. The construction makes no claim that its domains persist at other worlds.

**Lean certified:** Actuality-core conversion and admitted-value lemmas. · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#evaluators-cores).

<a id="uniform-complete-evaluators"></a>
#### Uniform evaluator selection measures well-orderability and Choice

Over C + ☐Plenitude, one admitted operator choosing, for each nonzero proposition p, a complete bivalent evaluator sending p to ⊤ exists exactly when the world atoms admit a represented well-order. Requiring such selectors at every relational type is equivalent to ☐Functional Choice. The propositional requirement and all-type Intensional Choice are independent over C + ☐Plenitude. Here completeness means preservation of all admitted rigid meets; these evaluators take only ⊥ and ⊤ as values.

[Proof length](#proof-length): long.

[Proofs](evidence/RESULT-INDEX.md#uniform-complete-evaluators).

<a id="diagonal-characters"></a>
#### Diagonal characters characterize ND + Atomicity at type t

A diagonal character preserves ⊥ and negation, takes only ⊤/⊥ values, and accepts

$$
w_E:=\forall p^t\, .\,Ep\to p.
$$

Separation by such characters is equivalent to ND (type t) + Atomicity (type t); neither BF nor Choice is needed.

For the stronger logical-observer schema, see [Logical Observer Separation](#logical-observers).

**Lean certified.** · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#diagonal-characters).

<a id="full-identity-observers"></a>
#### Symmetry controls the representation of observers

Over C + ☐ND (type t) + Actuality, propositional separation by observers preserving Boolean operations and quantification at t as composite operation identities is equivalent to Atomicity (type t). Atomicity supplies the corresponding observers at each fixed quantifier type.

In the specified symmetric ideally-full models with closed target symmetry groups, an arrow’s truth-evaluation map is representable exactly when the transported stabilizer of some finite set is contained in the target symmetry group. A representing observer can preserve Boolean operations and both quantifiers as operation identities.

The ordered symmetry construction separates these demands: Boolean observer separation holds at every world, and ☐BF holds, while quantifier separation fails at type e. This gives a route to studying observers through permutation groups, beyond the atomic sufficient conditions.

**Lean certified:** The propositional Atomicity characterization at t; simultaneous separation for every finite list of quantifier types under C5 + Atomicity (type t), with the converse under C5 + Actuality. · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#full-identity-observers).

<a id="evaluator-modal-commutation"></a>
[Supplemental results in this category](evidence/RESULT-INDEX.md#supplement-operators-and-evaluation) · [Back to contents](#categories)

<a id="h-observer-separation"></a>
### Logical observers

<a id="logical-observers"></a>
#### Logical observer separation: a branching implication map

Requiring separation by **logical observers → endpoint observers → a unique observer** leads respectively to C + BF, C5 + Atomicity (type t), and Extensionality over H. Under Extensionality, truth is itself an endpoint-valued observer. Over C, every arrow below is strict:

$$
\small\text{Extensionality}\ \Rightarrow\ \mathrm{C5}+\mathrm{Atomicity}_t\ \Rightarrow\ \Box\mathrm{OS}\ \Rightarrow\ \mathrm{OS}\ \Rightarrow\ \mathrm{BF}.
$$

Reversible logical separation implies No Pure Contingency without atoms or Actuality. The [observer section](#h-observer-separation) and [full map](proofs/h-observer-space/GRAPH.md) give the other branches and separating models.

**Lean certified:** H + OS ⇒ C + BF in the equivalent formulation with explicit endpoint identities. · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#logical-observers).

<a id="h-observer-space"></a>
#### Preservation, representation and logical observers

The [dedicated page](proofs/h-observer-space/GRAPH.md) develops the map from H, with exact premises, diagrams, proofs and countermodels. Its main results are:

- **Preservation and higher types.** For the finite family of independent primitive clauses, implication between separation principles is exactly reverse inclusion of clauses. Full typed separation factors into propositional separation plus Functionality.
- **Reversibility.** Separation by reversible logical observers (Rev) implies C5 + ☐OS + No Pure Contingency. Both chains Rev ⇒ SurjSep ⇒ OS and Rev ⇒ SplitMono ⇒ OS are strict; SurjSep and SplitMono require surjective observers and admitted qualified left inverses, respectively, and are incomparable. Over C5, SurjSep is Rev.
- **The endpoint boundary.** OS + Plenitude at (t,t) is equivalent over H to endpoint separation, hence to C5 + Atomicity (type t). Reversibility can hold in atomless models; one atom raises it to endpoint separation.
- **Canonical adjoints.** Over C5, every logical observer qualified at t has admitted order adjoints. These characterize injection, surjection and reversibility. A Boolean observer commutes with necessity exactly when it is injective.
- **Limits of combination and persistence.** Separate preservation requirements need not combine. SurjSep entails neither ☐OS nor ☐BF, even though an individual observer’s surjectivity persists over C + BF (type t).
- **Exact characterizations.** Over C5, Rev is characterized by its fixed propositions. Laws on the whole reversible group give sharp finite bounds; internally finite observer families give exact finiteness characterizations. [Statements and proofs](proofs/h-observer-space/GRAPH.md#reversibility-and-the-invariant-proposition-algebra).

The [detailed map and research frontier](proofs/h-observer-space/MAP.md) also cover weaker connective fragments, normalization, character extension and atomless order models.

**Main unresolved question:** does injective logical separation imply separation by logical observers with logical left inverses? The converse holds; this direction remains open over H and over C5. [Exact question and positive cases](CONJECTURES.md#observer-strength).

**Lean certified:** The foundational implication H + OS ⇒ C + BF, with explicit endpoint identities. · [Proof length](#proof-length): long.

[Map and proofs](evidence/RESULT-INDEX.md#h-observer-space).

[Back to contents](#categories)

<a id="worlds-and-probability"></a>
### Worlds, profiles and probability

<a id="profile-world-algebra"></a>
#### Profile richness and Functional Choice are separate requirements

Over ☐Plenitude, the world-representation results support consistent individual profile-realization strengthenings. Nominal models realize every finite supported richness rank while failing Functional Choice. Unrestricted relational-input realization instead meets a diagonal obstruction; it must not be identified with individual or finitely supported realization.

**Lean certified:** The finite-profile and atomic-profile results. · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#profile-world-algebra).

<a id="nominal-orbits"></a>
#### World orbits determine propositional Dedekind infinity

In the specified finite-support permutation models, propositions admit an injective nonsurjective operation exactly when there are infinitely many world orbits. Even infinitely many worlds can form just one orbit.

On atom worlds, ☐Intensional Choice at every admitted type coexists with the necessary failure of this operational Dedekind infinity. This concerns operations on propositions, not the quantified Frege Axiom of Infinity.

The key combinatorial step makes each fixed-support proposition stratum finite when there are finitely many world orbits; an injective operation omitting a value would produce infinitely many distinct iterates in one such stratum.

**Lean certified.** · [Proof length](#proof-length): medium.

[Proofs and certificates](evidence/RESULT-INDEX.md#nominal-orbits).

<a id="probability"></a>
#### Faithful probability has an exact finite-fibre condition and type ceiling

Over C + ☐Plenitude + Axiom of Infinity (type e), faithful probability is equivalent to admitted finite-fibre numerical labelling of world atoms. Countable Choice for finite fields strengthens this to countability in the model. Higher-type probability faces a finiteness obstruction.

**Lean certified:** Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone. · [Proof length](#proof-length): long.

[Proofs and certificates](evidence/RESULT-INDEX.md#probability).

[Back to contents](#categories)

## Remaining central questions

- [Does Relational Choice entail Transversal Choice?](CONJECTURES.md#rc-tc) — Unresolved; sharper positive and negative criteria.
- [Is pure Strong Possibility consistent?](CONJECTURES.md#pure-sp) — Unresolved; exact criteria and construction obstructions.
- [Is SP consistent for one unary predicate constant and no individual names?](CONJECTURES.md#signature-sp) — Unresolved; first-stage sufficient criterion.
- [Does injective logical separation imply logical left-inverse separation?](CONJECTURES.md#observer-strength) — Unresolved over H and over C5.

Further reductions, failed constructions and incomplete formalizations are recorded in the [question register](CONJECTURES.md).

<a id="proof-length"></a>
## Proof length

**Short:** under 1,000 words. **Medium:** 1,000–3,000. **Long:** over 3,000. Every entry is rated by the selected mathematical exposition, including substantive supporting arguments. Grouped entries combine their source passages, counting overlapping lines once. Alternative proofs, Lean code and compiler logs are excluded; published background is cited rather than expanded. These are measures of exposition length, not difficulty or importance. [Source selections and counts](evidence/proof-lengths.json).

<a id="notation"></a>
## Notation and scope

| Notation | Meaning |
|---|---|
| C; C5 | Fixed Classicism; C + ☐ND. |
| e; t; et; tt | Individuals; propositions; unary properties of individuals; unary properties of propositions. The fixed grammar admits no individual-valued function types. |
| ☐; ◇ | Necessarily; possibly. |
| ND; BF; BC | Necessity of Distinctness; Barcan; Boolean Completeness. |
| FC; RC; TC | Functional, Relational and Transversal Choice. Rigid Comprehension is written out. |
| TR; RP; WRP | Tame Rigidity; Rigid Power; Weakly Rigid Power. |
| Max; SP; Σ | Maximalism; Strong Possibility; the specified nonlogical signature. Eligibility depends on the stated reference theory. |
| PR | Profile Realization, a research proposal distinct from the database’s Actual Profile principle. |

Axiom of Infinity is distinct from the Infinity schema. Quantification over properties ranges over those admitted by the model; the fullness result explicitly asks for more. The original C remains finitary.
