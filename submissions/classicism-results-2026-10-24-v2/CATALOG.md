# Detailed result catalog

All 185 stable keys, including the original 160, are retained. Keys may group several claims. Exact aliases resolve to MAIN-RESULTS.json; linked aggregate keys retain narrower evidence boundaries. Supporting module metadata remains in [CATALOG.json](CATALOG.json).

[Main guide](MAIN-RESULTS.md) · [Questions](CONJECTURES.md) · [Integration review](DATABASE-INTEGRATION.md)

| Part | Sections |
|---|---|
| [I. Resolved database questions and connections](evidence/RESULT-INDEX.md#database-connections) | [Maximalism and Strong Possibility](evidence/RESULT-INDEX.md#maximalism-and-possibility); [Choice and rigidity](evidence/RESULT-INDEX.md#choice-and-rigidity); [Infinity](evidence/RESULT-INDEX.md#infinity-connections); [Continuum Hypothesis and forcing](evidence/RESULT-INDEX.md#continuum-hypothesis-and-forcing); [Previously known results formalized](evidence/RESULT-INDEX.md#previously-known-results-formalized). |
| [II. Further results about established principles](evidence/RESULT-INDEX.md#established-principles) | [Choice and completeness](evidence/RESULT-INDEX.md#choice-and-completeness); [Arithmetic and analysis](evidence/RESULT-INDEX.md#arithmetic-and-evaluation); [Strong Possibility and language](evidence/RESULT-INDEX.md#possibility-and-language); [Model theory and computational complexity](evidence/RESULT-INDEX.md#model-theory-and-computational-complexity). |
| [III. Extensions and new directions](evidence/RESULT-INDEX.md#extensions-and-new-directions) | [Abstraction and infinitary extensions](evidence/RESULT-INDEX.md#abstraction-and-infinitary-extensions); [Evaluation and separating operators](evidence/RESULT-INDEX.md#operators-and-evaluation); [Logical observers](evidence/RESULT-INDEX.md#h-observer-separation); [Worlds, profiles and probability](evidence/RESULT-INDEX.md#worlds-and-probability). |

<a id="choice.01"></a>
## choice.01

FC iff Actuality + pointwise sections of actual surjections. The mirrored type-fragment reduction is included. (`functional-choice-by-sections.md`)

**Lean certified:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions).

**Proofs:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md)

**Scoped evidence:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions)

<a id="choice.02"></a>
## choice.02

Boxed FC iff boxed Actuality + strong sections; fully boxed ordinary-section formulation included.

**Proofs:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md)

**Scoped evidence:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions)

<a id="choice.03"></a>
## choice.03

Plenitude iff Actuality + pointwise retractions of actual injections. (same; `choice-uniformization.md`)

**Lean certified:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions).

**Proofs:** [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md)

**Scoped evidence:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions)

<a id="choice.04"></a>
## choice.04

C5 iff persistence of actual injectivity iff strong retractions of actual injections. (`choice-uniformization.md`)

**Lean certified:** The C5 forward rules for persistent injectivity and strong retractions at all admitted relational types, the low-type converses to ☐ND (type t), and the per-map necessary-injectivity/strong-retraction equivalence.

**Exact reconciliation scope:** StrongLeftSplitting(A,B): forall f:A→B, actual Inj(f) implies exists g:B→A, box forall a, g(f a)=a. Ordinary pointwise retractions are weaker and must not receive this C5 equivalence. c5_injectivity_persists.rule covers arbitrary admitted A (including e) and relational B. Strong retractions restrict A to relational because g must return A. c5_strong_retractions.listRule ranges over finite argument lists, including the empty list, so its relational source is not restricted to unary types; B is arbitrary closed relational. The separate _t declaration also states the nullary source explicitly. The converses conclude boxed ND_t; the existing all-type collapse of boxed ND_t supplies C5. The fixed low-type tests are sufficient, not the total scope of the forward theorem. Per-map necessary injectivity iff existence of a strong retraction is separately checked. No choice, Atomicity or Actuality premise is introduced.

**Scope assessment:** [integration-scope-reconciliation.json](evidence/integration-scope-reconciliation.json)

**Proofs:** [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md)

**Scoped evidence:** [`C5-STRONG-RETRACTIONS`](evidence/RESULT-INDEX.md#c5-strong-retractions)

**Integration assessment:** [injectivity-persistence](DATABASE-INTEGRATION.md#choice.04--injectivity-persistence) · [per-map-necessary-injectivity](DATABASE-INTEGRATION.md#choice.04--per-map-necessary-injectivity) · [strong-left-splitting](DATABASE-INTEGRATION.md#choice.04--strong-left-splitting)

<a id="choice.05"></a>
## choice.05

BF_rel persistence/splitting calculus: persistence of surjectivity, idempotence or involutivity characterizes BF_rel; strong sections iff ordinary sections + BF_rel. These related law formulations are one family. (`functional-choice-by-sections.md`; `reversible-comprehension-and-algebraic-laws.md`)

**Lean certified:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions).

**Proofs:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md) · [reversible-comprehension-and-algebraic-laws.md](source/research/2026-10-22/notes/reversible-comprehension-and-algebraic-laws.md)

**Scoped evidence:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions)

<a id="choice.06"></a>
## choice.06

Per-map categorical/strong-splitting classification: Epi(f) iff necessary surjectivity; strong left invertibility iff necessary injectivity, at the stated relational types. (`choice-uniformization.md`)

**Lean certified:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions).

**Proofs:** [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md)

**Scoped evidence:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions)

<a id="choice.07"></a>
## choice.07

Plenitude iff representation of all total symmetric single-valued graphs (involution representation). (`reversible-comprehension-and-algebraic-laws.md`)

**Lean certified:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions).

**Proofs:** [reversible-comprehension-and-algebraic-laws.md](source/research/2026-10-22/notes/reversible-comprehension-and-algebraic-laws.md)

**Scoped evidence:** [`SECTIONS-RETRACTIONS`](evidence/RESULT-INDEX.md#sections-retractions)

<a id="choice.08"></a>
## choice.08

The six evaluator equivalences, as one hierarchy: Actuality truth-fiber, ordinary BE, globally bivalent evaluator, unique ordinary BE, necessary local BE, fixed necessarily correct BE. The adjacent separations are recorded separately. (`actual-truth-evaluator-ladder.md`)

**Lean certified:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores): Actuality-core conversion and admitted-value lemmas.

**Proofs:** [actual-truth-evaluator-ladder.md](source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.09"></a>
## choice.09

GC canonical evaluator/extensionalization theorem: unique globally bivalent evaluator, selected-world normal form, unique TwoVal representatives, idempotent Boolean normalization and pullback naturality. Grouped rather than counting each operator law. (`gallin-bivalent-evaluator.md`)

**Lean certified:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores): Actuality-core conversion and admitted-value lemmas.

**Proofs:** [gallin-bivalent-evaluator.md](source/research/2026-10-22/notes/gallin-bivalent-evaluator.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.10"></a>
## choice.10

GC quantifier-law family: current-predicate commutation, safe boxed absorption, and exact selected-world-relative-BF characterization of the stronger law. The unrestricted stronger law is not proved.

**Lean certified:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores): Actuality-core conversion and admitted-value lemmas.

**Proofs:** [gallin-bivalent-evaluator.md](source/research/2026-10-22/notes/gallin-bivalent-evaluator.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.11"></a>
## choice.11

Ordinary BE plus modal commutation forces Extensionality (and converse).

**Lean certified.**

**Exact reconciliation scope:** ActualEvaluator(E): forall p, (p implies E p=top) and (not p implies E p=bottom). Commutation is the unboxed pointwise identity forall p, E(box p)=box(E p), or its diamond counterpart. Full Extensionality is the schema at every closed relational type, including t; the certificate transports to every signature and any axiom set. No Gallin comprehension, Choice, Infinity or BF hypothesis.

**Scope assessment:** [integration-scope-reconciliation.json](evidence/integration-scope-reconciliation.json)

**Proofs:** [gallin-bivalent-evaluator.md](source/research/2026-10-22/notes/gallin-bivalent-evaluator.md)

**Scoped evidence:** [`EVALUATOR-MODAL-COMMUTATION`](evidence/RESULT-INDEX.md#evaluator-modal-commutation)

**Integration assessment:** [box-commutation](DATABASE-INTEGRATION.md#choice.11--box-commutation) · [diamond-commutation](DATABASE-INTEGRATION.md#choice.11--diamond-commutation)

<a id="choice.12"></a>
## choice.12

Actuality iff localized extensionality; the supported current extensional relational Henkin HOL interpretation over all current individuals. (`actuality-world-slice-core.md`)

**Lean certified:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores): Actuality-core conversion and admitted-value lemmas.

**Proofs:** [actuality-world-slice-core.md](source/research/2026-10-22/notes/actuality-world-slice-core.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.13"></a>
## choice.13

Ambient Relational Choice transfers to ordinary Choice in the local core; GC-core version included as the same transfer family. (`actuality-world-slice-core.md`; `gallin-extensional-core.md`)

**Evidence:** [actuality-slice](DATABASE-INTEGRATION.md#choice.13--actuality-slice) · [gallin-core](DATABASE-INTEGRATION.md#choice.13--gallin-core).

**Proofs:** [actuality-world-slice-core.md](source/research/2026-10-22/notes/actuality-world-slice-core.md) · [gallin-extensional-core.md](source/research/2026-10-22/notes/gallin-extensional-core.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.14"></a>
## choice.14

Exact quantified Infinity transfer to the local/GC cores for the stated original base sort. Two constructions, one transfer family. (same two files)

**Evidence:** [actuality-slice](DATABASE-INTEGRATION.md#choice.14--actuality-slice) · [gallin-core](DATABASE-INTEGRATION.md#choice.14--gallin-core).

**Proofs:** [actuality-world-slice-core.md](source/research/2026-10-22/notes/actuality-world-slice-core.md) · [gallin-extensional-core.md](source/research/2026-10-22/notes/gallin-extensional-core.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.15"></a>
## choice.15

Complete atomic local intervals and their unique supported projection representatives; existing-join preservation included. (`actuality-world-slice-core.md`, §§7–8)

**Evidence:** [existing-join-projection](DATABASE-INTEGRATION.md#choice.15--existing-join-projection) · [local-interval](DATABASE-INTEGRATION.md#choice.15--local-interval).

**Proofs:** [actuality-world-slice-core.md](source/research/2026-10-22/notes/actuality-world-slice-core.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.16"></a>
## choice.16

Globally TwoVal GC core and its canonical isomorphism with the Actuality slice as current structures. (`gallin-extensional-core.md`)

**Lean certified:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores): Actuality-core conversion and admitted-value lemmas.

**Proofs:** [gallin-extensional-core.md](source/research/2026-10-22/notes/gallin-extensional-core.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.17"></a>
## choice.17

Exact preservation of represented individual relations, well-orders, cardinal comparisons and induction under the local projection, with extensional relation equality. (`actuality-world-slice-core.md`, §8)

**Evidence:** [induction](DATABASE-INTEGRATION.md#choice.17--induction) · [relations](DATABASE-INTEGRATION.md#choice.17--relations) · [wellorders-cardinals](DATABASE-INTEGRATION.md#choice.17--wellorders-cardinals).

**Proofs:** [actuality-world-slice-core.md](source/research/2026-10-22/notes/actuality-world-slice-core.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.18"></a>
## choice.18

Faithful probability iff internally countable atomic worlds iff internal ccc; existence of a countably additive replacement. (`faithful-probability-countable-worlds.md`)

**Lean certified:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability): Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.

**Proofs:** [faithful-probability-countable-worlds.md](source/research/2026-10-22/notes/faithful-probability-countable-worlds.md)

**Scoped evidence:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability)

<a id="choice.19"></a>
## choice.19

Probability type classification and ceiling: atom-product criterion, et/all finite individual arities, tt iff finite worlds, and all-type incompatibility with quantified Infinity_e. Grouped as ONE classification. (same, §§7–8)

**Lean certified:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability): Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.

**Proofs:** [faithful-probability-countable-worlds.md](source/research/2026-10-22/notes/faithful-probability-countable-worlds.md)

**Scoped evidence:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability)

<a id="choice.20"></a>
## choice.20

Faithful probability versus full N-profile realization: incompatibility, despite compatibility with every finite binary pattern. (same, §5)

**Evidence:** [finite-pattern-compatibility](DATABASE-INTEGRATION.md#choice.20--finite-pattern-compatibility) · [full-profile-incompatibility](DATABASE-INTEGRATION.md#choice.20--full-profile-incompatibility).

**Proofs:** [faithful-probability-countable-worlds.md](source/research/2026-10-22/notes/faithful-probability-countable-worlds.md)

<a id="choice.21"></a>
## choice.21

Permutation-invariant faithful probability iff internally finitely many worlds, with unique uniform state. (`probability-and-world-symmetry.md`)

**Evidence:** [invariant-state](DATABASE-INTEGRATION.md#choice.21--invariant-state).

**Proofs:** [probability-and-world-symmetry.md](source/research/2026-10-22/notes/probability-and-world-symmetry.md)

<a id="choice.22"></a>
## choice.22

Finite-parameter pure-term definability of faithful probability forces finite worlds, with the precise parameter/output-core restrictions.

**Evidence:** [finite-parameter-term](DATABASE-INTEGRATION.md#choice.22--finite-parameter-term).

**Proofs:** [probability-and-world-symmetry.md](source/research/2026-10-22/notes/probability-and-world-symmetry.md)

<a id="choice.23"></a>
## choice.23

Strict six-level evaluator hierarchy: five adjacent nonimplications, realized by the chain, double-retract, retract, atom-plus-atomless, and involution-group models. (`actual-truth-evaluator-ladder.md`)

**Lean certified:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores): Actuality-core conversion and admitted-value lemmas.

**Proofs:** [actual-truth-evaluator-ladder.md](source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="choice.24"></a>
## choice.24

Independence of the two section-decomposition conjuncts and the strong/modal scopes: four stated witness configurations. Existing chain/retract constructions overlap item 23, but the additional splitting verdicts are different claims. (`functional-choice-by-sections.md`, §5)

**Evidence:** [actuality-not-necessary-actuality](DATABASE-INTEGRATION.md#choice.24--actuality-not-necessary-actuality) · [actuality-without-sections](DATABASE-INTEGRATION.md#choice.24--actuality-without-sections) · [ordinary-not-strong](DATABASE-INTEGRATION.md#choice.24--ordinary-not-strong) · [sections-without-actuality](DATABASE-INTEGRATION.md#choice.24--sections-without-actuality).

**Proofs:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md)

<a id="choice.25"></a>
## choice.25

Probability model calibration: full (E,W)=(N,N), (N,P(N)), (P(N),N) separates propositional probability and individual-state probability while retaining C + ☐Functional Choice and the stated Infinity assumptions. (`faithful-probability-countable-worlds.md`)

**Evidence:** [countable-both](DATABASE-INTEGRATION.md#choice.25--countable-both) · [uncountable-individuals](DATABASE-INTEGRATION.md#choice.25--uncountable-individuals) · [uncountable-worlds](DATABASE-INTEGRATION.md#choice.25--uncountable-worlds).

**Proofs:** [faithful-probability-countable-worlds.md](source/research/2026-10-22/notes/faithful-probability-countable-worlds.md)

<a id="choice.26"></a>
## choice.26

Finite torsor models plus Henkin compactness give endomorphism splitting + necessary all-type Infinity SCHEMA without ND. This is a RELATIVE CONSISTENCY construction, not a quantified-Infinity model claim. (`endomorphism-splitting-infinity-separator.md`)

**Evidence:** [compactness-schema](DATABASE-INTEGRATION.md#choice.26--compactness-schema) · [finite-approximations](DATABASE-INTEGRATION.md#choice.26--finite-approximations).

**Proofs:** [endomorphism-splitting-infinity-separator.md](source/research/2026-10-22/notes/endomorphism-splitting-infinity-separator.md)

<a id="rigidity.01"></a>
## rigidity.01

**Nullary rigidity.** Weak rigidity and rigidity of a proposition both mean bottom or top; the corresponding nullary rigidity principles are C-theorems. Route: `maximalism-modal.md` §15.

**Evidence:** [nullary-characterization](DATABASE-INTEGRATION.md#rigidity.01--nullary-characterization) · [nullary-laws](DATABASE-INTEGRATION.md#rigidity.01--nullary-laws).

**Lean certified:** Nullary proof bodies establish WeakRigid(p) iff top/bottom iff Rigid(p), with the stated nullary TR/RP/WRP/Rigid Rigidity/Weakly Rigid Weak Rigidity/RC/WeakRC theorems and indicated necessary versions. No internally finite-power theorem is inferred.

**Proofs:** [maximalism-modal.md](source/research/2026-10-22/notes/maximalism-modal.md)

<a id="rigidity.02"></a>
## rigidity.02

**Atomicity plus rigid comprehension.** Atomicity + Rigid Comprehension implies Weakly Rigid Power. Route: `maximalism-modal.md` §16.

**Lean certified:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications).

**Proofs:** [maximalism-modal.md](source/research/2026-10-22/notes/maximalism-modal.md)

**Scoped evidence:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications)

<a id="rigidity.03"></a>
## rigidity.03

**One-property-type descent.** TR, RP, WRP, Rigid Comprehension, Weak Rigid Comprehension and IC each descend one property type. Routes: `maximalism-modal.md` §17; `nd-inextensible-comprehension-implies-weak-power.md` §5.

**Evidence:** [ic](DATABASE-INTEGRATION.md#rigidity.03--ic) · [rc](DATABASE-INTEGRATION.md#rigidity.03--rc) · [rp](DATABASE-INTEGRATION.md#rigidity.03--rp) · [tr](DATABASE-INTEGRATION.md#rigidity.03--tr) · [weak-rc](DATABASE-INTEGRATION.md#rigidity.03--weak-rc) · [wrp](DATABASE-INTEGRATION.md#rigidity.03--wrp).

**Proofs:** [maximalism-modal.md](source/research/2026-10-22/notes/maximalism-modal.md) · [nd-inextensible-comprehension-implies-weak-power.md](source/research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md)

<a id="rigidity.04"></a>
## rigidity.04

**Singleton reconstruction.** Weak rigidity is reconstruction as the join of current tuple haecceities; rigidity is the necessary version. Route: `rigidity-by-joins-and-boolean-closure.md` §1.

**Evidence:** [necessary](DATABASE-INTEGRATION.md#rigidity.04--necessary) · [weak](DATABASE-INTEGRATION.md#rigidity.04--weak).

**Lean certified:** Singleton reconstruction and its necessary counterpart, with explicit finite-tuple certificate requests for both.

**Proofs:** [rigidity-by-joins-and-boolean-closure.md](source/research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md)

<a id="rigidity.05"></a>
## rigidity.05

**Existing joins and TR.** Existing represented joins preserve weak rigidity; TR is exactly closure of rigid relations under those joins. Route: the same file §2.

**Evidence:** [tr-join-characterization](DATABASE-INTEGRATION.md#rigidity.05--tr-join-characterization) · [weak-existing-joins](DATABASE-INTEGRATION.md#rigidity.05--weak-existing-joins).

**Lean certified:** Existing represented joins preserve weak rigidity; Tame Rigidity iff rigid-join closure, without optional completeness or a rigid indexing family.

**Proofs:** [rigidity-by-joins-and-boolean-closure.md](source/research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md)

<a id="rigidity.06"></a>
## rigidity.06

**ND equivalence package.** ND is characterized by intersection/difference closure, pointwise bivalence, and section closure of rigid or weakly rigid relations. Route: `rigid-boolean-closure.md` §§2–3,6–7.

**Evidence:** [finite-boolean](DATABASE-INTEGRATION.md#rigidity.06--finite-boolean) · [membership-bivalence](DATABASE-INTEGRATION.md#rigidity.06--membership-bivalence) · [sections](DATABASE-INTEGRATION.md#rigidity.06--sections).

**Lean certified:** The intersection, difference, symmetric-difference and membership-bivalence characterizations at weak and rigid levels.

**Proofs:** [rigid-boolean-closure.md](source/research/2026-10-22/notes/rigid-boolean-closure.md)

<a id="rigidity.07"></a>
## rigidity.07

**Complement closure.** Ambient complement closure has the exact typewise BF qualification and characterizes C5 at schema level. Route: the same file §§4,6.

**Evidence:** [c5-schema](DATABASE-INTEGRATION.md#rigidity.07--c5-schema) · [rigid](DATABASE-INTEGRATION.md#rigidity.07--rigid) · [weak](DATABASE-INTEGRATION.md#rigidity.07--weak).

**Lean certified:** Exact weak ND+BF versus rigid ND+boxed-BF complement characterizations, tt/C5 equivalence, and all-type C5 consequences with tuple laws.

**Proofs:** [rigid-boolean-closure.md](source/research/2026-10-22/notes/rigid-boolean-closure.md)

<a id="rigidity.08"></a>
## rigidity.08

**The bounded propagation gap.** WRP has an exact decomposition through TR, RP and bounded future tameness; ND supplies the missing condition, yielding ND+TR+RP⇒WRP. Route: `maximalism-modal.md` §§18–19.

**Lean certified:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications).

**Proofs:** [maximalism-modal.md](source/research/2026-10-22/notes/maximalism-modal.md)

**Scoped evidence:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications)

<a id="rigidity.09"></a>
## rigidity.09

**Inextensible comprehension supplies weak power.** ND_t + IC_(τt) ⇒ WRP_τ, including TR and RP consequences. This includes the earlier ND + Rigid Comprehension consequence. Route: `nd-inextensible-comprehension-implies-weak-power.md`.

**Evidence:** [all-type-record](DATABASE-INTEGRATION.md#rigidity.09--all-type-record) · [nd-t-inextensible-weak-power](DATABASE-INTEGRATION.md#rigidity.09--nd-t-inextensible-weak-power).

**Proofs:** [nd-inextensible-comprehension-implies-weak-power.md](source/research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md)

<a id="rigidity.10"></a>
## rigidity.10

**The exact boundary over ND+BC.** IC, Rigid Comprehension, TR and WRP are equivalent additional assumptions over ND+BC. Routes: the preceding file, final section; `old-new-boolean-completeness-and-rigidity-separation.md`.

**Lean certified:** [`RIGIDITY-ND-BC`](evidence/RESULT-INDEX.md#rigidity-nd-bc).

**Proofs:** [old-new-boolean-completeness-and-rigidity-separation.md](source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md)

**Scoped evidence:** [`RIGIDITY-ND-BC`](evidence/RESULT-INDEX.md#rigidity-nd-bc)

<a id="rigidity.11"></a>
## rigidity.11

**Uniform rigidification.** Uniform weak/rigid comprehension is exactly the ND strengthening of the corresponding comprehension schema. Route: `rigidity-by-joins-and-boolean-closure.md` §6.

**Lean certified:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications).

**Proofs:** [rigidity-by-joins-and-boolean-closure.md](source/research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md)

**Scoped evidence:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications)

<a id="rigidity.12"></a>
## rigidity.12

**Algebra of the weak and rigid fragments.** These fragments have the stated complete Boolean interval representation; uniform rigidification supplies a complete Boolean retraction. Route: the same file §§5–6. This concerns the rigidity fragments; the Actuality/Gallin interpretation has its own hypotheses.

**Lean certified:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications).

**Proofs:** [rigidity-by-joins-and-boolean-closure.md](source/research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md)

**Scoped evidence:** [`RIGIDITY-CLASSIFICATIONS`](evidence/RESULT-INDEX.md#rigidity-classifications)

<a id="rigidity.13"></a>
## rigidity.13

**Strong Leibniz propagation.** Strong Leibniz + Rigid Comprehension implies necessary Strong Leibniz and necessary relational BF, including the sharper typed dependencies. Routes: `../strong-leibniz-rigid-bottom-cut.md`; `audit-rigid-bottom-cut.md`.

**Lean certified:** [`MODAL-PROPAGATION`](evidence/RESULT-INDEX.md#modal-propagation).

**Proofs:** [strong-leibniz-rigid-bottom-cut.md](source/research/2026-10-22/strong-leibniz-rigid-bottom-cut.md) · [audit-rigid-bottom-cut.md](source/research/2026-10-22/notes/audit-rigid-bottom-cut.md)

**Scoped evidence:** [`MODAL-PROPAGATION`](evidence/RESULT-INDEX.md#modal-propagation)

<a id="rigidity.14"></a>
## rigidity.14

**Finite rigid representatives.** Every internally finite property has a unique rigid coextension in bare C. Route: `quotient-abstraction-lane.md` §13.1.

**Evidence:** [internally-finite-rigid-representatives](DATABASE-INTEGRATION.md#rigidity.14--internally-finite-rigid-representatives).

**Proofs:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="rigidity.15"></a>
## rigidity.15

**Functional-graph Bourbaki–Witt.** Bare-C fixed-point theorem for represented progressive functional graphs on genuinely antisymmetric chain-complete orders. Routes: `audit-bare-c-bourbaki-witt.md`; `quotient-abstraction-lane.md` §14.

**Evidence:** [functional-graph-fixed-point](DATABASE-INTEGRATION.md#rigidity.15--functional-graph-fixed-point).

**Proofs:** [audit-bare-c-bourbaki-witt.md](source/research/2026-10-22/notes/audit-bare-c-bourbaki-witt.md) · [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="rigidity.16"></a>
## rigidity.16

**The transversal theorem.** Point-output Relational Choice plus represented well-ordered Boolean-chain joins implies Transversal Choice. Includes RC+BC⇒TC and its sharper choice-instance refinement as one theorem. Routes: `relational-choice-boolean-completeness-transversal-proof.md`; `rc-guarded-progressive-operation.md`.

**Lean certified:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness): RC + BC ⇒ TC; the sharp Actuality theorem, Actuality-based TC, and the same-type RC + BC and CBC + CCC consequences.

**Exact reconciliation scope:** For any admitted type sigma, including e: unboxed RC_(sigma t,sigma t) + BC_(sigma t) => TC_sigma. Actual equivalence relations; no Actuality, BC_tt, ND, BF, or Plenitude premise. All shallow theorem, relational-type, and object-language translation checks passed; gate reports C-minus. For admitted sigma,kappa: unboxed RC_(sigma t,sigma t) + CBC_(kappa,sigma t) + BooleanCCC_(kappa,sigma t) => TC_sigma. CBC and CCC use represented Frege-label countability, not external countability. This retains property-output RC, not the sharper point-output premise. For admitted counting type kappa and relational type tau: unboxed RC_(tau,tau) + CBC_(kappa,tau) + BooleanCCC_(kappa,tau) => BC_tau. Generic Rel/Order/Pointwise interfaces implement the relational type system. A represented progressive, total, single-valued graph on a represented antisymmetric poset has a fixed point whenever its represented canonical union has the supplied DomainLUB. This is certified support for one-supremum/chain refinements, not a certificate for every resulting choice theorem. Unboxed RC_(t,t) + BC_tt => Actuality. For any admitted sigma: unboxed RC_(t,t) + BC_tt + RC_(sigma t,sigma) => TC_sigma. This uses Actuality and Transversal; it is not the direct RC_(sigma t,sigma)+BC_(sigma t) theorem.

**Scope assessment:** [direct-transversal-lean-coverage.json](evidence/direct-transversal-lean-coverage.json)

**Proofs:** [relational-choice-boolean-completeness-transversal-proof.md](source/research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md) · [rc-guarded-progressive-operation.md](source/research/2026-10-22/notes/rc-guarded-progressive-operation.md)

**Scoped evidence:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness)

<a id="rigidity.17"></a>
## rigidity.17

**Chain-completeness upgrade.** Under the matching RC instance, well-ordered-chain completeness, chain completeness and BC are equivalent. Route: `quotient-abstraction-lane.md` §15.

**Evidence:** [chain-completeness](DATABASE-INTEGRATION.md#rigidity.17--chain-completeness).

**Proofs:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="rigidity.18"></a>
## rigidity.18

**Directed completeness.** Directed Boolean completeness is equivalent to BC in bare C. Route: the same file §15.1.

**Evidence:** [directed-completeness](DATABASE-INTEGRATION.md#rigidity.18--directed-completeness).

**Proofs:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="rigidity.19"></a>
## rigidity.19

**Countable-completeness upgrade.** Matching RC+CBC+CCC implies BC, with the sharpened point-choice transversal consequence. Route: `relational-choice-countable-completeness-ccc.md`.

**Lean certified:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness): RC + BC ⇒ TC; the sharp Actuality theorem, Actuality-based TC, and the same-type RC + BC and CBC + CCC consequences.

**Proofs:** [relational-choice-countable-completeness-ccc.md](source/research/2026-10-22/notes/relational-choice-countable-completeness-ccc.md)

**Scoped evidence:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness)

<a id="rigidity.20"></a>
## rigidity.20

**Countable complete Boolean types.** An internally countable, countably complete Boolean type is internally finite, without Choice or an Infinity premise. Route: `quotient-abstraction-lane.md` §21.

**Proofs:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

**Scoped evidence:** [`COUNTABLE-BOOLEAN-FINITENESS`](evidence/RESULT-INDEX.md#countable-boolean-finiteness)

<a id="rigidity.21"></a>
## rigidity.21

**Finite-index CCC.** Finite-index CCC forces internal finiteness of the Boolean type without a completeness premise. Route: `finite-index-countable-chain-condition.md`.

**Evidence:** [finite-index-ccc](DATABASE-INTEGRATION.md#rigidity.21--finite-index-ccc).

**Proofs:** [finite-index-countable-chain-condition.md](source/research/2026-10-22/notes/finite-index-countable-chain-condition.md)

<a id="rigidity.22"></a>
## rigidity.22

**Dense-basis completeness.** Completeness for subfamilies of an admitted order-dense family implies BC; in particular a countable dense basis plus CBC suffices. Route: `maximalism-modal.md` §21.

**Evidence:** [countable-dense-basis](DATABASE-INTEGRATION.md#rigidity.22--countable-dense-basis) · [dense-subfamily-completeness](DATABASE-INTEGRATION.md#rigidity.22--dense-subfamily-completeness).

**Proofs:** [maximalism-modal.md](source/research/2026-10-22/notes/maximalism-modal.md)

<a id="rigidity.23"></a>
## rigidity.23

**Quotient-respecting relational choice.** Transversal Choice is equivalent, as an all-type schema, to Relational Choice respecting input equivalence classes. Route: `quotient-abstraction-lane.md` §20.

**Evidence:** [quotient-respecting-choice](DATABASE-INTEGRATION.md#rigidity.23--quotient-respecting-choice).

**Proofs:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="rigidity.24"></a>
## rigidity.24

**Finite cells and finite exceptional covers.** RC supplies transversals when all cells are internally finite, and more generally when the infinite cells have an internally finite represented cover. The finite-cell case is subsumed. Route: the same file §§13.2,17.3.

**Evidence:** [finite-cells](DATABASE-INTEGRATION.md#rigidity.24--finite-cells) · [finite-exceptional-cover](DATABASE-INTEGRATION.md#rigidity.24--finite-exceptional-cover).

**Proofs:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="rigidity.25"></a>
## rigidity.25

**Class-coding routes.** Represented well-ordered class covers give transversals without Choice; represented identity-valued class labels give them with the matching RC instance. Route: the same file §17.1.

**Evidence:** [identity-labels](DATABASE-INTEGRATION.md#rigidity.25--identity-labels) · [wellordered-cover](DATABASE-INTEGRATION.md#rigidity.25--wellordered-cover).

**Proofs:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="rigidity.26"></a>
## rigidity.26

**Countable-cell transversals.** ND+CBC gives unique weakly rigid representatives of countable properties; with the matching RC instance this gives transversals for countable-cell equivalence relations. Route: the same file §17.2.

**Evidence:** [countable-cell-transversals](DATABASE-INTEGRATION.md#rigidity.26--countable-cell-transversals) · [countable-representatives](DATABASE-INTEGRATION.md#rigidity.26--countable-representatives).

**Proofs:** [quotient-abstraction-lane.md](source/research/2026-10-22/notes/quotient-abstraction-lane.md)

<a id="rigidity.27"></a>
## rigidity.27

**Symmetric full-profile choice characterization.** In the specified full symmetric-profile category models, the membership-selector RC instance has an exact stabilizer/well-order characterization and implies TC. The earlier one-object no-go is subsumed. Route: `rc-symmetric-ideal-full-categories.md` §§6–7. Here RC means Relational Choice, not Intensional Choice or Inextensible Comprehension.

**Evidence:** [selector-stabilizer](DATABASE-INTEGRATION.md#rigidity.27--selector-stabilizer) · [selector-transversal](DATABASE-INTEGRATION.md#rigidity.27--selector-transversal).

**Proofs:** [rc-symmetric-ideal-full-categories.md](source/research/2026-10-22/notes/rc-symmetric-ideal-full-categories.md)

<a id="rigidity.28"></a>
## rigidity.28

**Comparable-family supremum selection.** Coextension-invariant actual-supremum selection for comparable families is equivalent to Transversal, the coextension-representative principle, not full Transversal Choice. Route: `rc-alone-fixedpoint-obstruction.md` §2.

**Evidence:** [comparable-supremum-selection](DATABASE-INTEGRATION.md#rigidity.28--comparable-supremum-selection).

**Proofs:** [rc-alone-fixedpoint-obstruction.md](source/research/2026-10-22/notes/rc-alone-fixedpoint-obstruction.md)

<a id="rigidity.29"></a>
## rigidity.29

**Shear-seed obstruction.** The specified finite-support rational shear seed cannot support the required membership selector after comprehension closure. Route: `rc-alone-shear-obstruction.md`.

**Evidence:** [shear-seed](DATABASE-INTEGRATION.md#rigidity.29--shear-seed).

**Proofs:** [rc-alone-shear-obstruction.md](source/research/2026-10-22/notes/rc-alone-shear-obstruction.md)

<a id="rigidity.30"></a>
## rigidity.30

**Linear-vector seed obstruction.** The analogous full rational-linear automorphism seed is obstructed using represented endomorphism graphs. Route: `rc-alone-vector-endomorphism-obstruction.md`.

**Evidence:** [linear-vector-seed](DATABASE-INTEGRATION.md#rigidity.30--linear-vector-seed).

**Proofs:** [rc-alone-vector-endomorphism-obstruction.md](source/research/2026-10-22/notes/rc-alone-vector-endomorphism-obstruction.md)

<a id="rigidity.31"></a>
## rigidity.31

**Corrected old/new model.** ND+full BC+¬IC_et+¬RigidComprehension_et at E, but ¬BC_et at O. Route: `old-new-boolean-completeness-and-rigidity-separation.md`.

**Lean certified:** [`OLDNEW-SEPARATION`](evidence/RESULT-INDEX.md#oldnew-separation).

**Proofs:** [old-new-boolean-completeness-and-rigidity-separation.md](source/research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md)

**Scoped evidence:** [`OLDNEW-SEPARATION`](evidence/RESULT-INDEX.md#oldnew-separation)

<a id="rigidity.32"></a>
## rigidity.32

A fixed-point entrance C-model with singleton individuals satisfies Atomicity, Boolean Completeness, Rigid Comprehension, Relational Choice, Tame Rigidity, Rigid Power and Weakly Rigid Power at every relational type, together with ☐Strong Actuality and BF (type e). It refutes ☐Tame Rigidity at type (tt)t, BF at every relational argument type, ND (type t), and Strong Leibniz Biconditionals at every relational type.

**Lean certified.**

**Proofs:** [fixed-point-entrance-cone.md](source/research/2026-10-22/notes/fixed-point-entrance-cone.md)

**Scoped evidence:** [`FIXED-POINT-ENTRANCE`](evidence/RESULT-INDEX.md#fixed-point-entrance)

**Integration assessment:** [future-failures](DATABASE-INTEGRATION.md#rigidity.32--future-failures) · [root-positive](DATABASE-INTEGRATION.md#rigidity.32--root-positive)

<a id="rigidity.33"></a>
## rigidity.33

**Colour-collapse entrance.** Full TR+boxed BF+boxed RP_et+¬WRP_et. This refutes the single-type implication, not the full-schema conjecture. Route: `colour-collapse-entrance.md`.

**Proofs:** [colour-collapse-entrance.md](source/research/2026-10-22/notes/colour-collapse-entrance.md) · [colour-collapse.md](proofs/colour-collapse.md)

**Scoped evidence:** [`COLOUR-COLLAPSE-SCOPE`](evidence/RESULT-INDEX.md#colour-collapse-scope)

<a id="rigidity.34"></a>
## rigidity.34

**Singleton symmetric-model applications.** Nine recorded construction families fail RC_(tt,t), while the old/new singleton variant satisfies □RC and □TC. Route: `rc-symmetric-singleton-applications.md`.

**Evidence:** [nine-singleton-obstructions](DATABASE-INTEGRATION.md#rigidity.34--nine-singleton-obstructions) · [old-new-singleton-positive](DATABASE-INTEGRATION.md#rigidity.34--old-new-singleton-positive).

**Proofs:** [rc-symmetric-singleton-applications.md](source/research/2026-10-22/notes/rc-symmetric-singleton-applications.md)

<a id="principles.01"></a>
## principles.01

Arithmetic-infinity equivalences, including the C5/domain-infinity boundary — `frege-infinity-20261022-1726.md` §§26–28,33.

**Lean certified:** [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations): The displayed Frege noncollapse and finiteness equivalences, number-map/Hume-class results, and C5–Actuality transfer results.

**Proofs:** [frege-infinity-20261022-1726.md](source/research/2026-10-22/notes/frege-infinity-20261022-1726.md)

**Scoped evidence:** [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations)

<a id="principles.02"></a>
## principles.02

Function-type finiteness classification and higher-type infinity propagation — `relational-coding-recursion-20261022.md` §§24,27,30.

**Lean certified:** [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations): The displayed Frege noncollapse and finiteness equivalences, number-map/Hume-class results, and C5–Actuality transfer results.

**Proofs:** [relational-coding-recursion-20261022.md](source/research/2026-10-22/notes/relational-coding-recursion-20261022.md)

**Scoped evidence:** [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations)

<a id="principles.03"></a>
## principles.03

Common ordinary first-order arithmetic of C plus numerical noncollapse, boxed Plenitude plus quantified Infinity at e and t, and full boxed Functional Choice with those infinity axioms; all-type boxed quantified Infinity preserves the same arithmetic theory. Existing source-based proof: Frege infinity §36, with the detailed comparison proof and McLarty interpretation dependency.

**Proofs:** [full-choice-arithmetic-conservativity.md](proofs/full-choice-arithmetic-conservativity.md) · [infinity-world-richness-consolidation-20261022.md](source/research/2026-10-22/notes/infinity-world-richness-consolidation-20261022.md)

**Scoped evidence:** [`ARITHMETIC-COMPARISON`](evidence/RESULT-INDEX.md#arithmetic-comparison)

<a id="principles.04"></a>
## principles.04

Exact pure-Max arithmetic theory Cn(T_arith ∪ TrueΠ₁), with the specified current graph-choice extensions. Ordinary proof in Frege infinity §37; full Lean formalization absent.

**Proofs:** [max-arithmetic-equality.md](proofs/max-arithmetic-equality.md)

**Scoped evidence:** [`MAX-ARITHMETIC-EQUALITY`](evidence/RESULT-INDEX.md#max-arithmetic-equality)

<a id="principles.05"></a>
## principles.05

Canonical successor-preserving arithmetic graphs between original counting bases — relational report §38.

**Lean certified:** [`MAX-PREDECESSOR`](evidence/RESULT-INDEX.md#max-predecessor): The no-predecessor theorem at every closed counting type; the total unique graph and Plenitude failure at e.

**Proofs:** [relational-coding-recursion-20261022.md](source/research/2026-10-22/notes/relational-coding-recursion-20261022.md)

**Scoped evidence:** [`MAX-PREDECESSOR`](evidence/RESULT-INDEX.md#max-predecessor)

<a id="principles.06"></a>
## principles.06

Max forbids predecessor operations and the displayed cross-base arithmetic operations — relational report §§34–35,38.

**Lean certified:** [`MAX-PREDECESSOR`](evidence/RESULT-INDEX.md#max-predecessor): The no-predecessor theorem at every closed counting type; the total unique graph and Plenitude failure at e.

**Proofs:** [relational-coding-recursion-20261022.md](source/research/2026-10-22/notes/relational-coding-recursion-20261022.md)

**Scoped evidence:** [`MAX-PREDECESSOR`](evidence/RESULT-INDEX.md#max-predecessor) · [`ARITHMETIC-COMPARISON`](evidence/RESULT-INDEX.md#arithmetic-comparison)

<a id="principles.07"></a>
## principles.07

Explicit guarded numerical join and increasing-chain failure under Max — Frege report §§12–18,23.

**Evidence:** [guarded-missing-join](DATABASE-INTEGRATION.md#principles.07--guarded-missing-join).

**Proofs:** [frege-infinity-20261022-1726.md](source/research/2026-10-22/notes/frege-infinity-20261022-1726.md)

<a id="principles.08"></a>
## principles.08

Pure named atoms cannot meet the arithmetic region; no pure Actuality witness under Max — `fresh-constant-profile-root-20261022.md` §15.

**Evidence:** [no-pure-actuality-witness](DATABASE-INTEGRATION.md#principles.08--no-pure-actuality-witness) · [pure-atom-arithmetic-obstruction](DATABASE-INTEGRATION.md#principles.08--pure-atom-arithmetic-obstruction).

**Proofs:** [fresh-constant-profile-root-20261022.md](source/research/2026-10-22/notes/fresh-constant-profile-root-20261022.md)

<a id="principles.09"></a>
## principles.09

Max forces an internally infinite region of failures of Actuality — same §16.

**Evidence:** [infinite-actuality-failure-region](DATABASE-INTEGRATION.md#principles.09--infinite-actuality-failure-region).

**Proofs:** [fresh-constant-profile-root-20261022.md](source/research/2026-10-22/notes/fresh-constant-profile-root-20261022.md)

<a id="principles.10"></a>
## principles.10

Pointed-completeness/finite-profile-width criteria for Max-consistent atomic cells — `profile-root-construction-20261022.md` §12; `sp-finite-profile-rank-20261022.md` §§1–3.

**Proofs:** [profile-root-construction-20261022.md](source/research/2026-10-22/notes/profile-root-construction-20261022.md) · [profile-root-construction-20261022.md](source/research/2026-10-22/sp-structural-proof-package/profile-root-construction-20261022.md) · [sp-finite-profile-rank-20261022.md](source/research/2026-10-22/notes/sp-finite-profile-rank-20261022.md)

**Scoped evidence:** [`SP-FINITE-PROFILE-RANK`](evidence/RESULT-INDEX.md#sp-finite-profile-rank)

<a id="principles.11"></a>
## principles.11

Finite stable C5-cell categoricity and explicit finite typed classification — `finite-c5-profile-cells-20261022.md` §§1–5.

**Proofs:** [finite-c5-profile-cells-20261022.md](source/research/2026-10-22/notes/finite-c5-profile-cells-20261022.md)

**Scoped evidence:** [`SP-FINITE-PROFILE-RANK`](evidence/RESULT-INDEX.md#sp-finite-profile-rank)

<a id="principles.12"></a>
## principles.12

Exact finite-signature boundary for Max consistency preservation, including the one-individual-name exception — `audit-signature-to-pure-sp-20261022.md` §§6,9.

**Proofs:** [audit-signature-to-pure-sp-20261022.md](source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

**Scoped evidence:** [`SIGNATURE-FINITE-BOUNDARY`](evidence/RESULT-INDEX.md#signature-finite-boundary)

<a id="principles.13"></a>
## principles.13

Conservative signature extension with an infinite reservoir of fresh names — same §8.

**Proofs:** [audit-signature-to-pure-sp-20261022.md](source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

**Scoped evidence:** [`SIGNATURE-INFINITE-RESERVOIR`](evidence/RESULT-INDEX.md#signature-infinite-reservoir)

<a id="principles.14"></a>
## principles.14

Σ₁-completeness of the pure identity problem and Max's fixed pure diagram — `max-degree.md` §§1–2.

**Evidence:** [fixed-max-pure-diagram](DATABASE-INTEGRATION.md#principles.14--fixed-max-pure-diagram) · [pure-identity-complexity](DATABASE-INTEGRATION.md#principles.14--pure-identity-complexity).

**Proofs:** [max-degree.md](source/research/2026-10-22/notes/max-degree.md)

**Scoped evidence:** [`COMPUTABILITY-COMPARISON`](evidence/RESULT-INDEX.md#computability-comparison)

<a id="principles.15"></a>
## principles.15

Stronger effective-axiomatization obstruction and exact oracle cone for consistent Max strengthenings — same §§3,11; `theory-space-comparison.md` §6. This counts the strengthening, not the published Max non-r.e. baseline.

**Evidence:** [hidden-language-obstruction](DATABASE-INTEGRATION.md#principles.15--hidden-language-obstruction) · [oracle-axiomatization-cone](DATABASE-INTEGRATION.md#principles.15--oracle-axiomatization-cone).

**Proofs:** [theory-space-comparison.md](source/research/2026-10-22/notes/theory-space-comparison.md)

**Scoped evidence:** [`COMPUTABILITY-COMPARISON`](evidence/RESULT-INDEX.md#computability-comparison)

<a id="principles.16"></a>
## principles.16

Robust Σ₂-completeness of Max theoremhood — `max-degree.md` §10.

**Proofs:** [max-degree.md](source/research/2026-10-22/notes/max-degree.md)

**Scoped evidence:** [`ARITHMETIC-COMPARISON`](evidence/RESULT-INDEX.md#arithmetic-comparison) · [`COMPUTABILITY-COMPARISON`](evidence/RESULT-INDEX.md#computability-comparison)

<a id="principles.17"></a>
## principles.17

Exact adequate-Max-model capacity: PA over 0′, uniform DNR equivalence, low solutions and common information — `max-degree.md` §9; `effective-refinements.md` §§3,8.

**Evidence:** [low-and-common-information](DATABASE-INTEGRATION.md#principles.17--low-and-common-information) · [model-capacity](DATABASE-INTEGRATION.md#principles.17--model-capacity) · [uniform-problem](DATABASE-INTEGRATION.md#principles.17--uniform-problem).

**Proofs:** [max-degree.md](source/research/2026-10-22/notes/max-degree.md) · [effective-refinements.md](source/research/2026-10-22/notes/effective-refinements.md)

**Scoped evidence:** [`COMPUTABILITY-COMPARISON`](evidence/RESULT-INDEX.md#computability-comparison)

<a id="principles.18"></a>
## principles.18

Positive-package Σ₁ theoremhood/ordinary-PA model capacity, including the stronger bare-code lower bound from possible weak Infinity — `positive-effective.md` §§13–17,22.

**Proofs:** [positive-effective.md](source/research/2026-10-22/notes/positive-effective.md)

**Scoped evidence:** [`ARITHMETIC-COMPARISON`](evidence/RESULT-INDEX.md#arithmetic-comparison) · [`COMPUTABILITY-COMPARISON`](evidence/RESULT-INDEX.md#computability-comparison)

<a id="principles.19"></a>
## principles.19

Standard-number code bounds: HYP lower information, sub-Kleene-O solutions, exact common information — same §§18–20. Standard-model existence hypotheses remain explicit.

**Evidence:** [below-kleene-o](DATABASE-INTEGRATION.md#principles.19--below-kleene-o) · [common-information](DATABASE-INTEGRATION.md#principles.19--common-information) · [nonhyperarithmetical-lower](DATABASE-INTEGRATION.md#principles.19--nonhyperarithmetical-lower).

**Proofs:** [positive-effective.md](source/research/2026-10-22/notes/positive-effective.md)

**Scoped evidence:** [`STANDARD-NUMBER-MODELS`](evidence/RESULT-INDEX.md#standard-number-models)

<a id="principles.20"></a>
## principles.20

Analytic complexity of standard-model finite-condition problems — same §21; `max-degree.md` §13.

**Evidence:** [analytic-finite-conditions](DATABASE-INTEGRATION.md#principles.20--analytic-finite-conditions) · [identity-fragment](DATABASE-INTEGRATION.md#principles.20--identity-fragment).

**Proofs:** [max-degree.md](source/research/2026-10-22/notes/max-degree.md)

**Scoped evidence:** [`STANDARD-NUMBER-MODELS`](evidence/RESULT-INDEX.md#standard-number-models)

<a id="principles.21"></a>
## principles.21

Effective pure-complete theories have recursive finite domain bounds and unique computably presentable actual structures — `effective-refinements.md` §§9.3–9.6.

**Evidence:** [recursive-finite-bounds](DATABASE-INTEGRATION.md#principles.21--recursive-finite-bounds) · [unique-actual-structure](DATABASE-INTEGRATION.md#principles.21--unique-actual-structure).

**Proofs:** [effective-refinements.md](source/research/2026-10-22/notes/effective-refinements.md)

**Scoped evidence:** [`COMPLETION-SPACES`](evidence/RESULT-INDEX.md#completion-spaces)

<a id="principles.22"></a>
## principles.22

Completion-space classifications: Max nowhere dense; positive isolated completions/perfect derivatives; exact effective-Borel distinctions — `theory-space-comparison.md`; `effective-refinements.md` §§2–5.

**Evidence:** [effective-borel](DATABASE-INTEGRATION.md#principles.22--effective-borel) · [max-topology](DATABASE-INTEGRATION.md#principles.22--max-topology) · [positive-isolated-perfect](DATABASE-INTEGRATION.md#principles.22--positive-isolated-perfect).

**Proofs:** [theory-space-comparison.md](source/research/2026-10-22/notes/theory-space-comparison.md) · [effective-refinements.md](source/research/2026-10-22/notes/effective-refinements.md)

**Scoped evidence:** [`COMPLETION-SPACES`](evidence/RESULT-INDEX.md#completion-spaces)

<a id="principles.23"></a>
## principles.23

Equational conservativity and idempotence of relative distinctness maximalization above Max — `theory-space-comparison.md` §9.

**Evidence:** [equational-conservativity](DATABASE-INTEGRATION.md#principles.23--equational-conservativity) · [idempotence](DATABASE-INTEGRATION.md#principles.23--idempotence).

**Proofs:** [theory-space-comparison.md](source/research/2026-10-22/notes/theory-space-comparison.md)

<a id="principles.24"></a>
## principles.24

Genuine infinitary comprehension boundary, including standardness transfer and incompatibility with original Max — `comparison-handoff-20261022.md` §7; `structural-lane-handoff.md`. This explicitly changes the object-language resources.

**Evidence:** [max-incompatibility](DATABASE-INTEGRATION.md#principles.24--max-incompatibility) · [standardness-transfer](DATABASE-INTEGRATION.md#principles.24--standardness-transfer) · [unrestricted-versus-bounded-comprehension](DATABASE-INTEGRATION.md#principles.24--unrestricted-versus-bounded-comprehension).

**Proofs:** [comparison-handoff-20261022.md](source/research/2026-10-22/notes/comparison-handoff-20261022.md) · [structural-lane-handoff.md](source/research/2026-10-22/notes/structural-lane-handoff.md)

<a id="principles.25"></a>
## principles.25

Conditional SP Σ₃-completeness and PA-over-0″ model capacity — `strong-possibility-degree.md` §§2–6.

**Proofs:** [strong-possibility-degree.md](source/research/2026-10-22/notes/strong-possibility-degree.md)

**Scoped evidence:** [`ARITHMETIC-COMPARISON`](evidence/RESULT-INDEX.md#arithmetic-comparison) · [`COMPUTABILITY-COMPARISON`](evidence/RESULT-INDEX.md#computability-comparison)

<a id="principles.26"></a>
## principles.26

SP's exact finite-profile atom decompositions — `sp-finite-profile-rank-20261022.md` §4; finite-cell notes.

**Proofs:** [sp-finite-profile-rank-20261022.md](source/research/2026-10-22/notes/sp-finite-profile-rank-20261022.md)

**Scoped evidence:** [`SP-FINITE-PROFILE-RANK`](evidence/RESULT-INDEX.md#sp-finite-profile-rank)

<a id="principles.27"></a>
## principles.27

Pure/signature SP incompatibility and exact finite individual-name bounds — `audit-signature-to-pure-sp-20261022.md` §§1–7,10.

**Lean certified:** [`SP-SIGNATURE-CONFLICT`](evidence/RESULT-INDEX.md#sp-signature-conflict): The signature-splitting lemma. [`SP-INDIVIDUAL-CARDINALITY`](evidence/RESULT-INDEX.md#sp-individual-cardinality): The conditional monism/reflection lemma.

**Proofs:** [audit-signature-to-pure-sp-20261022.md](source/research/2026-10-22/notes/audit-signature-to-pure-sp-20261022.md)

**Scoped evidence:** [`SP-SIGNATURE-CONFLICT`](evidence/RESULT-INDEX.md#sp-signature-conflict) · [`SP-INDIVIDUAL-CARDINALITY`](evidence/RESULT-INDEX.md#sp-individual-cardinality)

<a id="principles.28"></a>
## principles.28

Finite-signature atom counts via pointed isomorphism orbits/Burnside formulas — `finite-c5-signature-cells-20261022.md`.

**Proofs:** [finite-c5-signature-cells-20261022.md](source/research/2026-10-22/notes/finite-c5-signature-cells-20261022.md)

**Scoped evidence:** [`SP-FINITE-PROFILE-RANK`](evidence/RESULT-INDEX.md#sp-finite-profile-rank)

<a id="principles.29"></a>
## principles.29

Explicit all-input-type Barcan and Functionality failures under pure SP and the stated finite-signature SP hypotheses — `finite-c5-profile-cells-20261022.md` §9; `signature-sp-barcan-20261022.md`.

**Proofs:** [finite-c5-profile-cells-20261022.md](source/research/2026-10-22/notes/finite-c5-profile-cells-20261022.md) · [signature-sp-barcan-20261022.md](source/research/2026-10-22/notes/signature-sp-barcan-20261022.md)

**Scoped evidence:** [`SP-BARCAN-FUNCTIONALITY`](evidence/RESULT-INDEX.md#sp-barcan-functionality)

<a id="principles.30"></a>
## principles.30

Conditional finite possibility iterations: successive jumps and strict finite-hat consequences — `iterated-possibility-degrees.md`.

**Evidence:** [finite-hat-strictness](DATABASE-INTEGRATION.md#principles.30--finite-hat-strictness) · [finite-jump-hierarchy](DATABASE-INTEGRATION.md#principles.30--finite-jump-hierarchy).

**Proofs:** [iterated-possibility-degrees.md](source/research/2026-10-22/notes/iterated-possibility-degrees.md)

<a id="principles.31"></a>
## principles.31

Conditional omega iteration: omega-jump model capacity and theoremhood/completion complexity — `limit-possibility-degree.md`.

**Evidence:** [omega-absolute-completion-rank](DATABASE-INTEGRATION.md#principles.31--omega-absolute-completion-rank) · [omega-capacity](DATABASE-INTEGRATION.md#principles.31--omega-capacity) · [omega-theoremhood](DATABASE-INTEGRATION.md#principles.31--omega-theoremhood).

**Proofs:** [limit-possibility-degree.md](source/research/2026-10-22/notes/limit-possibility-degree.md)

<a id="principles.32"></a>
## principles.32

Pure-term-profile roots, independently prescribed atomic/atomless cells, and related finite-fragment/retract-graft variants — `profile-root-construction-20261022.md`; structural proof package. Treat the retract variants as part of this family rather than new models each time a target is changed.

**Evidence:** [profile-roots](DATABASE-INTEGRATION.md#principles.32--profile-roots) · [retract-fragments](DATABASE-INTEGRATION.md#principles.32--retract-fragments).

**Proofs:** [profile-root-construction-20261022.md](source/research/2026-10-22/notes/profile-root-construction-20261022.md) · [profile-root-construction-20261022.md](source/research/2026-10-22/sp-structural-proof-package/profile-root-construction-20261022.md)

<a id="principles.33"></a>
## principles.33

Fresh-constant/profile roots with prescribed finite atom counts, exact countability spectra, and arbitrary individual domains satisfying the stated UCP/raw-UWR conditions — `fresh-constant-profile-root-20261022.md`.

**Evidence:** [arbitrary-individual-domain](DATABASE-INTEGRATION.md#principles.33--arbitrary-individual-domain) · [countability-spectrum](DATABASE-INTEGRATION.md#principles.33--countability-spectrum) · [finite-atom-counts](DATABASE-INTEGRATION.md#principles.33--finite-atom-counts).

**Proofs:** [fresh-constant-profile-root-20261022.md](source/research/2026-10-22/notes/fresh-constant-profile-root-20261022.md)

<a id="principles.34"></a>
## principles.34

Finite-leaf coalesced model separating arithmetic infinity from possible domain infinity — Frege report §33.

**Evidence:** [finite-fan-infinity-separator](DATABASE-INTEGRATION.md#principles.34--finite-fan-infinity-separator).

**Proofs:** [frege-infinity-20261022-1726.md](source/research/2026-10-22/notes/frege-infinity-20261022-1726.md)

<a id="principles.35"></a>
## principles.35

Finite pointed-complete/coalesced structures separating finite effective completeness from C5 and functional representation — profile report §§20–26; `positive-effective.md` §23.

**Evidence:** [finite-bounds-choice](DATABASE-INTEGRATION.md#principles.35--finite-bounds-choice) · [finite-complete-cells](DATABASE-INTEGRATION.md#principles.35--finite-complete-cells) · [mixed-barcan-patterns](DATABASE-INTEGRATION.md#principles.35--mixed-barcan-patterns).

**Proofs:** [positive-effective.md](source/research/2026-10-22/notes/positive-effective.md) · [profile-root-construction-20261022.md](source/research/2026-10-22/notes/profile-root-construction-20261022.md) · [profile-root-construction-20261022.md](source/research/2026-10-22/sp-structural-proof-package/profile-root-construction-20261022.md)

<a id="sp_supplement.01"></a>
## sp_supplement.01

**Exact algebraic consistency/embedding criteria for SP.** SP equals Max plus the individually Max-consistent universal finite-Boolean-identity sentences; consistency is equivalent to the restricted existential-identity disjunction property. The normalized H-disjunction criterion and the criterion using embeddings into elementary extensions of every genuine Max model belong to this same family. This includes H-clopen embedding invariance. Routes: `notes/reflection-universal-core-20261022.md` §§2–7; `notes/sp-failed-disjunction-20261022.md` §§17,18.2. The required joint-embedding theorem and general H-clopen classification are not proved.

**Lean certified:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria): The universal-core equivalence and the stated conditional disjunction criterion.

**Proofs:** [reflection-universal-core-20261022.md](source/research/2026-10-22/notes/reflection-universal-core-20261022.md) · [reflection-universal-core-20261022.md](source/research/2026-10-22/sp-structural-proof-package/reflection-universal-core-20261022.md) · [sp-failed-disjunction-20261022.md](source/research/2026-10-22/notes/sp-failed-disjunction-20261022.md)

**Scoped evidence:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria)

<a id="sp_supplement.02"></a>
## sp_supplement.02

**Essential common-term algebra criterion.** Essentiality for the full pure term-operation signature is equivalent to the stated modal-ideal/density condition and is sufficient for a genuine Max model to satisfy SP; such an essential genuine model would fail Vicinity and Actuality. Route: `notes/sp-essential-extension-20261022.md` §§1–6,8. Exact status correction: essentiality has **not been shown necessary** for SP. There is no proved nonnecessity result and no essential genuine SP model is supplied.

**Lean certified:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria): The universal-core equivalence and the stated conditional disjunction criterion.

**Proofs:** [sp-essential-extension-20261022.md](source/research/2026-10-22/notes/sp-essential-extension-20261022.md)

**Scoped evidence:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria)

<a id="sp_supplement.03"></a>
## sp_supplement.03

**Maximal B-preserving quotients and permanent-survival criterion.** Such maximal quotients exist and are essential; correct-B-truth ultrafilters give literal identity correctness, and the resulting complete operation/truth diagram embeds in a genuine Max Henkin completion. A specified disequality survives every maximal B-preserving quotient exactly when its principal congruence already collapses distinct B-elements, with a finite polynomial-chain certificate. Routes: `notes/sp-essential-extension-20261022.md` §§4,7,9; `notes/sp-henkin-minimal-20261022.md` §§16–21; `notes/sp-failed-disjunction-20261022.md` §§15–16. This is an algebraic quotient/completion theorem, not an SP model: Henkin witnesses can still lose truth in later quotients.

**Evidence:** [main](DATABASE-INTEGRATION.md#sp_supplement.03--main) · [permanent_survival](DATABASE-INTEGRATION.md#sp_supplement.03--permanent_survival).

**Proofs:** [sp-essential-extension-20261022.md](source/research/2026-10-22/notes/sp-essential-extension-20261022.md) · [sp-henkin-minimal-20261022.md](source/research/2026-10-22/notes/sp-henkin-minimal-20261022.md) · [sp-failed-disjunction-20261022.md](source/research/2026-10-22/notes/sp-failed-disjunction-20261022.md)

<a id="sp_supplement.04"></a>
## sp_supplement.04

**Guarded old-witness extraction and finite interpolation.** Positive existential equations admit old pure-term witnesses; under the explicit guards, finite truth observations, finite direct identities/disequalities, and finite entity-valued input/output tables admit permanent old witnesses/interpolants, including avoidance of finitely many forbidden functions. Routes: `notes/sp-henkin-minimal-20261022.md` §§19–23; `notes/sp-existential-products-20261022.md` §§23–24; `notes/sp-failed-disjunction-20261022.md` §10. Arbitrary incoming higher-type operators, unbounded observations and unrestricted quantified dependence remain outside the theorem.

**Evidence:** [finite_interpolation](DATABASE-INTEGRATION.md#sp_supplement.04--finite_interpolation) · [main](DATABASE-INTEGRATION.md#sp_supplement.04--main).

**Proofs:** [sp-henkin-minimal-20261022.md](source/research/2026-10-22/notes/sp-henkin-minimal-20261022.md) · [sp-existential-products-20261022.md](source/research/2026-10-22/notes/sp-existential-products-20261022.md) · [sp-failed-disjunction-20261022.md](source/research/2026-10-22/notes/sp-failed-disjunction-20261022.md)

<a id="sp_supplement.05"></a>
## sp_supplement.05

**Product embeddings admit injective ultraproduct quotients.** Any embedding of a genuine C full-term algebra into a product has a finite-intersection family of pair-separation coordinates and therefore an injective ultraproduct quotient. For finite products an injective coordinate already exists. Route: `notes/sp-existential-products-20261022.md` §14. This concerns embeddings of full term algebras.

**Evidence:** [main](DATABASE-INTEGRATION.md#sp_supplement.05--main).

**Proofs:** [sp-existential-products-20261022.md](source/research/2026-10-22/notes/sp-existential-products-20261022.md)

<a id="sp_supplement.06"></a>
## sp_supplement.06

**Nonrigid four-proposition rigid-leaf classification.** The specified chain family L_(n,k) is classified by conjugacy classes of transitive subgroups of Sym(n−1)×Sym(k), with finite pure orbit isolators and exact BF behavior. Route: `sp-structural-proof-package/finite-rigid-leaf-galois-classification-20261022.md` §§1–10. The stable C5 cell classification and the recorded BF/Functionality equivalence are separate results.

**Evidence:** [main](DATABASE-INTEGRATION.md#sp_supplement.06--main).

**Proofs:** [finite-rigid-leaf-galois-classification-20261022.md](source/research/2026-10-22/notes/finite-rigid-leaf-galois-classification-20261022.md) · [finite-rigid-leaf-galois-classification-20261022.md](source/research/2026-10-22/sp-structural-proof-package/finite-rigid-leaf-galois-classification-20261022.md)

<a id="sp_supplement.07"></a>
## sp_supplement.07

**SP excludes strong worlds and allows atomless splitting of finite current diagrams.** SP rules out arbitrary strong worlds at every relational type, and yields the stated distinctness-preserving atomlessness possibilities preserving any fixed finite current diagram. Routes: `notes/sp-existential-products-20261022.md` §§5–6; `sp-structural-proof-package/reflection-universal-core-20261022.md` §§9–12. This does not refute weak atoms or establish SP inconsistency, and it does not say SP refutes unboxed Actuality.

**Evidence:** [finite_diagram_splitting](DATABASE-INTEGRATION.md#sp_supplement.07--finite_diagram_splitting) · [main](DATABASE-INTEGRATION.md#sp_supplement.07--main).

**Proofs:** [sp-existential-products-20261022.md](source/research/2026-10-22/notes/sp-existential-products-20261022.md) · [reflection-universal-core-20261022.md](source/research/2026-10-22/notes/reflection-universal-core-20261022.md) · [reflection-universal-core-20261022.md](source/research/2026-10-22/sp-structural-proof-package/reflection-universal-core-20261022.md)

<a id="sp_supplement.08"></a>
## sp_supplement.08

**Restricted pure persistent ghosts and finite multiplicity.** At every relational input/output type there are explicit closed-pure C-provably persistent operators nonzero under Max but with bottom entity-values on all current inputs under SP; every current operator has arbitrarily many distinct entity-coextensive operators, for each external finite bound. The contrasting closed-pure single-individual-input result is included. Route: `notes/sp-existential-products-20261022.md` §§18–20,25. The purity and persistence restrictions strengthen the unqualified BF/Functionality failure. No internally infinite sequence of such operators is claimed.

**Evidence:** [individual_boundary](DATABASE-INTEGRATION.md#sp_supplement.08--individual_boundary) · [main](DATABASE-INTEGRATION.md#sp_supplement.08--main).

**Proofs:** [sp-existential-products-20261022.md](source/research/2026-10-22/notes/sp-existential-products-20261022.md)

<a id="world_algebra.01"></a>
## world_algebra.01

**Internal world-indexed representation.** Encode/decode of arbitrary relational intensions as admitted rigid world-indexed extensions; world-times-tuple atomic normal form and internal truth lemma; the associated slicing/normalization laws. These are grouped as one representation family, with no external-fullness assertion. Route: world-representation §§3–4; root §1. This concerns internal truth-table representation. The Gallin biinterpretation and local Actuality/GC cores have separate entries.

**Lean certified:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra): The finite-profile and atomic-profile results.

**Proofs:** [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

**Scoped evidence:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra)

<a id="world_algebra.02"></a>
## world_algebra.02

**Complete subalgebras are world partitions.** Admitted internally complete Boolean subalgebras correspond to admitted equivalence relations on world atoms; the generator/separating-family criterion is included. Route: algebraic-core §1.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.02--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md)

<a id="world_algebra.03"></a>
## world_algebra.03

**Complete Boolean maps are contravariant world maps.** Complete bivalent homomorphisms are evaluations at atoms; general complete Boolean homomorphisms correspond to represented maps of atom fields, including injective/surjective and inverse-direction consequences. Route: algebraic-core §9.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.03--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md)

<a id="world_algebra.04"></a>
## world_algebra.04

**Complete normal modal operators are world relations.** Representation by admitted binary world relations, with the proved modal-law/frame correspondences, including .2/confluence and the indicated product refinements. Route: algebraic-core §§10, 17.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.04--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md)

<a id="world_algebra.05"></a>
## world_algebra.05

**Profile-map characterization and Cantor boundary.** EU is surjectivity and S injectivity of the world-to-rigid-profile map; literal pattern-cell characterization. The strongest type-boundary result is already in BARE C: unrestricted raw WR for all current profiles is impossible at every relational input type. Under T, raw WR and the rigid-profile EU formulation agree, so this supplies the EU boundary there. Do not silently identify the two outside T. Route: world-representation §5; root §§2, 4; world-cardinality-ucp-20261022.md §§12–17.

**Lean certified:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra): The finite-profile and atomic-profile results.

**Proofs:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) · [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

**Scoped evidence:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra)

<a id="world_algebra.06"></a>
## world_algebra.06

**Separate EU and S witnesses can be combined under Choice or the precise retraction hypothesis.** Boxed FC suffices; the sharper EU+S+Ret_t condition and the single generated-subalgebra retraction version are included. Route: world-representation §6; algebraic-core §23; root §§5, 13. The ordered nominal endpoint construction witnesses failure without the added hypotheses.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.06--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.07"></a>
## world_algebra.07

**Canonical configuration algebra and complete freeness.** The internally free complete atomic algebra on a represented index field exists already over T; exact profiles are characterized by unique complete-endomorphism extension of generator assignments. Coherent coordinate flips and the precise atomic-target boundary are grouped here. The exact-profile double-powerset corollary t≅P_rigid(P_rigid(e)), under BP+UWR_e, is included. Route: algebraic-core §§11, 21, 24; root §14; world-cardinality-ucp-20261022.md §22.

**Evidence:** [double_powerset](DATABASE-INTEGRATION.md#world_algebra.07--double_powerset) · [main](DATABASE-INTEGRATION.md#world_algebra.07--main).

**Proofs:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) · [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.08"></a>
## world_algebra.08

**Profile cardinal comparison and the Choice boundary.** The Choice-derived EU-or-S cardinal dichotomy, and the stronger all-represented-field comparability principle equivalent to boxed FC via typed Hartogs. Route: world-representation §§19, 21; root §18.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.08--main).

**Proofs:** [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.09"></a>
## world_algebra.09

**Complete-evaluator density exactly characterizes T.** Every nonzero proposition is true under a complete evaluator iff T; separation formulation and the weaker truth-preservation presentation give the same strength. Consequently boxed FC is evaluator density plus Relational Choice. Route: world-representation §§26–27; root §§20, 22; digest §1. The actual-truth evaluator hierarchy is a separate classification.

**Evidence:** [choice_factorization](DATABASE-INTEGRATION.md#world_algebra.09--choice_factorization) · [main](DATABASE-INTEGRATION.md#world_algebra.09--main).

**Proofs:** [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md) · [structural-digest.md](source/research/2026-10-22/notes/structural-digest.md)

<a id="world_algebra.10"></a>
## world_algebra.10

**Complete-evaluator existence has an atom-local Barcan characterization.** CE iff a persistently possible atom satisfies its specified local BF law; canonical replacement by E_w. In full action models this is existence of an epic outgoing arrow factoring through every outgoing arrow; chosen-type quantifier refinements are included. Route: world-representation §§22–24; root §§19, 21.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.10--main).

**Proofs:** [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.11"></a>
## world_algebra.11

**Exact full-action categorical criterion.** At a root, ND_t iff every outgoing arrow is split monic, BF_t iff every outgoing arrow is epic, and T/complete-evaluator density/boxed ND_t iff every outgoing arrow is invertible. These are FULL action-hierarchy semantic statements, not arbitrary-Henkin presentation criteria. Route: world-representation §28.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.11--main).

**Proofs:** [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.12"></a>
## world_algebra.12

**Complete Boolean retractions characterize full Choice.** Over T, complete retractions onto all admitted internally complete subalgebras at all relational types iff boxed FC. One canonical membership inclusion per output type suffices. Route: algebraic-core §§16, 18–19, 38; mixing §16; root §§10–11, 23. This is Boolean subalgebra splitting, distinct from ordinary surjection sections.

**Lean certified:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra): The finite-profile and atomic-profile results.

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-mixing-models.md](source/research/2026-10-22/evaluation-and-choice/structural-mixing-models.md) · [structural-mixing-models.md](source/research/2026-10-22/notes/structural-mixing-models.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

**Scoped evidence:** [`BOOLEAN-RETRACTIONS-CHOICE`](evidence/RESULT-INDEX.md#boolean-retractions-choice) · [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra)

<a id="world_algebra.13"></a>
## world_algebra.13

**Finite Boolean retractions characterize ultrafilter-valued Choice.** All-type finite retractions iff UFC; blockwise ultrafilter representation, uniform-free-ultrafilter formulation, and FC factorization via finite multiple selection plus finite retractions are grouped here. Route: algebraic-core §§20, 25, 30, 33, 38; mixing §22.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.13--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-mixing-models.md](source/research/2026-10-22/evaluation-and-choice/structural-mixing-models.md) · [structural-mixing-models.md](source/research/2026-10-22/notes/structural-mixing-models.md)

<a id="world_algebra.14"></a>
## world_algebra.14

**FineUF/BPI/filter-extension factorization.** Internal FE iff BPI iff UFC+FineUF iff ACfin+FineUF; FineUF's canonical whole-type and indexed binary Rado formulations are included. Route: algebraic-core §§26, 28, 39–41; root §§16, 26. The factors have separate independence results.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.14--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.15"></a>
## world_algebra.15

**Categorical injectivity/projectivity hierarchy.** For complete atomic algebras and complete maps: T makes every object projective; IC_all is injectivity of B_t; boxed FC is injectivity of every object. For finite Boolean maps with arbitrary Boolean sources, BPI is injectivity of complete atomic targets (the target 2 suffices for the converse). Route: algebraic-core §§34, 37; root §23.

**Evidence:** [finite_map_bpi](DATABASE-INTEGRATION.md#world_algebra.15--finite_map_bpi) · [main](DATABASE-INTEGRATION.md#world_algebra.15--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.16"></a>
## world_algebra.16

**Well-ordered preservation yields restricted ordinary Choice.** Retractions preserving internally well-ordered indexed meets select on output fields with a well-ordered separating predicate family; the EU+IC_e+Ret_t transfer to individual ultrafilters/ordinary Choice retains exactly its stated preservation and separation hypotheses. Route: mixing §§26, 28; root §23. The bare EU + IC_e implication remains unresolved.

**Evidence:** [bare_eu_ic](DATABASE-INTEGRATION.md#world_algebra.16--bare_eu_ic) · [main](DATABASE-INTEGRATION.md#world_algebra.16--main).

**Proofs:** [structural-mixing-models.md](source/research/2026-10-22/evaluation-and-choice/structural-mixing-models.md) · [structural-mixing-models.md](source/research/2026-10-22/notes/structural-mixing-models.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.17"></a>
## world_algebra.17

**Uniform complete evaluators measure world well-orderability.** UCE_t iff the atom field is internally well-orderable iff uniform complete-retraction selection; higher-type UCE gives the corresponding atom-product well-orderability and all-type UCE iff boxed FC. EU+UCE_t supplies individual-output Choice without IC. Route: algebraic-core §42; root §27.

**Evidence:** [individual_choice_corollary](DATABASE-INTEGRATION.md#world_algebra.17--individual_choice_corollary) · [main](DATABASE-INTEGRATION.md#world_algebra.17--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

**Scoped evidence:** [`UNIFORM-COMPLETE-EVALUATORS`](evidence/RESULT-INDEX.md#uniform-complete-evaluators)

<a id="world_algebra.18"></a>
## world_algebra.18

**Admitted world and individual permutations lift through all finite types.** Simultaneous logical-automorphism lifts, with the unpointed/transported-parameters qualification; pure selected-world/profile witnesses and pure individual orders/selectors are correspondingly obstructed in the specified nontrivial cases. Route: algebraic-core §§35–37; root §24.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.18--main) · [pure_witness_boundary](DATABASE-INTEGRATION.md#world_algebra.18--pure_witness_boundary).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.19"></a>
## world_algebra.19

**Extensional witnessing and typed world-indexed Choice.** Exact local-to-global existence and uniform extensional Skolem formulations of Intensional Choice; uniform extensional Choice is the corresponding typed Choice over worlds and inputs, with the stated input/output scopes. Route: mixing §§5, 20, 23. This is not the earlier Actuality+RInv decomposition and does not claim arbitrary intensional witnessing.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.19--main).

**Proofs:** [structural-mixing-models.md](source/research/2026-10-22/evaluation-and-choice/structural-mixing-models.md) · [structural-mixing-models.md](source/research/2026-10-22/notes/structural-mixing-models.md)

<a id="world_algebra.20"></a>
## world_algebra.20

**Ordered nominal hierarchy and endpoint-world variant.** Finite and even well-order-continuous Boolean retractions/BPI can coexist with failure of full Choice; separate EU and S witnesses can exist with no exact witness. The ordered atom and endpoint-world modifications are grouped, including their stated selector failures. Route: mixing §§17–19, 21; algebraic-core §§22, 31; world-representation §20.

**Evidence:** [endpoint_modification](DATABASE-INTEGRATION.md#world_algebra.20--endpoint_modification) · [main](DATABASE-INTEGRATION.md#world_algebra.20--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-mixing-models.md](source/research/2026-10-22/evaluation-and-choice/structural-mixing-models.md) · [structural-mixing-models.md](source/research/2026-10-22/notes/structural-mixing-models.md)

<a id="world_algebra.21"></a>
## world_algebra.21

**Finite-category complete-evaluator boundaries.** Proper/reverse retract and related finite-category witnesses distinguish CE existence, persistent or necessarily atomic witnesses, and CE density; even current ND plus necessary CE/Atomicity need not give T. Weak truth-preserving witnesses need not themselves preserve quantifiers as identities. Route: world-representation §§23–24, 27–28.

**Evidence:** [fixed_witness_boundary](DATABASE-INTEGRATION.md#world_algebra.21--fixed_witness_boundary) · [main](DATABASE-INTEGRATION.md#world_algebra.21--main).

**Proofs:** [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md)

<a id="world_algebra.22"></a>
## world_algebra.22

**Finite evaluation plus substantial Choice without T.** Finite-coordinate/ordered-cut examples and the fully atomless ordinary-ZFC generic Boolean Henkin construction establish finite-evaluator density/uniformity with the specified boxed Relational/Intensional Choice while Plenitude/FC/T fail. The atom-plus-atomless model has the additional displayed verdicts. Route: world-representation §§30–34; mixing §§30–31; algebraic-core §43; root §28. The infinitary forcing construction has a separate entry.

**Evidence:** [generic_boolean_model](DATABASE-INTEGRATION.md#world_algebra.22--generic_boolean_model) · [main](DATABASE-INTEGRATION.md#world_algebra.22--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-world-representation.md](source/research/2026-10-22/evaluation-and-choice/structural-world-representation.md) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) · [structural-mixing-models.md](source/research/2026-10-22/evaluation-and-choice/structural-mixing-models.md) · [structural-mixing-models.md](source/research/2026-10-22/notes/structural-mixing-models.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="world_algebra.23"></a>
## world_algebra.23

**Independence of the BPI factors.** Direct pair-flip construction gives FineUF without ACfin/UFC; the opposite UFC-without-BPI/FineUF direction uses the Howard–Tachtsis ZFA model as a literature-dependent input transferred to the typed hierarchy. The second direction retains its external literature dependency. Route: algebraic-core §§29, 32, 40.3; digest §3. Exact printed page of the cited Remark 4 was not recovered in the research notes.

**Evidence:** [literature_dependent_direction](DATABASE-INTEGRATION.md#world_algebra.23--literature_dependent_direction) · [main](DATABASE-INTEGRATION.md#world_algebra.23--main).

**Proofs:** [structural-algebraic-core.md](source/research/2026-10-22/evaluation-and-choice/structural-algebraic-core.md) · [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) · [structural-digest.md](source/research/2026-10-22/notes/structural-digest.md)

<a id="world_algebra.24"></a>
## world_algebra.24

**Numerically indexed Boolean structure has an exact world-cardinality criterion.** Over BP+quantified Infinity_κ, existence of an internally N_κ-independent family ⇔ an admitted surjection Atoms→N_κ ⇔ an N_κ-indexed nonzero partition/numerical lottery; universal countable finite-intersection compactness is exactly the negation of these conditions. Over C + ☐Functional Choice, quantified Infinity_t ⇔ existence of an N_t-independent family, and with a separately infinite counting base universal countable compactness ⇔ propositional finiteness. Full N-profile realization is strictly stronger than finite-pattern independence, with the indicated N/P(N) full models. The BP model with both infinities but no independent family is the nominal construction in §34. Routes: world-cardinality-ucp-20261022.md §§23–27, 34; infinity-world-richness-consolidation-20261022.md §6. The infinite-index hypothesis and internal finite/nonstandard-N interpretation are essential.

**Evidence:** [f_level_infinity](DATABASE-INTEGRATION.md#world_algebra.24--f_level_infinity) · [main](DATABASE-INTEGRATION.md#world_algebra.24--main) · [nominal_extra_verdict](DATABASE-INTEGRATION.md#world_algebra.24--nominal_extra_verdict).

**Exact reconciliation scope:** Over C + ☐Functional Choice, quantified Infinity_t iff N_t-independent family. With a separately infinite counting base, universal countable compactness iff propositional finiteness. Independence is for every internally finite pattern; N_kappa and finite sets can be externally nonstandard. Infinity_e cannot be silently obtained from Infinity_t or the counting bases exchanged. Without Choice do not replace atom surjection onto N by an injection N→Atoms. Full admitted N-profile realization is strictly stronger than finite-pattern independence: the indicated full N-world/P(N)-world models separate them. Universal compactness quantifies over all admitted families, not one selected coordinate system. The nominal model in §34 adds a verdict to an already counted construction; it is not a new model count.

**Scope assessment:** [integration-scope-reconciliation.json](evidence/integration-scope-reconciliation.json)

**Proofs:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) · [infinity-world-richness-consolidation-20261022.md](source/research/2026-10-22/notes/infinity-world-richness-consolidation-20261022.md)

<a id="world_algebra.25"></a>
## world_algebra.25

**Exact and arbitrarily high supported profile richness without Choice.** Explicit ordinary-ZFC nominal models have BP+both quantified infinities+UWR_e/AUCP_e but fail Functional Choice; the tagged nominal hierarchy realizes every finite supported rigid-core WR rank simultaneously while still failing FC. The finite-profile Fin(A) versus full admitted-profile Fin(A)∪Cofin(A) separation is grouped with this construction family. These are distinct from item 20's ordered endpoint construction: here full exact individual profiles DO exist, and the point is their insufficiency for Choice. Routes: world-cardinality-ucp-20261022.md §§35–36; infinity-world-richness-consolidation-20261022.md §6. The nominal support-bound classification is recorded separately.

**Lean certified:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra): The finite-profile and atomic-profile results.

**Proofs:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) · [infinity-world-richness-consolidation-20261022.md](source/research/2026-10-22/notes/infinity-world-richness-consolidation-20261022.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

**Scoped evidence:** [`PROFILE-WORLD-ALGEBRA`](evidence/RESULT-INDEX.md#profile-world-algebra)

<a id="world_algebra.26"></a>
## world_algebra.26

**Pair-individual support hierarchy, with fixed worlds.** This family has a nontrivial individual action. Here E=J×{0,1}, G=(Z/2Z)^J acts NONTRIVIALLY by independent individual-pair flips, W has TRIVIAL action, and supports contain fewer than a fixed infinite regular κ pair indices. The model has BP and a full e-free hierarchy. All-type Intensional Choice holds exactly when |W|<κ; all e-free IC instances hold for every W; Relational Choice fails for every nonempty W. For κ=ω and J=W=ω, Ret_t holds while IC_e fails. Route: structural-mixing-models.md §§2–3, 15.2. The pair-world construction has trivial individual action and is separate.

**Evidence:** [main](DATABASE-INTEGRATION.md#world_algebra.26--main) · [ret_t_boundary](DATABASE-INTEGRATION.md#world_algebra.26--ret_t_boundary).

**Proofs:** [structural-mixing-models.md](source/research/2026-10-22/evaluation-and-choice/structural-mixing-models.md) · [structural-mixing-models.md](source/research/2026-10-22/notes/structural-mixing-models.md) · [structural-representation-root.md](source/research/2026-10-22/evaluation-and-choice/structural-representation-root.md) · [structural-representation-root.md](source/research/2026-10-22/notes/structural-representation-root.md)

<a id="model_interpretation.01"></a>
## model_interpretation.01

**C5 transfer of generated algebras and natural cardinalities.** The finite-sorted impredicative-generation transfer theorem, with admitted commuting maps and its explicit inverse conditions, includes the original/core Frege-natural isomorphism at every counting type. No Actuality or Choice is required. Proofs: [generated algebras](source/research/2026-10-22/notes/c5-generated-algebra-transfer-20261022.md), §§1–6; [natural-cardinality transfer](source/research/2026-10-22/notes/audit-infinity-transfer-20261022.md), §§3–7. This concerns the rigid C5 core and is distinct from the Actuality/GC slice transfer and the arithmetic-infinity classification.

**Lean certified:** [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations): The displayed Frege noncollapse and finiteness equivalences, number-map/Hume-class results, and C5–Actuality transfer results.

**Proofs:** [c5-generated-algebra-transfer-20261022.md](source/research/2026-10-22/notes/c5-generated-algebra-transfer-20261022.md) · [audit-infinity-transfer-20261022.md](source/research/2026-10-22/notes/audit-infinity-transfer-20261022.md) · [certificate.json](evidence/certificates/generated-algebra-source/certificate.json) · [certificate.json](evidence/certificates/generated-algebra-target/certificate.json) · [certificate.json](evidence/certificates/generated-algebra-left-inverse-zero/certificate.json)

**Scoped evidence:** [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations)

<a id="model_interpretation.02"></a>
## model_interpretation.02

**Exact finite-support nominal classification.** For the specified Sym(A) hierarchy with trivial-action individuals E=N, classify all-type Intensional Choice, propositional Dedekind Infinity, Functional Choice and Relational Choice by world orbits and stabilizers. Include the four-way separating examples in this one classification family. Proof: [nominal classification](source/research/2026-10-22/notes/nominal-choice-classification-20261022.md), §§1–8. It is not a classification of all positive models.

**Evidence:** [main](DATABASE-INTEGRATION.md#model_interpretation.02--main).

**Lean certified:** Full permutation group and finite supports: propositional operational Dedekind infinity iff infinitely many global world orbits; atom-world necessary Intensional Choice at every admitted type and necessary failure of operational Dedekind infinity. Semantic metatheory; not a certificate for the full arbitrary-world Choice classification.

**Proofs:** [nominal-choice-classification-20261022.md](source/research/2026-10-22/notes/nominal-choice-classification-20261022.md) · [nominal-orbit-classification.md](proofs/nominal-orbit-classification.md) · [certificate.json](evidence/certificates/nominal-orbit-classification/certificate.json)

**Scoped evidence:** [`NOMINAL-ORBITS`](evidence/RESULT-INDEX.md#nominal-orbits)

<a id="model_interpretation.03"></a>
## model_interpretation.03

**Larger support bounds and world geometry.** Countable supports give boxed Intensional Choice and propositional Dedekind Infinity without Functional or Relational Choice. Group this construction with its regular/singular support-bound and world-stabilizer classification. Proofs: [countable supports](source/research/2026-10-22/notes/countable-support-choice-countermodel-20261022.md), §§8–9; [general bounds](source/research/2026-10-22/notes/support-bounds-world-geometry-20261022.md), §§1–5. These use ZFC metatheory. They do not subsume the pair-individual construction with a nontrivial individual action in the world/algebra count.

**Evidence:** [main](DATABASE-INTEGRATION.md#model_interpretation.03--main) · [support_cardinal_cases](DATABASE-INTEGRATION.md#model_interpretation.03--support_cardinal_cases).

**Proofs:** [countable-support-choice-countermodel-20261022.md](source/research/2026-10-22/notes/countable-support-choice-countermodel-20261022.md) · [support-bounds-world-geometry-20261022.md](source/research/2026-10-22/notes/support-bounds-world-geometry-20261022.md)

<a id="model_interpretation.04"></a>
## model_interpretation.04

**Effective Gallin representation of every positive model.** Original positive models and the specified relational Henkin presentations have explicit effective reconstructions, with exact degree preservation for the stated canonical type/operation coding. The treatment of truth and arbitrary signature constants retains its qualifications. Proofs: [representation audit](source/research/2026-10-22/notes/effective-gallin-representation-audit-20261022.md); [biinterpretation](source/research/2026-10-22/notes/gallin-biinterpretation-20261022.md). The computational content is additional to the semantic world-indexed representation.

**Evidence:** [main](DATABASE-INTEGRATION.md#model_interpretation.04--main).

**Proofs:** [effective-gallin-representation-audit-20261022.md](source/research/2026-10-22/notes/effective-gallin-representation-audit-20261022.md) · [gallin-biinterpretation-20261022.md](source/research/2026-10-22/notes/gallin-biinterpretation-20261022.md)

<a id="model_interpretation.05"></a>
## model_interpretation.05

**Exact degree realization preserving a supplied complete theory.** Every complete consistent pure theory extending C has a uniformly constructed adequate model of exactly its degree and with that exact pure theory. Group the resulting exact degree spectra and the stronger oracle needed to parametrize the entire completion space in this one family. Proofs: [exact spectra](source/research/2026-10-22/notes/exact-completion-model-spectra-20261022.md), §§3–6; [parametrization boundary](source/research/2026-10-22/notes/completion-space-parametrization-audit-20261022.md), §§1–4. This strengthens the oracle-capacity results. Conditional SP applications retain their consistency hypotheses.

**Evidence:** [exact_theory_degree](DATABASE-INTEGRATION.md#model_interpretation.05--exact_theory_degree) · [main](DATABASE-INTEGRATION.md#model_interpretation.05--main).

**Proofs:** [exact-completion-model-spectra-20261022.md](source/research/2026-10-22/notes/exact-completion-model-spectra-20261022.md) · [completion-space-parametrization-audit-20261022.md](source/research/2026-10-22/notes/completion-space-parametrization-audit-20261022.md)

**Scoped evidence:** [`EXACT-MODEL-DEGREES`](evidence/RESULT-INDEX.md#exact-model-degrees)

<a id="f01"></a>
## F01

RC_(t,t)+BC_(tt) implies Actuality, unboxed. BC_tt gives BC_t and a haecceity join; represented disjoint refinement reduces to the reflection lemma for a true disjoint join. Boxed premises yield the boxed conclusion only by necessitating the discharged theorem.

**Lean certified:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness): RC + BC ⇒ TC; the sharp Actuality theorem, Actuality-based TC, and the same-type RC + BC and CBC + CCC consequences.

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [choice-completeness-actuality.md](source/research/2026-10-22/followup/choice-completeness-actuality.md) · [choice-completeness-actuality-audit.md](source/research/2026-10-22/followup/choice-completeness-actuality-audit.md)

**Scoped evidence:** [`CHOICE-COMPLETENESS`](evidence/RESULT-INDEX.md#choice-completeness)

<a id="f02"></a>
## F02

Exact compatible-history limits and represented chain-complete preorder, RC-derived strict-unless-full progression; finite-ambiguity criterion. RC alone implies TC remains open.

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [choice-compatible-history-limits.md](source/research/2026-10-22/followup/choice-compatible-history-limits.md) · [choice-transversal.md](source/research/2026-10-22/followup/choice-transversal.md) · [choice-coherence.md](proofs/choice-coherence.md) · [coextension-operations.md](proofs/coextension-operations.md)

**Scoped evidence:** [`CHOICE-COHERENCE`](evidence/RESULT-INDEX.md#choice-coherence) · [`COEXTENSION-OPERATIONS`](evidence/RESULT-INDEX.md#coextension-operations)

<a id="f03"></a>
## F03

Weakly persistent two-output truth selector iff Actuality; RC graphs normalize to necessarily total/functional graphs with containment only actual; finite stabilizer-orbit obstructions.

**Evidence:** [main](DATABASE-INTEGRATION.md#f03--main).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [choice-transversal-symmetry.md](source/research/2026-10-22/followup/choice-transversal-symmetry.md)

<a id="f04"></a>
## F04

Symmetric full-BC surjection construction fails precisely RC_(t,t); stronger support-fragment choice obstruction. Paired-individual model satisfies specified finite-input and propositional-output choice fragments while TC_e and RC_(et,e) fail.

**Evidence:** [main](DATABASE-INTEGRATION.md#f04--main) · [paired_fragment](DATABASE-INTEGRATION.md#f04--paired_fragment).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [choice-propositional-symmetry-obstruction.md](source/research/2026-10-22/followup/choice-propositional-symmetry-obstruction.md) · [choice-support-obstruction.md](source/research/2026-10-22/followup/choice-support-obstruction.md) · [choice-paired-atoms-type-fragment.md](source/research/2026-10-22/followup/choice-paired-atoms-type-fragment.md)

<a id="f05"></a>
## F05

SL+RigidComp implies full boxed RigidComp and boxed BC, including individual/mixed tuples by haecceity-code pullback. Weaker sufficient package: SL_t+RigidComp+BF_rel.

**Lean certified:** [`MODAL-PROPAGATION`](evidence/RESULT-INDEX.md#modal-propagation).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [modal-propagation.md](source/research/2026-10-22/followup/modal-propagation.md)

**Scoped evidence:** [`MODAL-PROPAGATION`](evidence/RESULT-INDEX.md#modal-propagation)

<a id="f06"></a>
## F06

Stitched forcing/coalesced middle-world countermodel to dropping BF_rel: boxed SL_t, root RigidComp, boxed BF_t/BF_e, boxed RelChoice/Actuality, but failures of boxed RigidComp and boxed BC at et.

**Evidence:** [main](DATABASE-INTEGRATION.md#f06--main).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [propagation-without-barcan-countermodel.md](source/research/2026-10-22/followup/propagation-without-barcan-countermodel.md)

<a id="f07"></a>
## F07

Every permitted fixed set-sized signature has supported-product gluing model of Logical Necessity, boxed BF/TR, RelChoice and Countable BC, atomlessness and failure of Actuality/Vicinity/WIC/RP. Infinite-moving-individual variant has both quantified infinities.

**Lean certified:** [`LOGICAL-NECESSITY-SEPARATION`](evidence/RESULT-INDEX.md#logical-necessity-separation).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [central-map.md](source/research/2026-10-22/followup/central-map.md)

**Scoped evidence:** [`LOGICAL-NECESSITY-SEPARATION`](evidence/RESULT-INDEX.md#logical-necessity-separation)

<a id="f08"></a>
## F08

Separate symmetric-surjection/free-word model has Logical Necessity, boxed BC/BF/TR/WRP, atomlessness and no Actuality/Vicinity, but fails RelChoice. Exact cancellation criterion controls BF; moving-individual variants retain infinities.

**Evidence:** [cancellation_criterion](DATABASE-INTEGRATION.md#f08--cancellation_criterion) · [main](DATABASE-INTEGRATION.md#f08--main).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [central-map-complete-gluing.md](source/research/2026-10-22/followup/central-map-complete-gluing.md)

<a id="f09"></a>
## F09

Full boxed FC is not finitely axiomatizable by fixed-type closed formulas over C. Strict cofinal selector/diagonal hierarchies; bounded-type-order obstruction; input/output hierarchy distinctions and single-fixed-input nonfinite basis.

**Proofs:** [finite-functional-choice.md](source/research/2026-10-22/followup/finite-functional-choice.md) · [choice-nonfinite-basis.md](proofs/choice-nonfinite-basis.md)

**Scoped evidence:** [`CHOICE-NO-FINITE-BASIS`](evidence/RESULT-INDEX.md#choice-no-finite-basis)

<a id="f10"></a>
## F10

Conditional AD_R uniformization separator; failed one-block Cohen reservoir refuted by an explicit real-indexed relation; alternative full-Aut(Cohen) construction proposes ZF+DC_omega1+Unif(Reals)+not WO(Reals), yielding boxed FC_(t,t)+boxed not Sel_t.

**Evidence:** [conditional_ad_r](DATABASE-INTEGRATION.md#f10--conditional_ad_r) · [main](DATABASE-INTEGRATION.md#f10--main) · [refuted_reservoir](DATABASE-INTEGRATION.md#f10--refuted_reservoir).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [type-t-uniformization.md](source/research/2026-10-22/followup/type-t-uniformization.md)

<a id="f11"></a>
## F11

Pure Maximalism + unboxed propositional Atomicity is inconsistent. The final proof and exact Lean certificate use the canonical Jech–Shelah splitting construction; no extra selector or non-theoremhood hypothesis remains.

**Lean certified:** [`MAX-ATOMICITY`](evidence/RESULT-INDEX.md#max-atomicity).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [max-atomicity-rigid-selector.md](source/research/2026-10-22/followup/max-atomicity-rigid-selector.md) · [max-atomicity-selector-audit.md](source/research/2026-10-22/followup/max-atomicity-selector-audit.md)

**Scoped evidence:** [`MAX-ATOMICITY`](evidence/RESULT-INDEX.md#max-atomicity)

<a id="f12"></a>
## F12

Atomicity preserved by stated full coalescences; exact single-sentence construction criterion; atomic predecessor of atomless world and infinite atomic profiles with standard arithmetic/no Actuality.

**Evidence:** [atomic_profiles](DATABASE-INTEGRATION.md#f12--atomic_profiles) · [main](DATABASE-INTEGRATION.md#f12--main).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [max-atomicity.md](source/research/2026-10-22/followup/max-atomicity.md)

<a id="f13"></a>
## F13

Truth-preserving Boolean absorption/elementarity over the common term algebra, arbitrary finite Boolean alternations and several fixed evaluations; guarded numerical disjunction/witness preservation.

**Lean certified:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria): The universal-core equivalence and the stated conditional disjunction criterion.

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [strong-possibility.md](source/research/2026-10-22/followup/strong-possibility.md)

**Scoped evidence:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria)

<a id="f14"></a>
## F14

Pure SP one-step C+I omega-rule and true Pi02 arithmetic; sharp correctness boundary if consistent; explicit numerical H-Barcan obstruction.

**Lean certified:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria): The universal-core equivalence and the stated conditional disjunction criterion.

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [strong-possibility.md](source/research/2026-10-22/followup/strong-possibility.md)

**Scoped evidence:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria) · [`SP-ARITHMETIC-REFLECTION`](evidence/RESULT-INDEX.md#sp-arithmetic-reflection)

<a id="f15"></a>
## F15

Full-term homomorphisms embed actual number fields; retractions force arithmetic isomorphism. D(P) at Max model M iff a one-way full-term embedding into a Max+P model. Exact target-kernel quotient, algebraic removal of H(G), and no-go for generic term/numerical profiles.

**Lean certified:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria): The universal-core equivalence and the stated conditional disjunction criterion.

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [strong-possibility-one-way.md](source/research/2026-10-22/followup/strong-possibility-one-way.md)

**Scoped evidence:** [`SP-CRITERIA`](evidence/RESULT-INDEX.md#sp-criteria)

<a id="r01"></a>
## R01

In C, relational-atom existential projection is a proposition atom; coordinates exist iff some current value is nonzero. Local polyadic BF suffices. Collision iff w=v and w<=tuple identity; tuple ND gives uniqueness, and Atomicity_t makes uniqueness imply tuple ND.

**Evidence:** [collision_uniqueness](DATABASE-INTEGRATION.md#r01--collision_uniqueness) · [main](DATABASE-INTEGRATION.md#r01--main).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [atom-normal-form.md](source/research/2026-10-22/proof-refinements/atom-normal-form.md)

<a id="r02"></a>
## R02

Canonical completely additive atomic part below a finite additive faithful charge, zero-on-atoms remainder and normalized faithful replacement by finite subsums.

**Lean certified:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability): Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [canonical-atomic-probability.md](source/research/2026-10-22/proof-refinements/canonical-atomic-probability.md)

**Scoped evidence:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability)

<a id="r03"></a>
## R03

Over C + ☐Functional Choice + quantified Infinity_e, faithful represented-R-invariant state iff internally countable worlds and finite R-classes; explicit completely additive replacement.

**Evidence:** [main](DATABASE-INTEGRATION.md#r03--main).

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [probability-under-world-partitions.md](source/research/2026-10-22/proof-refinements/probability-under-world-partitions.md)

<a id="r04"></a>
## R04

Actuality+quantified Infinity_e gives exact number isomorphism with its slice; GC version too. Preserves literal number identity and represented arithmetic/subsets, without Choice or BF.

**Lean certified:** [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations): The displayed Frege noncollapse and finiteness equivalences, number-map/Hume-class results, and C5–Actuality transfer results.

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [infinity-core-number-isomorphism.md](source/research/2026-10-22/proof-refinements/infinity-core-number-isomorphism.md)

**Scoped evidence:** [`ARITHMETIC-FOUNDATIONS`](evidence/RESULT-INDEX.md#arithmetic-foundations)

<a id="r05"></a>
## R05

Over C + ☐Plenitude + quantified Infinity_e, faithful finite/countable/complete-additive probability iff finite-fibre numerical labelling of worlds. Countable Choice for finite fields upgrades this to injection/countability.

**Lean certified:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability): Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.

**Exact reconciliation scope:** Finite fibres need not be singletons. The countability upgrade needs its separate choice resource; the exact finite-fibre statement does not. The countably/completely additive state is a constructed replacement; an arbitrary original finitely additive state is not thereby countably additive. R09 supplies current graph-valued probabilities, not automatically ambient C operations or a future-stable globally rigid real-code domain. It does not lower the stronger assumptions of higher-type or lifted world-symmetry theorems. Ordinary arithmetic or analysis-stability theorems do not provide the required internal number/core interpretation, represented-family operations, finite-fibre criterion, or type-ceiling argument.

**Scope assessment:** [integration-scope-reconciliation.json](evidence/integration-scope-reconciliation.json)

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [choice-free-faithful-probability.md](source/research/2026-10-22/proof-refinements/choice-free-faithful-probability.md)

**Scoped evidence:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability)

<a id="r06"></a>
## R06

Choice-free averaging on finite world classes gives unique completely additive invariant state with normalized class masses, idempotently; criterion is finite-fibre labelling plus finite classes over C + ☐Plenitude + Infinity_e.

**Lean certified:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability): Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.

**Exact reconciliation scope:** Finite fibres need not be singletons. The countability upgrade needs its separate choice resource; the exact finite-fibre statement does not. The countably/completely additive state is a constructed replacement; an arbitrary original finitely additive state is not thereby countably additive. R09 supplies current graph-valued probabilities, not automatically ambient C operations or a future-stable globally rigid real-code domain. It does not lower the stronger assumptions of higher-type or lifted world-symmetry theorems. Ordinary arithmetic or analysis-stability theorems do not provide the required internal number/core interpretation, represented-family operations, finite-fibre criterion, or type-ceiling argument.

**Scope assessment:** [integration-scope-reconciliation.json](evidence/integration-scope-reconciliation.json)

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [canonical-finite-class-symmetrization.md](source/research/2026-10-22/proof-refinements/canonical-finite-class-symmetrization.md)

**Scoped evidence:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability)

<a id="r07"></a>
## R07

Admitted powerset P(X) has finite-fibre numerical labelling iff X is internally finite. Choice-free tt ceiling; event type (et)t already conflicts with quantified Infinity_e under C + ☐Plenitude.

**Lean certified:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability): Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.

**Exact reconciliation scope:** Finite fibres need not be singletons. The countability upgrade needs its separate choice resource; the exact finite-fibre statement does not. The countably/completely additive state is a constructed replacement; an arbitrary original finitely additive state is not thereby countably additive. R09 supplies current graph-valued probabilities, not automatically ambient C operations or a future-stable globally rigid real-code domain. It does not lower the stronger assumptions of higher-type or lifted world-symmetry theorems. Ordinary arithmetic or analysis-stability theorems do not provide the required internal number/core interpretation, represented-family operations, finite-fibre criterion, or type-ceiling argument.

**Scope assessment:** [integration-scope-reconciliation.json](evidence/integration-scope-reconciliation.json)

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [choice-free-probability-type-ceiling.md](source/research/2026-10-22/proof-refinements/choice-free-probability-type-ceiling.md)

**Scoped evidence:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability)

<a id="r08"></a>
## R08

Ordinary Eval (equivalently ND+Actuality) yields canonical quantifier-preserving actual-world evaluator; global bivalence identifies any supplied evaluator with it. No BF/Choice or future-predicate boxed law.

**Lean certified:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores): Actuality-core conversion and admitted-value lemmas.

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [canonical-actual-evaluator.md](source/research/2026-10-22/proof-refinements/canonical-actual-evaluator.md)

**Scoped evidence:** [`EVALUATORS-CORES`](evidence/RESULT-INDEX.md#evaluators-cores)

<a id="r09"></a>
## R09

Local graph-valued propositional probability finite-fibre criterion under Actuality+Atomicity_t+BC_t+quantified Infinity_e, without ND/BF/Plenitude/Choice.

**Lean certified:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability): Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone.

**Exact reconciliation scope:** Finite fibres need not be singletons. The countability upgrade needs its separate choice resource; the exact finite-fibre statement does not. The countably/completely additive state is a constructed replacement; an arbitrary original finitely additive state is not thereby countably additive. R09 supplies current graph-valued probabilities, not automatically ambient C operations or a future-stable globally rigid real-code domain. It does not lower the stronger assumptions of higher-type or lifted world-symmetry theorems. Ordinary arithmetic or analysis-stability theorems do not provide the required internal number/core interpretation, represented-family operations, finite-fibre criterion, or type-ceiling argument.

**Scope assessment:** [integration-scope-reconciliation.json](evidence/integration-scope-reconciliation.json)

**Proofs:** [INVENTORY.md](source/research/2026-10-22/lean-formalization/INVENTORY.md) · [local-propositional-probability.md](source/research/2026-10-22/proof-refinements/local-propositional-probability.md)

**Scoped evidence:** [`PROBABILITY`](evidence/RESULT-INDEX.md#probability)

<a id="catalog.06"></a>
## catalog.06

At any one relational type, operation-valued uniform Persistent, Weak Persistent, or Weak Inextensible Comprehension each characterizes Actuality. No analogous equivalence for full uniform IC is asserted.

**Evidence:** [main](DATABASE-INTEGRATION.md#catalog.06--main).

**Lean certified.**

**Proofs:** [RESULT-CATALOG.md](source/research/2026-10-22/RESULT-CATALOG.md) · [uniform-half-comprehension-definitions.md](source/research/2026-10-22/notes/uniform-half-comprehension-definitions.md)

<a id="central.signature_countermodels"></a>
## central.signature_countermodels

Finite/natural full-model single-constant signature separators for the displayed central-question rows, with exact signature restrictions.

**Lean certified:** [`SIGNATURE-INDEPENDENCE`](evidence/RESULT-INDEX.md#signature-independence).

**Proofs:** [central-questions-audit.md](source/research/2026-10-22/central-questions-audit.md)

**Scoped evidence:** [`SIGNATURE-INDEPENDENCE`](evidence/RESULT-INDEX.md#signature-independence)

<a id="synthesis.npc-atomicity"></a>
## synthesis.npc-atomicity

C5 plus Atomicity (type t) entails No Pure Contingency: each closed pure sentence, if true, is necessary.

**Lean certified.**

**Proofs:** [c5-and-atomicity-imply-no-pure-contingency.md](source/topics/classicism/writeups/c5-and-atomicity-imply-no-pure-contingency.md)

**Scoped evidence:** [`NPC-ATOMICITY`](evidence/RESULT-INDEX.md#npc-atomicity)

<a id="synthesis.colour-collapse-scope"></a>
## synthesis.colour-collapse-scope

The colour-collapse model satisfies Tame Rigidity and ☐BF, together with ☐Rigid Power (type et), but fails Weakly Rigid Power (type et). It also fails Rigid Power (type (et)t).

**Lean certified.**

**Proofs:** [colour-collapse-entrance.md](source/research/2026-10-22/notes/colour-collapse-entrance.md) · [colour-collapse.md](proofs/colour-collapse.md)

**Scoped evidence:** [`COLOUR-COLLAPSE-SCOPE`](evidence/RESULT-INDEX.md#colour-collapse-scope)

<a id="synthesis.diagonal-characters"></a>
## synthesis.diagonal-characters

Separation of propositions by diagonal characters is equivalent over C to ND (type t) together with Atomicity (type t).

**Lean certified.**

**Proofs:** [diagonal-characters.md](proofs/diagonal-characters.md)

**Scoped evidence:** [`DIAGONAL-CHARACTERS`](evidence/RESULT-INDEX.md#diagonal-characters)

<a id="synthesis.evaluator-modal-commutation"></a>
## synthesis.evaluator-modal-commutation

Existence of an actual truth evaluator that commutes with box is equivalent to Extensionality. The same is true with diamond in place of box.

**Lean certified.**

**Proofs:** [gallin-bivalent-evaluator.md](source/research/2026-10-22/notes/gallin-bivalent-evaluator.md)

**Scoped evidence:** [`EVALUATOR-MODAL-COMMUTATION`](evidence/RESULT-INDEX.md#evaluator-modal-commutation)

<a id="synthesis.coextension-operations"></a>
## synthesis.coextension-operations

At any fixed relational type with nonempty argument domains, Actuality is equivalent to an extension-preserving operation whose internal invariant closure exhausts every actual coextension class. Finite iteration of coextension-class coding preserves all selector ambiguity.

**Lean certified:** Orbit averaging and finite code towers; orbit/Actuality equivalence at t and inhabited unary types.

**Proofs:** [coextension-operations.md](proofs/coextension-operations.md)

**Scoped evidence:** [`COEXTENSION-OPERATIONS`](evidence/RESULT-INDEX.md#coextension-operations)

<a id="synthesis.logical-observers"></a>
## synthesis.logical-observers

Over H, OS entails C + BF; full typed endpoint separation is equivalent to C5 + Atomicity (type t), and full typed factive separation is equivalent to Extensionality. Over C, the strict hierarchy is Extensionality ⇒ C5 + Atomicity (type t) ⇒ ☐OS ⇒ OS ⇒ BF. Atomicity (type t) + BF implies OS. Over C5 + Actuality, OS, ☐OS and Atomicity (type t) are equivalent. Over C5, ☐OS + ◇Actuality entails ☐Plenitude; replacing ☐OS by OS does not suffice. Given OS, uniqueness of the qualified logical observer is equivalent to Extensionality. Reversible separation is equivalent to involutive separation and to its separately boxed schema, and entails C5 + ☐OS. Reversible separation together with Actuality, one atom, or one qualified observer at t with finitely many outputs is equivalent to endpoint separation. Finite-image separation is incomparable with reversible separation, C + Atomicity (type t) + BF, and ☐OS. Under C5, propositional atoms correspond bijectively to endpoint observers qualified at t. In the propositional conjunction/universal fragment, requiring jointly qualified observers is strictly stronger over H than requiring separate separating classes. Over C, universal separation and joint separation are equivalent to the corresponding unboxed BF instances for each finite type list. Over C, each singleton connective-preservation separation principle holds, while any two of conjunction, disjunction and negation preserved by the same observers give Boolean separation. Top-accepting identity-fixing separation at t is exactly ND (type t); adjoining universal preservation at the finite list Δ gives ND (type t) + BF at Δ, hence C5 when t belongs to Δ. Over C, an endpoint-fixing operator with range {⊤,⊥} exists exactly when modal .2 holds. Over C5, propositional separation by Boolean observers preserving the universal quantifier at t is equivalent to full OS. Over C, either of the accepting, identity-fixing mixed N/Q_t or V/Q_t separation formulas characterizes C5 + OS. The finite-support natural-numbers/singleton all-maps model gives OS with failure of ☐BF_e, ☐BF_t and ☐Functionality at (e,t). Under C5, ☐OS plus one atom is equivalent to endpoint separation; the single boxed propositional Good_{ {t} } separation formula suffices. Reversible logical separation implies No Pure Contingency without atoms or Actuality. The implication from reversible separation to C5 + ☐OS is strict even in atomless models. The finite-block symmetry countermodel makes the pure six-element subset-selection sentence contingent. Reversible separation is equivalently logical separation by necessarily bijective observers; over C it is also separation by invertible universal-preserving observers at finite type lists containing t. Full separation by observers with admitted qualified right inverses is exactly reversible separation. Qualified left-inverse separation is strictly weaker, even with C5 and its own boxed schema; it implies OS but does not imply C5, ☐OS, its own boxed schema, ☐BF or ☐Functionality. Separate full endpoint-fixing M/Q/P, V/Q/P and N/Q/P separation, even with all their boxed instances and boxed BF and Functionality, does not imply Boolean separation: the ternary Cantor model refutes the unrestricted mixed-quantifier reductions. The arrow from qualified left-inverse separation to OS is also strict, and SplitMono is incomparable with ☐OS. Under internal finiteness of all propositions, full SplitMono, Rev and endpoint separation coincide. Even C5 + ☐SplitMono + No Pure Contingency does not imply Rev. Rev implies the stronger noncontingency schema for pure formulas with finitely many individual parameters and endpoint-valued first-order relation parameters. Over C + BF, each fixed-list left-inverse separation instance is equivalent to the corresponding reversible instance or ordinary separation together with one qualified left-inverse pair having a true kernel element. Full H scope gives an external schema of such alternatives, not a global disjunction. If every admitted injective proposition operation is onto, full left-inverse and reversible separation coincide; the two-colour atomless model satisfies this condition and Rev while endpoint separation fails. Over H, endpoint separation is equivalent to OS + Plenitude at (t,t), OS + full Plenitude, C5 + OS + Actuality, C5 + OS + Boolean Completeness, and C5 + Atomicity (type t). Already C + BF (type t) + Plenitude at (t,t) is equivalent to C5 + Actuality. Over C5, each currently surjective Good observer at a finite list containing t has a definable admitted same-list qualified right inverse; hence Rev is equivalent over H to C5 + full surjective logical separation. Both chains Rev ⇒ SurjSep ⇒ OS and Rev ⇒ SplitMono ⇒ OS are strict. SurjSep and SplitMono are incomparable even over C + ☐BF + ☐OS, witnessed by the full omega-chain and the C5 finite-block model. Within C5, SurjSep is Rev and does imply SplitMono. The linear/circular fibre model satisfies C5 + ☐OS + D_t with atomless propositions but fails SplitMono at the explicit propositional list {t,e,et,eet,(et)t,((et)t)t}; a contingent closed pure sentence about infinite amorphous cells proves the obstruction. A specified countably infinite sequence fixed by a source symmetry group in the all-bijections finite-pinning framework gives one qualified left-inverse pair with a true kernel element, normalizing ordinary separators at that source. At the trivial-symmetry object of the qualitative-contrast model, C5 + SplitMono holds but ☐OS and ☐SplitMono fail. Thus SplitMono and ☐OS are incomparable even over C5. Every full cancellative-monoid action model with singleton individuals satisfies separately boxed full SurjSep. A specified infinite sequence of distinct units also gives separately boxed full SplitMono, with one common qualified left inverse. A nonunit refutes C5. The concrete monoid ℤ×ℕ therefore refutes ☐SurjSep + ☐SplitMono ⇒ Rev, even over C + ☐BF. SurjSep + SplitMono lies strictly below Rev and strictly above each factor; its two witness families may be different. Over C + BF (type t), Onto(E) implies ☐Onto(E), with E a free parameter; Good qualification is persistent over C. Full SurjSep nevertheless gives neither ☐OS nor ☐SurjSep, even with ☐BF and ☐Functionality. A root truth-profile extension of a fixed/free symmetry tail supplies this countermodel, with failure already at the future propositional Boolean instance. Thus Rev ⇒ ☐SurjSep ⇒ SurjSep and ☐SurjSep ⇒ ☐OS are strict. SurjSep does not imply ☐BF, with failure at every admitted type in the integer-shift predecessor model. Over C5, every admitted Good-{t} observer E has admitted order adjoints L ⊣ E ⊣ R, with Rq=∃p[(Ep≤q)∧p] and Lq=¬R(¬q). With k=RBottom and a=¬k, R(Ep)=p∨k and L(Ep)=p∧a, giving a Boolean order isomorphism from [Bottom,a] onto the admitted image. Injectivity is equivalent to RBottom=Bottom or LTop=Top; onto is equivalent to join preservation by R or meet preservation by L; bijectivity is equivalent to R=L or negation preservation by either adjoint. The admitted image floor ER and ceiling EL are idempotent, with ER≤I≤EL and mutual absorption. ER is an auxiliary S5 interior and equals native Box exactly when E is endpoint-valued. The endpoint-fixing envelopes T−q=(a∧Rq)∨(k∧q) and T+q=Lq∨(k∧q) preserve M/all Q and V/all P respectively, and coincide exactly when E is onto. Already for a Boolean E over C5, commuting with native Box or Diamond is exactly injectivity, without Q_t. The integer-shift predecessor model satisfies C + full typed SurjSep + BF while ☐BF_σ fails at every admitted type σ. In the finite-pinning tail over ℕ×ℤ and {∗}×ℤ, split epimorphisms approximate finite pins and invertible integer translations supply prescribed-coordinate kernel pairs. The root truth-profile extension combines all-type evaluation readers with those onto tails. A future object has nononto transport at every type and refutes every BF instance. Hence SurjSep ⇒ ☐BF is refuted with exact all-type scope. Full BoxSep restricts Good separators by the whole native-modality identity E∘Box=Box∘E; InjSep instead requires current injectivity. Over H, BoxSep gives C + OS + ☐BF + ☐Functionality + .2. Locally over C, BF_σ + BoxSep(t,Δ) gives ☐BF_σ when {σ,σt}⊆Δ. The .2 consequence needs only propositional separation by Bottom-fixing observers commuting with native Box, without Boolean or quantifier laws. Over C5, BoxSep(τ,Δ) is equivalent to InjSep(τ,Δ) at the same list, and Rev ⇒ InjSep=BoxSep ⇒ OS has both implications strict. Over C+BF, BoxSep is incomparable with InjSep and SplitMono; over C+☐BF it is incomparable with ☐OS. It implies neither C5 nor its own necessary schema. The linear/circular model refutes the entire converse OS+☐BF+☐Functionality+.2 ⇒ BoxSep. For an arbitrary admitted E over C, ☐Inj(E) is equivalent to an admitted unqualified whole left inverse; the description D_E(q)=∀p[(Ep=q)→p] supplies it without BF or Choice. Current injectivity does not suffice outside C5, even for an individually full-Good observer with necessary BF. Over C5, fix injective Good_Δ E with t∈Δ and admitted adjoints L⊣E⊣R. Put C_E=E∘L. Qualified left inverses F correspond bijectively to admitted propositions u satisfying C_E(u)=Top and ∀q[u∧C_E(u∧q)=u∧q], via F_u(q)=L(u∧q) and u_F=¬k_F. The proof uses Frobenius L(q∧Ep)=Lq∧p and the Boolean isomorphism p↦u∧Ep onto [Bottom,u], with all admitted quantifier laws. No Choice or external completeness is assumed. The full-function C5 model on 2×RO(Cantor²) has an injective all-type Good cylinder embedding with no qualified Good-t left inverse, although its admitted adjoints are unqualified left inverses. This model fails OS(t,{t}); it does not refute InjSep⇒SplitMono. The separation comparison remains unresolved generally and over C5. IdemBoxSep adds the whole identity E∘E=E to BoxSep. Over H, IdemBoxSep⇒BoxSep is strict, C5+IdemBoxSep is equivalent to Extensionality, and IdemBoxSep is incomparable with Rev and End; either conjunction with IdemBoxSep is Extensionality. In a full model with singleton individuals on a finite rooted poset P, Boolean observers are exactly inflationary coordinate maps E_f=f⁻¹; native-Box commutation is f[↑x]=↑f(x), and idempotence is f²=f. An idempotent native-Box reader of a is exactly x↦x∨a. Thus full IdemBoxSep holds exactly when P is a join-semilattice, and then holds necessarily. In the four-level family root<A_m<B_n<top, for positive finite m,n, BoxSep iff m=1 or n≤m, while IdemBoxSep iff m=1 or n=1. P_{2,2} gives strictness; P_{2,3} refutes BoxSep despite ☐OS+☐BF+☐Functionality+☐Atomicity_t+☐.2. The diamond has ☐IdemBoxSep but fails .3 and C5. A singleton root below a terminal two-point cluster has current IdemBoxSep but fails its boxed schema. Over C5, for each relational τ and finite Δ containing t, InjSep(τ,Δ) iff RevSep(τ,Δ) or (OS(τ,Δ) and J_Δ). J_Δ asserts one admitted injective Good_Δ E and one currently true c with R_Ec=Bottom, equivalently ∀p(Ep≤c→p=Bottom). The Boolean patch (c∧Gp)∨(¬c∧Ep) normalizes every ordinary G to an injective Good observer while preserving its entire current truth profile. The reverse alternative uses an admitted local interval involution, without treating L_E as globally Good. K_Δ implies J_Δ. Under C5, same-observer quantifier reduction and Functionality reduce full OS, InjSep, Rev and SplitMono to their single propositional Good-{t} instances. Consequently full InjSep iff Rev or (OS and J_{t}), and full SplitMono iff Rev or (OS and K_{t}), as genuine finite disjunctions. The open C5 comparison is exactly whether OS+J_t forces Rev or K_t; that separation implication remains open, while J_t⇒K_t alone is refuted by the regular-open model, which fails OS. The general C+BF decomposition retains its finite-list schema. Over C+BoxSep(t,{t}), A→☐A holds for every finite universally closed parameter-free Boolean/native-modal sentence A=∀p̄ θ(p̄), with quantifier-free θ. More generally it holds for ∀R̄ φ(R̄) in the specified equality-free first-order modal fragment: predicate heads are only the outer variables, applied only to object-variable tuples; inner object quantifiers may be universal or existential at any admitted type, but object variables are not bare asserted propositions. Δ includes every outer predicate type and inner binder type. No inner quantified predicate head or other predicate constant is allowed. This gives the finite BF reflection and conditional .3→☐.3 and 5→☐5, not .3 or 5. Unconditional C equivalence transfers the theorem to equivalent modal-algebra statements. Arbitrary ∀p∃q with q asserted as a proposition is outside the theorem. C+BF_t+.2 already implies ☐.2. A four-point root/singleton/two-point-cluster model has C+☐OS+☐BF+☐Functionality and current ∀p(☐◇p→◇☐p) but not its necessity; it fails .2, so it does not separate reflection from the entire lower bundle. For each fixed external r≥1, B_r adds E^(r+1)=E^r to the native-Box logical qualification. B_1 is IdemBoxSep, and B_1⇒B_2⇒…⇒BoxSep has every successive implication strict; each fixed B_r strictly implies BoxSep. The separately boxed hierarchy is strict too. P_{3,2} witnesses the first step; for r≥2, a root followed by r two-point antichains and a top has ☐B_{r+1} but not B_r. On P_{m,n}, B_2 iff m=1 or n=1 or m>n; B_3 iff BoxSep. All witnesses retain C+☐OS+☐BF+☐Functionality+☐Atomicity_t+☐.2. One infinite frame with countably many two-point antichains and a common top has ☐BoxSep but fails every fixed B_r, witnessed by the same proposition pair. An admitted Q_t diagonal excludes all nonprincipal observer characters, extending the coordinate-reader and IdemBoxSep/join criteria to rooted posets of fixed finite external width. For every fixed r, C5+B_r, Rev+B_r and End+B_r are exactly Extensionality; B_r is incomparable with Rev and End. Over C5 and each fixed external n≥0, FG_n(E) says that the Boolean image of E plus n admitted propositions generates the ambient proposition algebra. A Good observer with a currently true local Boolean transversal has a qualified involution with its entire current truth profile, without an injectivity premise. FG_n supplies such a transversal, so separation by Good+FG_n observers is exactly Rev, at fixed τ,Δ containing t and at full scope with C5 retained; adding injectivity leaves the equivalence unchanged. For an individual injective FG_n observer, the controlled selector gives a qualified left inverse and can make Fc=Bottom whenever R_Ec=Bottom. Consequently K_Δ is exactly J_Δ with a one-generator image extension, equivalently J_Δ with FG_n for any fixed n≥1. J is an admitted relative logical embedding into a currently false principal interval; K is the corresponding relative logical isomorphism with an admitted inverse. The unchanged full-function C5 model on 2×RO(Cantor²) refutes J⇒K. Its clopen-partition embedding witnesses J and even has a qualified left inverse, but that inverse has a false greatest kernel, and every Good-t observer preserves current truth, ruling out K. OS fails in the same model, so OS+J_t⇒Rev∨K_t and InjSep⇒SplitMono remain open. The displayed embedding fails every fixed FG_n condition. The full exterior-arm poset A_{m,n} always has B_2 at its root. Its future P_{m,n} cone gives exact thresholds: ☐B_2 iff m=1 or n=1 or m>n; for fixed r≥3, ☐B_r iff ☐BoxSep iff m=1 or n≤m. A_{2,2} has B_2+☐B_3 but not ☐B_2. The single ten-point A_{2,3} has B_2 but not ☐BoxSep, and B_r but not ☐B_r for every fixed r≥2, retaining C+☐OS+☐BF+☐Functionality+☐Atomicity_t+☐.2. B_1 is hereditary within full finite-width poset models by the join criterion, not in general preorder models. Over C5, every Good_Δ observer E, with t∈Δ, has admitted local-transversal support s_E=∃b(Loc_E(b)∧b), using an endpoint locality guard defined by whole unary identity. Locality is injection of L_E on [Bottom,b]. The support is the maximal region whose every nonzero part contains a nonzero local transversal. An admitted join is local exactly when every pair of its members has local union; directed admitted families glue. The exact laws are Loc_{F∘E}(b) iff Loc_F(b) and Loc_E(L_F b), s_{F∘E}=s_F∧F(s_E), and s_G=(d∧s_E)∨(¬d∧s_F) for the Boolean patch G=dE∨¬dF. N(E)(p)=(s_E∧Ep)∨(¬s_E∧p) retracts the Good class onto its composition-closed support-Top subclass. Separation by full-support observers, by true-support observers, or by the admitted range of N is exactly Rev over C5 at fixed and full scope. No injectivity is assumed. Full support is strictly broader than each fixed FG_n for individuals and need not itself be local or imply an individual inverse. Under the additional current unboxed premises C5+BC_t+Zorn_t, any Good E and proposition r admit a maximal local u≤r with L_Eu=L_E(s_E∧r). BC_t supplies actual joins of current chain members; C_E is left adjoint to ER_E, so compatible locality survives those joins; Zorn_t supplies maximality. With injection added, a qualified left inverse exists iff L_Es_E=Top, and one killing a prescribed c exists iff L_E(s_E∧¬c)=Top. Thus K is exactly an injective Good observer with a currently true c and this controlled support coverage. A J witness with full support gives K under these premises, but J alone only gives L_E¬c=Top. Neither optional premise is necessitated, and no uniform choice is claimed. Over C5, TrueHom means that a currently true principal interval admits relative order isomorphisms to all its nonzero principal subintervals, with admitted inverses. Those witnesses preserve every requested quantifier. TrueHom implies Actuality or K; the atomic branch plus OS gives End and Rev, while the nonatomic branch gives a false-interval isomorphism and true-kernel inverse pair. Consequently C5+OS+TrueHom implies SplitMono without J. An admitted homogeneous cover with join Top suffices for TrueHom. External homogeneity alone does not. This sufficient condition does not resolve the general OS+J⇒Rev∨K question. Over C5, for every fixed external n≥1, Deg_n(E) says that n+1 disjoint propositions have L_E-images with zero common intersection. For arbitrary Good_Δ E with t∈Δ, without injection, this implies full local support and an admitted qualified involution with the same entire current truth profile. Degree-bounded separation is exactly Rev at fixed and full scope; degree one is exactly surjectivity. Degree bounds multiply under composition and add under Boolean patching. Under the additional current BC_t+Zorn_t premises, degree at most n is exactly a partition of Top into n local transversals, allowing zero sheets. FG_k implies Deg_{2^k} over C5 alone, and the reverse holds with BC_t+Zorn_t. All bounds are fixed external integers, not finite range or an internal quantifier over finite bounds. For every fixed relational τ and finite Δ, over C, Actuality+FinBoxSep(τ,Δ) iff Fin_t(All)+BoxSep(τ,Δ), with no t∈Δ, BF, Functionality, C5 or Choice added. FinBoxSep requires internally Frege-finite image of the same Good/native-Box observers. An observer accepting an actual world has identity's current truth profile; native-Box commutation makes it injective, and internal finite-preimage induction gives finite All. Conversely finite image induction and a finite true-meet fold give the other direction and Actuality. Full schema scope recovers C over H. In every full set-sized rooted-poset action model with singleton individuals, FinBoxSep iff the frame is finite and BoxSep holds, at arbitrary width; no infinite-width observer classification is used. Cent_Δ(E) means Good_Δ E and whole commutation with every admitted same-list Good G. Over C with unary Functionality, Boolean patches force idempotence. Over C5+S_{t,Δ}, t∈Δ, a central observer is identity or an endpoint observer with a currently true greatest kernel, with at most one nonidentity possibility. Central separation excludes that possibility using its true atomic kernel and the corresponding endpoint observer. Thus C5+CentreSep is exactly Extensionality, already from its propositional instance with t∈Δ. Full CentreSep+Rev and CentreSep+End also equal Extensionality. CentreSep is incomparable with Rev and End over H: a two-point chain has ☐CentreSep but fails C5, while a two-point S5 cluster has Rev and End but not CentreSep. In full finite rooted-poset models with singleton individuals, the centre is identity plus the constant-top map when top exists, so CentreSep holds exactly on a singleton or two-point chain. This is not merely a chosen pairwise commuting family or an abstract H classification. The unchanged atomless two-colour finite-pinning model additionally has ☐BC_t with C5+☐Rev+D_t, but fails Actuality, End, BC_tt and Zorn_t. Actual joins of stabilizer orbits are their finite fixed-pin projections, and finitely many such projections join the current extension of any admitted predicate. An admitted preorder of finite colour-coordinate joins refutes the single Zorn_t instance: finite pins bound all admitted antisymmetric chains, but fresh coordinates prevent maximal elements. The model therefore does not refute any conclusion with BC_t and Zorn_t jointly added. The exact type specialization of the recorded completeness proof gives C5+BC_tt⇒Plen_{t,t}⇒Actuality; with OS it gives End. Over C5, S_{t,Δ}+BC_σ implies ☐BC_σ when Δ contains σ and σt. Observers fix endpoint order judgments and postcompose the family predicate; current completeness and separation then identify BC_σ with Top. The C5 Good-t reduction permits the single S_{t,{t}} instance and full OS. This reflects each assumed instance, not a lift from BC_t to higher completeness. Over C5, full Rev is equivalent to the single finite sentence that only Bottom and Top are fixed by every reversible Good-t observer. The admitted join of reversible images is the least invariant proposition above an input. The same invariants are exactly the propositions respected by every logical observer on its local-transversal support, equivalently fixed by every support-normalized observer. Over H, full CentreSep is exactly IdemBoxSep plus at most four proposition objects and is equivalent to its separately boxed schema. Separation by the centre of the reversible logical group is exactly C5 plus the same four-proposition bound, is persistent, and is incomparable with CentreSep; their conjunction is Extensionality. For fixed external n≥1, Rev plus the whole identity E^n=I for every reversible Good-t observer is exactly C5 plus at most 2^k propositions, where k is the largest integer such that each of 1,…,k divides n. Finite common refinement supplies admitted cycles of each prescribed finite length. Full FinBoxSep is equivalent over H to BoxSep plus internal Frege finiteness of all propositions, and implies Actuality and necessary finiteness. Over C the fixed-instance equivalence needs any relational type in the finite qualification list; empty and individual-only lists remain unresolved without Actuality. C5 or Rev together with FinBoxSep is exactly End plus internal finiteness. FinBoxSep does not imply its boxed schema even with necessary global finiteness, as witnessed by the finite exterior-arm model. For every fixed nonempty reduced group word w, H+Rev+Law_w is exactly C5+AtMost_(2^k(w))(t), equivalently End plus that bound, where k(w) is the largest j for which Sym(j) satisfies w and 1≤k(w)≤length(w). Commutativity gives four propositions and the metabelian word gives eight. Over C5 without Rev, Law_w is exactly the condition that no k(w)+1 disjoint propositions have invariant orbit joins with nonzero common meet. Finitely many targets admit common reversible nonzero refinements exactly when their orbit joins overlap; finite invariant localization proves the converse group-law direction without Choice, BC or Zorn. Over H, an internally Frege-finite admitted observer family separating an admitted proposition class makes that class internally finite. The independent finite-table theorem counts admitted functions on finite input/output predicates under an identifying evaluation premise; Functionality supplies that premise for a full input domain. H+Rev+Fin_tt(Aut_Good_t), C5+FinAll, End+FinAll and C5+FinBoxSep are equivalent. Full finite-family ordinary logical separation is OS+FinAll; its reversible version is C5+FinAll; its native-Box version is FinBoxSep. Over H, OS plus existence of a correct actual-truth evaluator is equivalent to endpoint separation. Over C, endpoint separation is equivalent to necessary existence of a unique correct evaluator and to ☐Plenitude; existence of one evaluator necessarily correct at every world is equivalent to Extensionality.

**Lean certified:** H + OS ⇒ C + BF with explicit endpoint identities. Their omission is justified by the linked ordinary reduction proof.

**Proofs:** [logical-observer-hierarchy.md](proofs/logical-observer-hierarchy.md) · [logical-observers.md](proofs/logical-observers.md) · [operator-representation.md](proofs/operator-representation.md) · [full-identity-observers.md](proofs/full-identity-observers.md) · [observer-models.md](proofs/observer-models.md) · [observer-countermodel.md](proofs/observer-countermodel.md) · [local-observers.md](proofs/local-observers.md) · [logical-observer-endpoint-reduction.md](proofs/logical-observer-endpoint-reduction.md) · [meet-quantifier-separation.md](proofs/meet-quantifier-separation.md) · [observer-lattice.md](proofs/observer-lattice.md) · [observer-lattice-models.md](proofs/observer-lattice-models.md) · [modal-selectors-and-quantifier-reduction.md](proofs/modal-selectors-and-quantifier-reduction.md) · [logical-separation-with-contingent-barcan.md](proofs/h-observer-space/logical-separation-with-contingent-barcan.md) · [necessary-separation-and-atoms.md](proofs/h-observer-space/necessary-separation-and-atoms.md) · [reversible-separation-and-pure-truth.md](proofs/h-observer-space/reversible-separation-and-pure-truth.md) · [finite-block-symmetry-reversible-gap.md](proofs/h-observer-space/finite-block-symmetry-reversible-gap.md) · [reversible-quantifier-observers.md](proofs/h-observer-space/reversible-quantifier-observers.md) · [local-conjugacy-and-reversible-observers.md](proofs/h-observer-space/local-conjugacy-and-reversible-observers.md) · [split-inverse-logical-observers.md](proofs/h-observer-space/split-inverse-logical-observers.md) · [finite-block-symmetry-left-inverse.md](proofs/h-observer-space/finite-block-symmetry-left-inverse.md) · [ternary-cantor-observer-model.md](proofs/h-observer-space/ternary-cantor-observer-model.md) · [fork-one-sided-inverse-separation.md](proofs/h-observer-space/fork-one-sided-inverse-separation.md) · [component-shift-symmetry-reversible-gap.md](proofs/h-observer-space/component-shift-symmetry-reversible-gap.md) · [left-inverse-separation-decomposition.md](proofs/h-observer-space/left-inverse-separation-decomposition.md) · [finite-pinning-dedekind-propositions.md](proofs/h-observer-space/finite-pinning-dedekind-propositions.md) · [plenitude-endpoint-bridge.md](proofs/h-observer-space/plenitude-endpoint-bridge.md) · [surjective-logical-observers.md](proofs/h-observer-space/surjective-logical-observers.md) · [linear-circular-fibre-left-inverse-gap.md](proofs/h-observer-space/linear-circular-fibre-left-inverse-gap.md) · [omega-chain-surjective-observers.md](proofs/h-observer-space/omega-chain-surjective-observers.md) · [fixed-point-symmetry-left-inverse-separation.md](proofs/h-observer-space/fixed-point-symmetry-left-inverse-separation.md) · [full-cancellative-monoid-observers.md](proofs/h-observer-space/full-cancellative-monoid-observers.md) · [root-truth-profile-surjective-separation.md](proofs/h-observer-space/root-truth-profile-surjective-separation.md) · [canonical-adjoints-and-image-factorization.md](proofs/h-observer-space/canonical-adjoints-and-image-factorization.md) · [integer-shift-predecessor-contingent-barcan.md](proofs/h-observer-space/integer-shift-predecessor-contingent-barcan.md) · [native-box-logical-observers.md](proofs/h-observer-space/native-box-logical-observers.md) · [injective-observers-and-boolean-transversals.md](proofs/h-observer-space/injective-observers-and-boolean-transversals.md) · [idempotent-native-box-observers.md](proofs/h-observer-space/idempotent-native-box-observers.md) · [injective-separation-decomposition.md](proofs/h-observer-space/injective-separation-decomposition.md) · [native-box-reflection.md](proofs/h-observer-space/native-box-reflection.md) · [bounded-stabilization-native-box-observers.md](proofs/h-observer-space/bounded-stabilization-native-box-observers.md) · [finite-relative-image-generation.md](proofs/h-observer-space/finite-relative-image-generation.md) · [injective-gap-without-split-kernel.md](proofs/h-observer-space/injective-gap-without-split-kernel.md) · [exterior-arm-posets-native-box-nonpersistence.md](proofs/h-observer-space/exterior-arm-posets-native-box-nonpersistence.md) · [local-transversal-support.md](proofs/h-observer-space/local-transversal-support.md) · [zorn-local-transversal-selection.md](proofs/h-observer-space/zorn-local-transversal-selection.md) · [local-homogeneity-and-split-observers.md](proofs/h-observer-space/local-homogeneity-and-split-observers.md) · [bounded-fibre-degree-logical-observers.md](proofs/h-observer-space/bounded-fibre-degree-logical-observers.md) · [finite-image-native-box-observers.md](proofs/h-observer-space/finite-image-native-box-observers.md) · [central-logical-observers.md](proofs/h-observer-space/central-logical-observers.md) · [finite-colour-propositional-completeness.md](proofs/h-observer-space/finite-colour-propositional-completeness.md) · [reversible-fixed-proposition-characterization.md](proofs/h-observer-space/reversible-fixed-proposition-characterization.md) · [central-separation-and-four-propositions.md](proofs/h-observer-space/central-separation-and-four-propositions.md) · [finite-image-box-reflection.md](proofs/h-observer-space/finite-image-box-reflection.md) · [centre-of-reversible-logical-observers.md](proofs/h-observer-space/centre-of-reversible-logical-observers.md) · [invariant-components-and-local-support.md](proofs/h-observer-space/invariant-components-and-local-support.md) · [bounded-exponent-reversible-observers.md](proofs/h-observer-space/bounded-exponent-reversible-observers.md) · [group-identities-reversible-observers.md](proofs/h-observer-space/group-identities-reversible-observers.md) · [invariant-components-and-group-identities.md](proofs/h-observer-space/invariant-components-and-group-identities.md) · [internally-finite-observer-families.md](proofs/h-observer-space/internally-finite-observer-families.md)

**Scoped evidence:** [`LOGICAL-OBSERVERS`](evidence/RESULT-INDEX.md#logical-observers)

<a id="synthesis.analytic-rigidification"></a>
## synthesis.analytic-rigidification

Over C5 plus ☐Rigid Comprehension, a possible real structure at a fixed type has a rigid representative which is necessarily a real structure. Represented powers can be supplied simultaneously at each prescribed finite list of arities.

**Lean certified:** Rigidification and simultaneous represented powers of every prescribed finite list of positive arities, at every closed admitted type and in arbitrary signatures.

**Proofs:** [analytic-rigidification.md](proofs/analytic-rigidification.md)

**Scoped evidence:** [`ANALYTIC-RIGIDIFICATION`](evidence/RESULT-INDEX.md#analytic-rigidification)

<a id="synthesis.full-standard-gallin"></a>
## synthesis.full-standard-gallin

Over C + C5 + Atomicity (type t), Arbitrary Atomic Joins at every relational type is equivalent to fullness of the canonical standard hierarchy. Equivalently, every subset of each typed domain is the actual extension of an admitted property. No fixed bound on the indexed families suffices across arbitrary model sizes.

**Proofs:** [full-gallin.md](proofs/full-gallin.md) · [atomic-join-calculus.md](proofs/atomic-join-calculus.md) · [infinitary-canonical-representation.md](proofs/infinitary-canonical-representation.md)

**Scoped evidence:** [`FULL-STANDARD-GALLIN`](evidence/RESULT-INDEX.md#full-standard-gallin)

<a id="synthesis.forcing-transfer"></a>
## synthesis.forcing-transfer

In the specified full modalized-domain construction, recursive normal forms identify every finite relational type with its Boolean-valued counterpart. The lottery cloud therefore makes both CH and its negation possible for real structures at the same fixed type et.

**Proofs:** [forcing-transfer.md](proofs/forcing-transfer.md) · [forcing-reals.md](proofs/forcing-reals.md)

**Scoped evidence:** [`FORCING-TRANSFER`](evidence/RESULT-INDEX.md#forcing-transfer)

<a id="synthesis.finite-compression-separation"></a>
## synthesis.finite-compression-separation

A finite compression labelled entrance model satisfies Tame Rigidity and Rigid Power, but refutes Weakly Rigid Power (type et).

**Lean certified.**

**Proofs:** [finite-compression.md](proofs/finite-compression.md)

**Scoped evidence:** [`FINITE-COMPRESSION-SEPARATION`](evidence/RESULT-INDEX.md#finite-compression-separation)

<a id="synthesis.lambda-free-translation"></a>
## synthesis.lambda-free-translation

An explicit classical lambda-free applicative calculus has exactly C’s consequences in its original language, including open contexts and finite lists of assumptions. A conservative named extension reconstructs arbitrary C terms and full contextual beta eta delta conversion.

**Lean certified.**

**Proofs:** [lambda-free-reconstruction.md](proofs/lambda-free-reconstruction.md) · [lambda-logical-operators.md](proofs/lambda-logical-operators.md) · [lambda-finite-name-erasure.md](proofs/lambda-finite-name-erasure.md) · [bracket-abstraction.md](proofs/bracket-abstraction.md)

**Scoped evidence:** [`LAMBDA-FREE-TRANSLATION`](evidence/RESULT-INDEX.md#lambda-free-translation)

<a id="synthesis.beta-eta-conversion"></a>
## synthesis.beta-eta-conversion

On raw typed lambda syntax, beta identity at every relational output type, ordinary application congruence and the theorem-only fresh-variable rule from Fx=Gx to F=G derive eta, lambda congruence and every contextual beta eta conversion.

**Lean certified.**

**Proofs:** [beta-eta.md](proofs/beta-eta.md) · [beta-reduced-bases.md](proofs/beta-reduced-bases.md)

**Scoped evidence:** [`BETA-ETA-CONVERSION`](evidence/RESULT-INDEX.md#beta-eta-conversion)

<a id="synthesis.finite-type-propagation"></a>
## synthesis.finite-type-propagation

Under the Functionality instances in its type tree, a relational type containing no e is finite iff t is finite; one containing e is finite iff both e and t are finite. The downward implications already hold over bare C. Consequently, over C, quantified Infinity at t is equivalent to quantified Infinity at every relational type, and Infinity at e and t is equivalent to Infinity at every admitted type.

**Lean certified:** Finiteness propagation, descent, and the exact classification by type. The four C5 base-infinity combinations and the stated two-stage model/finiteness/Functionality endpoints.

**Proofs:** [finite-types.md](proofs/finite-types.md) · [finite-type-classification.md](proofs/finite-type-classification.md)

**Scoped evidence:** [`FINITE-TYPE-PROPAGATION`](evidence/RESULT-INDEX.md#finite-type-propagation)

<a id="synthesis.choice-coherence"></a>
## synthesis.choice-coherence

For a fixed actual equivalence R, two specified Relational Choice instances yield a transversal exactly when a successor chooser on good histories has some nonempty internally finite ambiguity cell at each active history.

**Proofs:** [choice-coherence.md](proofs/choice-coherence.md)

**Scoped evidence:** [`CHOICE-COHERENCE`](evidence/RESULT-INDEX.md#choice-coherence)

<a id="synthesis.full-identity-observers"></a>
## synthesis.full-identity-observers

Over C, Atomicity (type t) and BF at each tested type give separation by operators preserving Boolean connectives and both quantifiers as composite operation identities. Over C + ☐ND (type t) + Actuality this separation is equivalent to Atomicity (type t).

**Lean certified:** Simultaneous propositional separation for every finite list of closed quantifier types under C5 + Atomicity (type t), including its necessary schema; the converses and equivalence of the two schemas under C5 + Actuality.

**Proofs:** [operator-representation.md](proofs/operator-representation.md) · [ordered-observers.md](proofs/ordered-observers.md) · [full-identity-observers.md](proofs/full-identity-observers.md) · [local-observers.md](proofs/local-observers.md) · [operator-boundaries.md](proofs/operator-boundaries.md) · [observer-lattice.md](proofs/observer-lattice.md)

**Scoped evidence:** [`FULL-IDENTITY-OBSERVERS`](evidence/RESULT-INDEX.md#full-identity-observers)

<a id="synthesis.pure-sp-bounded-image"></a>
## synthesis.pure-sp-bounded-image

In the specified two-axiom pure SP test for a true independent Π₂ arithmetic sentence, any full pure-term embedding between the required Max endpoints sends every source number below every target counterexample.

**Proofs:** [pure-sp-bounded-image.md](proofs/pure-sp-bounded-image.md) · [pure-sp-omitted-cut.md](proofs/pure-sp-omitted-cut.md)

**Scoped evidence:** [`PURE-SP-BOUNDED-IMAGE`](evidence/RESULT-INDEX.md#pure-sp-bounded-image)

<a id="synthesis.signature-sp-survival"></a>
## synthesis.signature-sp-survival

For exactly one unary predicate constant and no individual names, nonemptiness of the first witness-derivative stage K₁ implies consistency of full signature SP. K₁ is nonempty exactly when each existential theorem of the marked Max theory has a named instance consistent with that theory.

**Proofs:** [signature-sp-first-stage.md](proofs/signature-sp-first-stage.md) · [signature-sp-derivative.md](proofs/signature-sp-derivative.md) · [signature-sp-effective.md](proofs/signature-sp-effective.md)

**Scoped evidence:** [`SIGNATURE-SP-SURVIVAL`](evidence/RESULT-INDEX.md#signature-sp-survival)

<a id="synthesis.infinitary-resources"></a>
## synthesis.infinitary-resources

One admitted predicate saying “different from every name” gives countable named-exhaustion reflection. A separate profile construction proves Max-eligibility for an explicit semantic reference theory Td, so SP(Td) entails exactly countably many actual individuals and failure of necessary exhaustion.

**Proofs:** [infinitary-resources.md](proofs/infinitary-resources.md)

**Scoped evidence:** [`INFINITARY-RESOURCES`](evidence/RESULT-INDEX.md#infinitary-resources)

<a id="synthesis.coalesced-ch"></a>
## synthesis.coalesced-ch

Assuming Con(ZFC), a coalesced sum of two extensional Henkin models makes CH and its negation possible at the same type e. It satisfies ☐Atomicity, ☐BF, ☐Strong Leibniz, ☐Rigid Rigidity, ☐Weakly Rigid Weak Rigidity, ☐Tame Rigidity and Modal Well-Ordering together.

**Lean certified:** Opposite-CH components at type e and their coalesced C countermodel with ☐BF, constructed in Lean’s ambient metatheory.

**Proofs:** [coalesced-ch.md](proofs/coalesced-ch.md) · [opposite-ch-components.md](proofs/opposite-ch-components.md)

**Scoped evidence:** [`CH-COALESCED`](evidence/RESULT-INDEX.md#ch-coalesced)

<a id="synthesis.max-ch"></a>
## synthesis.max-ch

Pure Maximalism together with Non-contingency of CH is inconsistent.

**Lean certified:** Maximalism + Non-contingency of CH ⇒ ⊥, using constructed type-e components in Lean’s ambient metatheory.

**Proofs:** [coalesced-ch.md](proofs/coalesced-ch.md) · [opposite-ch-components.md](proofs/opposite-ch-components.md)

**Scoped evidence:** [`MAX-CH`](evidence/RESULT-INDEX.md#max-ch)

<a id="synthesis.infinitary-comprehension"></a>
## synthesis.infinitary-comprehension

In the specified classical infinitary language, Infinitary Comprehension together with C5 characterizes the full standard relational hierarchies among set-sized models. Atomicity follows and need not be assumed. For every infinite regular κ, allowing fewer than κ simultaneous parameters leaves a countermodel, even when formula size is unrestricted. Without C5, the surjection and idempotent full action models satisfy the specified infinitary comprehension schema while retaining their failures of ND or BF.

**Lean certified:** For universe-0 categorical premodels, term-denotation closure + unrestricted original-closed-type Infinitary Comprehension + ☐ND (type t) imply faithful full-standard representation; full standard models satisfy the corresponding infinitary axioms.

**Proofs:** [infinitary-comprehension.md](proofs/infinitary-comprehension.md) · [infinitary-canonical-representation.md](proofs/infinitary-canonical-representation.md) · [lambda-free-reconstruction.md](proofs/lambda-free-reconstruction.md)

**Scoped evidence:** [`INFINITARY-COMPREHENSION`](evidence/RESULT-INDEX.md#infinitary-comprehension)

<a id="synthesis.forcing-possibilism"></a>
## synthesis.forcing-possibilism

With the database’s strict-smallness definition, Forcing Possibilism is independent over C + ☐Functional Choice + Axiom of Infinity (types e and t). For any infinite world set W in external ZFC, full S5 satisfies FP exactly when 2^{|W|} equals the continuum. A free-root model satisfies FP and both quantified Infinity axioms while failing Intensional Choice.

**Proofs:** [forcing-possibilism.md](proofs/forcing-possibilism.md)

**Scoped evidence:** [`FORCING-POSSIBILISM`](evidence/RESULT-INDEX.md#forcing-possibilism)

<a id="synthesis.infinity-schema-separation"></a>
## synthesis.infinity-schema-separation

C + ☐Functional Choice has a Henkin model satisfying both finite lower-bound Infinity schemata while necessarily refuting both corresponding quantified Axioms of Infinity. A second model satisfies ☐Functional Choice, ☐FP, ☐Axiom of Infinity (type t) and the individual Infinity schema while necessarily refuting Axiom of Infinity (type e).

**Proofs:** [forcing-possibilism.md](proofs/forcing-possibilism.md)

**Scoped evidence:** [`INFINITY-SCHEMA-SEPARATION`](evidence/RESULT-INDEX.md#infinity-schema-separation)

<a id="synthesis.h-observer-space"></a>
## synthesis.h-observer-space

For any finite set Γ of independent primitive preservation clauses M, V, N, Qσ, Pσ, put T_J = H + S[A ∧ Z ∧ J]. At a fixed preservation tier and fixed propositional or full relational scope, T_K entails T_J exactly when J ⊆ K. Uniform corruption models prove every omitted-clause non-implication. For every observer qualification K, full relational separation is equivalent over H to propositional separation plus Functionality. Conjoining separately separating classes can be strictly weaker than requiring one class to satisfy both qualifications. The accompanying representation theorems characterize the connective, quantifier and equality branches with their explicit premises. Reversible accepting/rejecting meet separation plus one atom makes atoms separate order, represents every proposition as the join of its atoms, and gives a unique true atom. Under internal Frege finiteness of all propositions, material and pointwise meet separation are equivalent, and likewise for join separation, retaining each acceptance/rejection orientation. Full relational separation collapses all three tiers. A least true meet element or greatest false join element suffices for the corresponding normalization without finiteness. Reversible meet separation plus one atom is exactly bounded atomistic meet structure, a true atom and transitivity of admitted full-meet automorphisms on atoms; arbitrary extra restrictions use the exact MoveTrue condition without closure assumptions. A six-element model shows that atomisticity and a true atom alone do not suffice. For each finite preservation signature, pointwise separation is equivalent to the existence of an admitted composition-closed separating family of material observers, equivalently such a composition-closed family containing identity. Finite-image material meet separation is equivalent to at-most-two-output pointwise meet separation, and likewise for join, without finiteness of the proposition domain. Full typed OS need not imply ☐BF or ☐Functionality. Endpoint logical separation is equivalent to C5 + ☐OS + one atom, and already to C5 plus the boxed propositional Good_{ {t} } separation instance plus one atom. Reversible logical separation implies C5 + ☐OS + No Pure Contingency, with no atom or Actuality premise. The proof extends qualified involutions by typewise conjugation and applies separation to each closed pure sentence. Reversible logical separation is strictly stronger than C5 + ☐OS, even among atomless models: the even-block/power-of-two-block symmetry model has necessary OS but a contingent closed pure six-element selection sentence. Over H + ND (type t), material and pointwise meet/universal separation have the same exact meet/GLB representation, with a dual join/existential result. Finite-image normalization extends to matching quantifiers and joint M,V,Q,P packages. Over C, an admitted whole inverse is equivalent to necessary bijectivity; invertible Q_t observers are automatically Boolean. Local stabilizer conjugacy supplies reversible observers in the stated symmetry-model families. Internal Frege finiteness also gives exact affine representation by two-output pointwise homomorphisms, separately for XOR and biconditional. Finite-image material affine separation has the same normalization without finiteness of the domain. Plenitude at (t,t), stated explicitly over H, normalizes all seven nonempty primitive connective signatures, each affine operation, and the verified matching lattice/quantifier packages, including infinite-image observers. Full qualified right-inverse separation is exactly Rev. Qualified left-inverse separation is strictly weaker even with C5 and its own boxed schema; it implies OS, but not C5, ☐OS, its own boxed schema, ☐BF or ☐Functionality. The ternary Cantor model satisfies the separate endpoint-fixing M/Q/P, V/Q/P and N/Q/P separation schemas and their boxes, together with C and boxed BF and Functionality, while even propositional Boolean separation fails. Both arrows Rev ⇒ SplitMono ⇒ OS are strict. The full fork satisfies ☐OS and all boxed BF and Functionality but fails SplitMono, so SplitMono and ☐OS are incomparable. Under internal Fin_t(All), full SplitMono, Rev and endpoint separation coincide. Over H plus the preorder Zorn instance at tt, every admitted partial Boolean-group truth character extends, and material affine separation is exactly the relevant group equations with the stated endpoint alignments. Under Plenitude at (t,t), material negation separation and each separate material affine separation are equivalent to pointwise involutive separation, fixing the endpoints mentioned by the qualification; whole identities retain local Functionality or full typed scope. The component-shift symmetry model satisfies C5 + ☐SplitMono + No Pure Contingency but not Rev. Rev further implies noncontingency for pure formulas with finitely many individual parameters and endpoint-valued first-order relation parameters. Zorn at tt also supplies admitted prime filters and extension of admitted partial lattice truth characters over H; material joint lattice and Boolean separation have exact algebraic converses under this explicit premise, with the stated endpoint alignments and derived operations. Over bare H, joint negation/affine material separation is exactly affine separation plus the translation identity ¬x=x+c, c=¬0. Joint XOR/biconditional separation is exactly XOR separation plus the corresponding translated-operation identity. Under the actual expansion X=¬D, all three two-operation material packages agree with the three-operation package; Plenitude supplies pointwise involutions for the linked signatures. Over C + BF, at each finite list Δ containing t and relational output type τ, SplitMonoSep(τ,Δ) is equivalent to RevSep(τ,Δ) or [OS(τ,Δ) and KΔ], where KΔ asserts one admitted qualified pair F∘E=I and a true c with Fc=Bottom. The full-H form is full OS plus the external schema RevSep(t,Δ) or KΔ. The condition D_t that every admitted injective E:tt is onto makes full SplitMono and Rev equivalent. It is strictly weaker than internal Frege finiteness: a two-colour finite-pinning model satisfies C5 + Rev + D_t with atomless propositions, while endpoint separation and internal Frege finiteness fail. Over H, endpoint separation is equivalent to OS + Plenitude at (t,t), OS + full Plenitude, C5 + OS + Actuality, C5 + OS + Boolean Completeness, and C5 + Atomicity (type t). Already C + BF (type t) + Plenitude at (t,t) is equivalent to C5 + Actuality. Over C5, each currently surjective Good observer at a finite list containing t has a definable admitted same-list qualified right inverse; hence Rev is equivalent over H to C5 + full surjective logical separation. Both chains Rev ⇒ SurjSep ⇒ OS and Rev ⇒ SplitMono ⇒ OS are strict. SurjSep and SplitMono are incomparable even over C + ☐BF + ☐OS, witnessed by the full omega-chain and the C5 finite-block model. Within C5, SurjSep is Rev and does imply SplitMono. The linear/circular fibre model satisfies C5 + ☐OS + D_t with atomless propositions but fails SplitMono at the explicit propositional list {t,e,et,eet,(et)t,((et)t)t}; a contingent closed pure sentence about infinite amorphous cells proves the obstruction. For an admitted group G of whole meet automorphisms over H, its common truth-profile relation is the largest admitted invariant truth-compatible equivalence and is a meet congruence; separation is exactly the absence of a nontrivial such congruence. On chains the obstruction is convex. An admitted order-primitive action on the interior of a bounded dense chain, together with an interior true/false pair, gives reversible meet separation. The rational-chain full-function model has joint reversible meet/join separation and all Functionality while C fails, with no atoms or truth extrema. Order primitivity is strictly weaker than order 2-homogeneity for admitted actions. A specified countably infinite sequence fixed by a source symmetry group in the all-bijections finite-pinning framework gives one qualified left-inverse pair with a true kernel element, normalizing ordinary separators at that source. At the trivial-symmetry object of the qualitative-contrast model, C5 + SplitMono holds but ☐OS and ☐SplitMono fail. Thus SplitMono and ☐OS are incomparable even over C5. Every full cancellative-monoid action model with singleton individuals satisfies separately boxed full SurjSep. A specified infinite sequence of distinct units also gives separately boxed full SplitMono, with one common qualified left inverse. A nonunit refutes C5. The concrete monoid ℤ×ℕ therefore refutes ☐SurjSep + ☐SplitMono ⇒ Rev, even over C + ☐BF. SurjSep + SplitMono lies strictly below Rev and strictly above each factor; its two witness families may be different. Over H, a bounded meet chain with a greatest false and a least true proposition and a specified admitted whole-meet automorphism group G has S[G] exactly when every nontrivial interval contains an adjacent pair and G is transitive on adjacent pairs. Plenitude at (t,t) plus Q_t/P_t supplying the admitted order bounds gives that truth cut, without C or Functionality. The full-function complete split interval is atomless and satisfies full reversible endpoint-fixing M,V,Q_Δ,P_Γ separation for every finite list while C fails; its observers need not preserve negation. For a specified admitted invariant convex block relation on the interior of a bounded dense chain, with each block without endpoints, global separation is exactly one crossed block, transitivity on blocks and separation by its admitted stabilizer. For a specified external finite central partition of a bounded distributive lattice preserved by G, global separation is exactly transitivity on factor units and stabilizer separation inside the unique true factor. Lexicographic rational-chain and finite-product atomless models give joint reversible M/V separation with all Functionality below C. Over C + BF (type t), Onto(E) implies ☐Onto(E), with E a free parameter; Good qualification is persistent over C. Full SurjSep nevertheless gives neither ☐OS nor ☐SurjSep, even with ☐BF and ☐Functionality. A root truth-profile extension of a fixed/free symmetry tail supplies this countermodel, with failure already at the future propositional Boolean instance. Thus Rev ⇒ ☐SurjSep ⇒ SurjSep and ☐SurjSep ⇒ ☐OS are strict. SurjSep does not imply ☐BF, with failure at every admitted type in the integer-shift predecessor model. Over C5, every admitted Good-{t} observer E has admitted order adjoints L ⊣ E ⊣ R, with Rq=∃p[(Ep≤q)∧p] and Lq=¬R(¬q). With k=RBottom and a=¬k, R(Ep)=p∨k and L(Ep)=p∧a, giving a Boolean order isomorphism from [Bottom,a] onto the admitted image. Injectivity is equivalent to RBottom=Bottom or LTop=Top; onto is equivalent to join preservation by R or meet preservation by L; bijectivity is equivalent to R=L or negation preservation by either adjoint. The admitted image floor ER and ceiling EL are idempotent, with ER≤I≤EL and mutual absorption. ER is an auxiliary S5 interior and equals native Box exactly when E is endpoint-valued. The endpoint-fixing envelopes T−q=(a∧Rq)∨(k∧q) and T+q=Lq∨(k∧q) preserve M/all Q and V/all P respectively, and coincide exactly when E is onto. Already for a Boolean E over C5, commuting with native Box or Diamond is exactly injectivity, without Q_t. The integer-shift predecessor model satisfies C + full typed SurjSep + BF while ☐BF_σ fails at every admitted type σ. In the finite-pinning tail over ℕ×ℤ and {∗}×ℤ, split epimorphisms approximate finite pins and invertible integer translations supply prescribed-coordinate kernel pairs. The root truth-profile extension combines all-type evaluation readers with those onto tails. A future object has nononto transport at every type and refutes every BF instance. Hence SurjSep ⇒ ☐BF is refuted with exact all-type scope. Full BoxSep restricts Good separators by the whole native-modality identity E∘Box=Box∘E; InjSep instead requires current injectivity. Over H, BoxSep gives C + OS + ☐BF + ☐Functionality + .2. Locally over C, BF_σ + BoxSep(t,Δ) gives ☐BF_σ when {σ,σt}⊆Δ. The .2 consequence needs only propositional separation by Bottom-fixing observers commuting with native Box, without Boolean or quantifier laws. Over C5, BoxSep(τ,Δ) is equivalent to InjSep(τ,Δ) at the same list, and Rev ⇒ InjSep=BoxSep ⇒ OS has both implications strict. Over C+BF, BoxSep is incomparable with InjSep and SplitMono; over C+☐BF it is incomparable with ☐OS. It implies neither C5 nor its own necessary schema. The linear/circular model refutes the entire converse OS+☐BF+☐Functionality+.2 ⇒ BoxSep. For an arbitrary admitted E over C, ☐Inj(E) is equivalent to an admitted unqualified whole left inverse; the description D_E(q)=∀p[(Ep=q)→p] supplies it without BF or Choice. Current injectivity does not suffice outside C5, even for an individually full-Good observer with necessary BF. Over C5, fix injective Good_Δ E with t∈Δ and admitted adjoints L⊣E⊣R. Put C_E=E∘L. Qualified left inverses F correspond bijectively to admitted propositions u satisfying C_E(u)=Top and ∀q[u∧C_E(u∧q)=u∧q], via F_u(q)=L(u∧q) and u_F=¬k_F. The proof uses Frobenius L(q∧Ep)=Lq∧p and the Boolean isomorphism p↦u∧Ep onto [Bottom,u], with all admitted quantifier laws. No Choice or external completeness is assumed. The full-function C5 model on 2×RO(Cantor²) has an injective all-type Good cylinder embedding with no qualified Good-t left inverse, although its admitted adjoints are unqualified left inverses. This model fails OS(t,{t}); it does not refute InjSep⇒SplitMono. The separation comparison remains unresolved generally and over C5. IdemBoxSep adds the whole identity E∘E=E to BoxSep. Over H, IdemBoxSep⇒BoxSep is strict, C5+IdemBoxSep is equivalent to Extensionality, and IdemBoxSep is incomparable with Rev and End; either conjunction with IdemBoxSep is Extensionality. In a full model with singleton individuals on a finite rooted poset P, Boolean observers are exactly inflationary coordinate maps E_f=f⁻¹; native-Box commutation is f[↑x]=↑f(x), and idempotence is f²=f. An idempotent native-Box reader of a is exactly x↦x∨a. Thus full IdemBoxSep holds exactly when P is a join-semilattice, and then holds necessarily. In the four-level family root<A_m<B_n<top, for positive finite m,n, BoxSep iff m=1 or n≤m, while IdemBoxSep iff m=1 or n=1. P_{2,2} gives strictness; P_{2,3} refutes BoxSep despite ☐OS+☐BF+☐Functionality+☐Atomicity_t+☐.2. The diamond has ☐IdemBoxSep but fails .3 and C5. A singleton root below a terminal two-point cluster has current IdemBoxSep but fails its boxed schema. Over C5, for each relational τ and finite Δ containing t, InjSep(τ,Δ) iff RevSep(τ,Δ) or (OS(τ,Δ) and J_Δ). J_Δ asserts one admitted injective Good_Δ E and one currently true c with R_Ec=Bottom, equivalently ∀p(Ep≤c→p=Bottom). The Boolean patch (c∧Gp)∨(¬c∧Ep) normalizes every ordinary G to an injective Good observer while preserving its entire current truth profile. The reverse alternative uses an admitted local interval involution, without treating L_E as globally Good. K_Δ implies J_Δ. Under C5, same-observer quantifier reduction and Functionality reduce full OS, InjSep, Rev and SplitMono to their single propositional Good-{t} instances. Consequently full InjSep iff Rev or (OS and J_{t}), and full SplitMono iff Rev or (OS and K_{t}), as genuine finite disjunctions. The open C5 comparison is exactly whether OS+J_t forces Rev or K_t; that separation implication remains open, while J_t⇒K_t alone is refuted by the regular-open model, which fails OS. The general C+BF decomposition retains its finite-list schema. Over C+BoxSep(t,{t}), A→☐A holds for every finite universally closed parameter-free Boolean/native-modal sentence A=∀p̄ θ(p̄), with quantifier-free θ. More generally it holds for ∀R̄ φ(R̄) in the specified equality-free first-order modal fragment: predicate heads are only the outer variables, applied only to object-variable tuples; inner object quantifiers may be universal or existential at any admitted type, but object variables are not bare asserted propositions. Δ includes every outer predicate type and inner binder type. No inner quantified predicate head or other predicate constant is allowed. This gives the finite BF reflection and conditional .3→☐.3 and 5→☐5, not .3 or 5. Unconditional C equivalence transfers the theorem to equivalent modal-algebra statements. Arbitrary ∀p∃q with q asserted as a proposition is outside the theorem. C+BF_t+.2 already implies ☐.2. A four-point root/singleton/two-point-cluster model has C+☐OS+☐BF+☐Functionality and current ∀p(☐◇p→◇☐p) but not its necessity; it fails .2, so it does not separate reflection from the entire lower bundle. For each fixed external r≥1, B_r adds E^(r+1)=E^r to the native-Box logical qualification. B_1 is IdemBoxSep, and B_1⇒B_2⇒…⇒BoxSep has every successive implication strict; each fixed B_r strictly implies BoxSep. The separately boxed hierarchy is strict too. P_{3,2} witnesses the first step; for r≥2, a root followed by r two-point antichains and a top has ☐B_{r+1} but not B_r. On P_{m,n}, B_2 iff m=1 or n=1 or m>n; B_3 iff BoxSep. All witnesses retain C+☐OS+☐BF+☐Functionality+☐Atomicity_t+☐.2. One infinite frame with countably many two-point antichains and a common top has ☐BoxSep but fails every fixed B_r, witnessed by the same proposition pair. An admitted Q_t diagonal excludes all nonprincipal observer characters, extending the coordinate-reader and IdemBoxSep/join criteria to rooted posets of fixed finite external width. For every fixed r, C5+B_r, Rev+B_r and End+B_r are exactly Extensionality; B_r is incomparable with Rev and End. Over C5 and each fixed external n≥0, FG_n(E) says that the Boolean image of E plus n admitted propositions generates the ambient proposition algebra. A Good observer with a currently true local Boolean transversal has a qualified involution with its entire current truth profile, without an injectivity premise. FG_n supplies such a transversal, so separation by Good+FG_n observers is exactly Rev, at fixed τ,Δ containing t and at full scope with C5 retained; adding injectivity leaves the equivalence unchanged. For an individual injective FG_n observer, the controlled selector gives a qualified left inverse and can make Fc=Bottom whenever R_Ec=Bottom. Consequently K_Δ is exactly J_Δ with a one-generator image extension, equivalently J_Δ with FG_n for any fixed n≥1. J is an admitted relative logical embedding into a currently false principal interval; K is the corresponding relative logical isomorphism with an admitted inverse. The unchanged full-function C5 model on 2×RO(Cantor²) refutes J⇒K. Its clopen-partition embedding witnesses J and even has a qualified left inverse, but that inverse has a false greatest kernel, and every Good-t observer preserves current truth, ruling out K. OS fails in the same model, so OS+J_t⇒Rev∨K_t and InjSep⇒SplitMono remain open. The displayed embedding fails every fixed FG_n condition. The full exterior-arm poset A_{m,n} always has B_2 at its root. Its future P_{m,n} cone gives exact thresholds: ☐B_2 iff m=1 or n=1 or m>n; for fixed r≥3, ☐B_r iff ☐BoxSep iff m=1 or n≤m. A_{2,2} has B_2+☐B_3 but not ☐B_2. The single ten-point A_{2,3} has B_2 but not ☐BoxSep, and B_r but not ☐B_r for every fixed r≥2, retaining C+☐OS+☐BF+☐Functionality+☐Atomicity_t+☐.2. B_1 is hereditary within full finite-width poset models by the join criterion, not in general preorder models. Over C5, every Good_Δ observer E, with t∈Δ, has admitted local-transversal support s_E=∃b(Loc_E(b)∧b), using an endpoint locality guard defined by whole unary identity. Locality is injection of L_E on [Bottom,b]. The support is the maximal region whose every nonzero part contains a nonzero local transversal. An admitted join is local exactly when every pair of its members has local union; directed admitted families glue. The exact laws are Loc_{F∘E}(b) iff Loc_F(b) and Loc_E(L_F b), s_{F∘E}=s_F∧F(s_E), and s_G=(d∧s_E)∨(¬d∧s_F) for the Boolean patch G=dE∨¬dF. N(E)(p)=(s_E∧Ep)∨(¬s_E∧p) retracts the Good class onto its composition-closed support-Top subclass. Separation by full-support observers, by true-support observers, or by the admitted range of N is exactly Rev over C5 at fixed and full scope. No injectivity is assumed. Full support is strictly broader than each fixed FG_n for individuals and need not itself be local or imply an individual inverse. Under the additional current unboxed premises C5+BC_t+Zorn_t, any Good E and proposition r admit a maximal local u≤r with L_Eu=L_E(s_E∧r). BC_t supplies actual joins of current chain members; C_E is left adjoint to ER_E, so compatible locality survives those joins; Zorn_t supplies maximality. With injection added, a qualified left inverse exists iff L_Es_E=Top, and one killing a prescribed c exists iff L_E(s_E∧¬c)=Top. Thus K is exactly an injective Good observer with a currently true c and this controlled support coverage. A J witness with full support gives K under these premises, but J alone only gives L_E¬c=Top. Neither optional premise is necessitated, and no uniform choice is claimed. Over C5, TrueHom means that a currently true principal interval admits relative order isomorphisms to all its nonzero principal subintervals, with admitted inverses. Those witnesses preserve every requested quantifier. TrueHom implies Actuality or K; the atomic branch plus OS gives End and Rev, while the nonatomic branch gives a false-interval isomorphism and true-kernel inverse pair. Consequently C5+OS+TrueHom implies SplitMono without J. An admitted homogeneous cover with join Top suffices for TrueHom. External homogeneity alone does not. This sufficient condition does not resolve the general OS+J⇒Rev∨K question. Over C5, for every fixed external n≥1, Deg_n(E) says that n+1 disjoint propositions have L_E-images with zero common intersection. For arbitrary Good_Δ E with t∈Δ, without injection, this implies full local support and an admitted qualified involution with the same entire current truth profile. Degree-bounded separation is exactly Rev at fixed and full scope; degree one is exactly surjectivity. Degree bounds multiply under composition and add under Boolean patching. Under the additional current BC_t+Zorn_t premises, degree at most n is exactly a partition of Top into n local transversals, allowing zero sheets. FG_k implies Deg_{2^k} over C5 alone, and the reverse holds with BC_t+Zorn_t. All bounds are fixed external integers, not finite range or an internal quantifier over finite bounds. For every fixed relational τ and finite Δ, over C, Actuality+FinBoxSep(τ,Δ) iff Fin_t(All)+BoxSep(τ,Δ), with no t∈Δ, BF, Functionality, C5 or Choice added. FinBoxSep requires internally Frege-finite image of the same Good/native-Box observers. An observer accepting an actual world has identity's current truth profile; native-Box commutation makes it injective, and internal finite-preimage induction gives finite All. Conversely finite image induction and a finite true-meet fold give the other direction and Actuality. Full schema scope recovers C over H. In every full set-sized rooted-poset action model with singleton individuals, FinBoxSep iff the frame is finite and BoxSep holds, at arbitrary width; no infinite-width observer classification is used. Cent_Δ(E) means Good_Δ E and whole commutation with every admitted same-list Good G. Over C with unary Functionality, Boolean patches force idempotence. Over C5+S_{t,Δ}, t∈Δ, a central observer is identity or an endpoint observer with a currently true greatest kernel, with at most one nonidentity possibility. Central separation excludes that possibility using its true atomic kernel and the corresponding endpoint observer. Thus C5+CentreSep is exactly Extensionality, already from its propositional instance with t∈Δ. Full CentreSep+Rev and CentreSep+End also equal Extensionality. CentreSep is incomparable with Rev and End over H: a two-point chain has ☐CentreSep but fails C5, while a two-point S5 cluster has Rev and End but not CentreSep. In full finite rooted-poset models with singleton individuals, the centre is identity plus the constant-top map when top exists, so CentreSep holds exactly on a singleton or two-point chain. This is not merely a chosen pairwise commuting family or an abstract H classification. The unchanged atomless two-colour finite-pinning model additionally has ☐BC_t with C5+☐Rev+D_t, but fails Actuality, End, BC_tt and Zorn_t. Actual joins of stabilizer orbits are their finite fixed-pin projections, and finitely many such projections join the current extension of any admitted predicate. An admitted preorder of finite colour-coordinate joins refutes the single Zorn_t instance: finite pins bound all admitted antisymmetric chains, but fresh coordinates prevent maximal elements. The model therefore does not refute any conclusion with BC_t and Zorn_t jointly added. The exact type specialization of the recorded completeness proof gives C5+BC_tt⇒Plen_{t,t}⇒Actuality; with OS it gives End. Over C5, S_{t,Δ}+BC_σ implies ☐BC_σ when Δ contains σ and σt. Observers fix endpoint order judgments and postcompose the family predicate; current completeness and separation then identify BC_σ with Top. The C5 Good-t reduction permits the single S_{t,{t}} instance and full OS. This reflects each assumed instance, not a lift from BC_t to higher completeness. Over C5, full Rev is equivalent to the single finite sentence that only Bottom and Top are fixed by every reversible Good-t observer. The admitted join of reversible images is the least invariant proposition above an input. The same invariants are exactly the propositions respected by every logical observer on its local-transversal support, equivalently fixed by every support-normalized observer. Over H, full CentreSep is exactly IdemBoxSep plus at most four proposition objects and is equivalent to its separately boxed schema. Separation by the centre of the reversible logical group is exactly C5 plus the same four-proposition bound, is persistent, and is incomparable with CentreSep; their conjunction is Extensionality. For fixed external n≥1, Rev plus the whole identity E^n=I for every reversible Good-t observer is exactly C5 plus at most 2^k propositions, where k is the largest integer such that each of 1,…,k divides n. Finite common refinement supplies admitted cycles of each prescribed finite length. Full FinBoxSep is equivalent over H to BoxSep plus internal Frege finiteness of all propositions, and implies Actuality and necessary finiteness. Over C the fixed-instance equivalence needs any relational type in the finite qualification list; empty and individual-only lists remain unresolved without Actuality. C5 or Rev together with FinBoxSep is exactly End plus internal finiteness. FinBoxSep does not imply its boxed schema even with necessary global finiteness, as witnessed by the finite exterior-arm model. For every fixed nonempty reduced group word w, H+Rev+Law_w is exactly C5+AtMost_(2^k(w))(t), equivalently End plus that bound, where k(w) is the largest j for which Sym(j) satisfies w and 1≤k(w)≤length(w). Commutativity gives four propositions and the metabelian word gives eight. Over C5 without Rev, Law_w is exactly the condition that no k(w)+1 disjoint propositions have invariant orbit joins with nonzero common meet. Finitely many targets admit common reversible nonzero refinements exactly when their orbit joins overlap; finite invariant localization proves the converse group-law direction without Choice, BC or Zorn. Over H, an internally Frege-finite admitted observer family separating an admitted proposition class makes that class internally finite. The independent finite-table theorem counts admitted functions on finite input/output predicates under an identifying evaluation premise; Functionality supplies that premise for a full input domain. H+Rev+Fin_tt(Aut_Good_t), C5+FinAll, End+FinAll and C5+FinBoxSep are equivalent. Full finite-family ordinary logical separation is OS+FinAll; its reversible version is C5+FinAll; its native-Box version is FinBoxSep.

**Lean certified:** The foundational implication H + OS ⇒ C + BF, with explicit endpoint identities.

**Proofs:** [GRAPH.md](proofs/h-observer-space/GRAPH.md) · [MAP.md](proofs/h-observer-space/MAP.md) · [README.md](proofs/h-observer-space/README.md) · [finite-affine-separation.md](proofs/h-observer-space/finite-affine-separation.md) · [fork-without-binary-families.md](proofs/h-observer-space/fork-without-binary-families.md) · [identity-collapse.md](proofs/h-observer-space/identity-collapse.md) · [local-tiers-and-models.md](proofs/h-observer-space/local-tiers-and-models.md) · [observer-restrictions.md](proofs/h-observer-space/observer-restrictions.md) · [primitive-package-classification.md](proofs/h-observer-space/primitive-package-classification.md) · [quantifier-generated-lattices.md](proofs/h-observer-space/quantifier-generated-lattices.md) · [relational-clone-model.md](proofs/h-observer-space/relational-clone-model.md) · [representation-under-identity-bivalence.md](proofs/h-observer-space/representation-under-identity-bivalence.md) · [reversible-meet-atomicity.md](proofs/h-observer-space/reversible-meet-atomicity.md) · [term-closure-and-affine-branches.md](proofs/h-observer-space/term-closure-and-affine-branches.md) · [truth-profiles-and-connective-reducts.md](proofs/h-observer-space/truth-profiles-and-connective-reducts.md) · [two-orders-model.md](proofs/h-observer-space/two-orders-model.md) · [typed-separation-and-classicism.md](proofs/h-observer-space/typed-separation-and-classicism.md) · [reversible-meet-characterization.md](proofs/h-observer-space/reversible-meet-characterization.md) · [finite-semilattice-normalization.md](proofs/h-observer-space/finite-semilattice-normalization.md) · [composition-closed-characterization.md](proofs/h-observer-space/composition-closed-characterization.md) · [finite-image-material-normalization.md](proofs/h-observer-space/finite-image-material-normalization.md) · [logical-separation-with-contingent-barcan.md](proofs/h-observer-space/logical-separation-with-contingent-barcan.md) · [necessary-separation-and-atoms.md](proofs/h-observer-space/necessary-separation-and-atoms.md) · [reversible-separation-and-pure-truth.md](proofs/h-observer-space/reversible-separation-and-pure-truth.md) · [finite-block-symmetry-reversible-gap.md](proofs/h-observer-space/finite-block-symmetry-reversible-gap.md) · [necessity-of-distinctness-representation.md](proofs/h-observer-space/necessity-of-distinctness-representation.md) · [reversible-quantifier-observers.md](proofs/h-observer-space/reversible-quantifier-observers.md) · [local-conjugacy-and-reversible-observers.md](proofs/h-observer-space/local-conjugacy-and-reversible-observers.md) · [finite-affine-normalization.md](proofs/h-observer-space/finite-affine-normalization.md) · [split-inverse-logical-observers.md](proofs/h-observer-space/split-inverse-logical-observers.md) · [plenitude-material-normalization.md](proofs/h-observer-space/plenitude-material-normalization.md) · [finite-block-symmetry-left-inverse.md](proofs/h-observer-space/finite-block-symmetry-left-inverse.md) · [ternary-cantor-observer-model.md](proofs/h-observer-space/ternary-cantor-observer-model.md) · [fork-one-sided-inverse-separation.md](proofs/h-observer-space/fork-one-sided-inverse-separation.md) · [zorn-affine-character-extension.md](proofs/h-observer-space/zorn-affine-character-extension.md) · [partial-reversible-normalization.md](proofs/h-observer-space/partial-reversible-normalization.md) · [component-shift-symmetry-reversible-gap.md](proofs/h-observer-space/component-shift-symmetry-reversible-gap.md) · [zorn-lattice-character-extension.md](proofs/h-observer-space/zorn-lattice-character-extension.md) · [negation-affine-compatibility.md](proofs/h-observer-space/negation-affine-compatibility.md) · [left-inverse-separation-decomposition.md](proofs/h-observer-space/left-inverse-separation-decomposition.md) · [finite-pinning-dedekind-propositions.md](proofs/h-observer-space/finite-pinning-dedekind-propositions.md) · [plenitude-endpoint-bridge.md](proofs/h-observer-space/plenitude-endpoint-bridge.md) · [surjective-logical-observers.md](proofs/h-observer-space/surjective-logical-observers.md) · [linear-circular-fibre-left-inverse-gap.md](proofs/h-observer-space/linear-circular-fibre-left-inverse-gap.md) · [omega-chain-surjective-observers.md](proofs/h-observer-space/omega-chain-surjective-observers.md) · [reversible-semilattice-order-actions.md](proofs/h-observer-space/reversible-semilattice-order-actions.md) · [fixed-point-symmetry-left-inverse-separation.md](proofs/h-observer-space/fixed-point-symmetry-left-inverse-separation.md) · [full-cancellative-monoid-observers.md](proofs/h-observer-space/full-cancellative-monoid-observers.md) · [reversible-truth-gap-chains.md](proofs/h-observer-space/reversible-truth-gap-chains.md) · [reversible-semilattice-local-global.md](proofs/h-observer-space/reversible-semilattice-local-global.md) · [root-truth-profile-surjective-separation.md](proofs/h-observer-space/root-truth-profile-surjective-separation.md) · [canonical-adjoints-and-image-factorization.md](proofs/h-observer-space/canonical-adjoints-and-image-factorization.md) · [integer-shift-predecessor-contingent-barcan.md](proofs/h-observer-space/integer-shift-predecessor-contingent-barcan.md) · [native-box-logical-observers.md](proofs/h-observer-space/native-box-logical-observers.md) · [injective-observers-and-boolean-transversals.md](proofs/h-observer-space/injective-observers-and-boolean-transversals.md) · [idempotent-native-box-observers.md](proofs/h-observer-space/idempotent-native-box-observers.md) · [injective-separation-decomposition.md](proofs/h-observer-space/injective-separation-decomposition.md) · [native-box-reflection.md](proofs/h-observer-space/native-box-reflection.md) · [bounded-stabilization-native-box-observers.md](proofs/h-observer-space/bounded-stabilization-native-box-observers.md) · [finite-relative-image-generation.md](proofs/h-observer-space/finite-relative-image-generation.md) · [injective-gap-without-split-kernel.md](proofs/h-observer-space/injective-gap-without-split-kernel.md) · [exterior-arm-posets-native-box-nonpersistence.md](proofs/h-observer-space/exterior-arm-posets-native-box-nonpersistence.md) · [local-transversal-support.md](proofs/h-observer-space/local-transversal-support.md) · [zorn-local-transversal-selection.md](proofs/h-observer-space/zorn-local-transversal-selection.md) · [local-homogeneity-and-split-observers.md](proofs/h-observer-space/local-homogeneity-and-split-observers.md) · [bounded-fibre-degree-logical-observers.md](proofs/h-observer-space/bounded-fibre-degree-logical-observers.md) · [finite-image-native-box-observers.md](proofs/h-observer-space/finite-image-native-box-observers.md) · [central-logical-observers.md](proofs/h-observer-space/central-logical-observers.md) · [finite-colour-propositional-completeness.md](proofs/h-observer-space/finite-colour-propositional-completeness.md) · [reversible-fixed-proposition-characterization.md](proofs/h-observer-space/reversible-fixed-proposition-characterization.md) · [central-separation-and-four-propositions.md](proofs/h-observer-space/central-separation-and-four-propositions.md) · [finite-image-box-reflection.md](proofs/h-observer-space/finite-image-box-reflection.md) · [centre-of-reversible-logical-observers.md](proofs/h-observer-space/centre-of-reversible-logical-observers.md) · [invariant-components-and-local-support.md](proofs/h-observer-space/invariant-components-and-local-support.md) · [bounded-exponent-reversible-observers.md](proofs/h-observer-space/bounded-exponent-reversible-observers.md) · [group-identities-reversible-observers.md](proofs/h-observer-space/group-identities-reversible-observers.md) · [invariant-components-and-group-identities.md](proofs/h-observer-space/invariant-components-and-group-identities.md) · [internally-finite-observer-families.md](proofs/h-observer-space/internally-finite-observer-families.md)

**Scoped evidence:** [`H-OBSERVER-SPACE`](evidence/RESULT-INDEX.md#h-observer-space)

<a id="synthesis.intrinsic-observer-axioms"></a>
## synthesis.intrinsic-observer-axioms

Over H, full typed endpoint separation together with unboxed infinitary range comprehension at every original input type characterizes the full standard relational hierarchies among set-sized models, up to canonical typed representation. The representation is provable in ZF. Range comprehension permits arbitrary set-indexed parameter families under every simultaneous assignment. Over H + endpoint separation, it gives the same original typed reducts as External Comprehension, Arbitrary Atomic Joins, external Boolean completeness, or the larger boxed Infinitary Comprehension presentations.

**Proofs:** [intrinsic-observer-axioms.md](proofs/intrinsic-observer-axioms.md) · [logical-observer-hierarchy.md](proofs/logical-observer-hierarchy.md) · [typed-separation-and-classicism.md](proofs/h-observer-space/typed-separation-and-classicism.md) · [infinitary-canonical-representation.md](proofs/infinitary-canonical-representation.md)

**Scoped evidence:** [`INTRINSIC-OBSERVER-AXIOMS`](evidence/RESULT-INDEX.md#intrinsic-observer-axioms)
