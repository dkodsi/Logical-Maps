# Propositional probability needs only a local mathematical core

22 October 2026. Ordinary mathematical refinement by OpenAI Codex; direct source `misc`. No independent or formal verification claim. This further reduces the background of [choice-free faithful probability](choice-free-faithful-probability.md), refining the original [probability theorem](../notes/faithful-probability-countable-worlds.md).

## 1. Exact claim and witness convention

Assume only

    C + Actuality + Atomicity_t + Boolean Completeness_t
      + quantified Infinity_e.                              (A)

Then the Boolean algebra of all current propositions admits a faithful finitely additive probability iff its atom field has an admitted finite-fibre numerical labelling by N_e. Equivalently it admits a faithful countably additive, or represented-completely-additive, probability. Countable Choice for finite fields, if separately added in the interpreted mathematics, upgrades finite-fibre labelling to the original injection/countability criterion.

Probabilities here are **functional graphs with values in the actual-world core's Dedekind real codes**. This is the graph-coded convention permitted by the original probability note. Without Plenitude, we do not infer an ambient C operation representing every such graph. The theorem is current; its supporting world and real codes may collapse at a later point. It supplies the algebraic probability assertion in this specified local interpretation; it does not assert that a separately prescribed globally rigid real-code domain remains available under (A).

Under the old stronger background, the local and Gallin mathematical cores have the canonical current isomorphism proved in `gallin-extensional-core.md`, §8. Transport of real values and graph membership preserves the probability axioms. The local extension here preserves that current algebraic meaning while deliberately making no claim about the future interpretation of the codes.

No ND, BF, all-type Atomicity, all-type Boolean Completeness, Plenitude, or Choice is assumed. This is a theorem about the propositional event algebra. The higher-type atom factorization, type ceiling, and lifted logical world-symmetry statements in the other notes retain their stronger backgrounds.

The modal reduction is strict in the recorded evidence: a proved-only Engine query with exactly the four optional premises in (A), and no engine background, finds `full-two-object-chain-individuals-fixed-infinite` satisfying them while failing ND. Boxed Plenitude entails ND, so the weaker package does not recover it. This is the existing two-object-chain construction with the group's fixed-infinite-individual setting; no new model verdict is supplied.

## 2. A graph-coded core with both individuals and events

The existing [Actuality world-slice proof, §§1–3](../notes/actuality-world-slice-core.md) gives the key localization fact. For the unique actual world w, any two w-supported relations currently coextensive on the whole argument domain are literally identical. The true universal coextension lies above w by Actuality; outside w both relations vanish; Intensionality gives their identity. No BF is used.

To keep all current propositions as **events**, rather than mistaking them for the core's two truth values, use three target base sorts:

    individuals I: code type e, field H_I(x):=w;
    events A:      code type t, field H_A(p):=w;
    truth O:       code type t, field H_O(p):=w∧(p=⊥∨p=w).

They are distinct target sorts even when their code types coincide. The first two fields contain every current individual and every current proposition. The truth field contains just ⊥ and w. Every field predicate is w-supported.

For a target function type α→β, use the allowed C code type

    c(α→β) := c(α)c(β)t.

Its field consists of graphs G supported on w∧H_α(x)∧H_β(y) that are **currently** total and single-valued from H_α to H_β. Multiply the field predicate by w. Two such graphs for the same current function are currently coextensive and hence identical by localization. Thus target function equality is extensional identity of the admitted graph codes. No C operation with individual output is introduced.

All fields are currently nonempty. Fix one individual, the event ⊥, and the false truth value ⊥; a default in an arrow field is the w-supported constant graph at the already constructed codomain default. This is finite recursion on each target type from three fixed defaults, not an internal Choice principle.

### Term and quantifier closure

Translate a target term u to its current value relation Val_u(z). Variables use equality. An application f(v) has value z exactly when some function graph G and input y satisfy Val_f(G), Val_v(y), and G(y,z). The induction hypothesis and functionality of G give a unique value in the codomain field.

A lambda abstraction λx.u is represented by the C relation

    G(x,z) := w ∧ H_α(x) ∧ H_β(z) ∧ Val_u(z).

It is supported by construction and currently total and functional by the induction hypothesis. Localization identifies any two such graph representations, giving the target beta and extensionality laws. An individual-valued abstraction is handled by this same graph construction; it never asks for a forbidden ambient arrow.

Target formulas translate by restricting quantifiers to the corresponding H-fields and interpreting truth as the value w. A target predicate graph P is true at x exactly when P(x,w) holds. Its universal quantifier therefore has value w iff

    ∀x(H_α(x)→P(x,w)),

and value ⊥ otherwise. The w-supported graph of these two cases is admitted by comprehension and is currently functional. Equality and Boolean connectives have the analogous supported two-case or finite-table graphs. Every target comprehension instance is represented by its translated formula with the same support. This proves current Henkin closure, including quantification over newly coded function fields. It adds no external subsets or maps.

The use of current functionality is deliberate. There is no assertion that these fields stay inhabited or retain their members at successors where w fails.

## 3. The event algebra and its represented families

The Boolean event operations are the **ambient** operations on all current propositions: ⊥, ⊤, complement, conjunction, and algebraic order. Their target functional graphs are obtained by cutting the corresponding value equations by w and the field supports. C's Boolean identities give the current Boolean algebra laws. In particular the event unit is the ambient ⊤, whereas the core's logical true value is w; they are not being identified.

Atomicity_t transfers directly because the event field is all current propositions with inherited literal equality and order. For a represented family of events, its current image is an admitted ambient predicate on t: for a graph F from a represented index field J, use

    P(p) := ∃j(H_J(j)∧F(j,p)).

Boolean Completeness_t gives its join. The join is unique in the current Boolean algebra, so the interpreted join graph is supplied by comprehension. This checks completeness for every admitted family used by the probability proof. It does not require all-type BC or a future-domain closure assumption.

## 4. Numerical and real interpretation

The source world-slice construction transfers quantified Infinity_e to its core, without Choice. The graph presentation above gives the same extensional individual mathematics: a predicate graph X has the decoded ambient property

    X° := λx. w∧X(x,w).

Every ambient current individual-property extension occurs this way, by its supported truth-table graph. Deletion of a point has the expected current extension, and supported graphs agreeing currently are identical.

For clarity the number-transfer argument can be repeated directly in this presentation. Send an original finite cardinality n to the core cardinality graph whose truth on X is the current truth of n(X°). Supported comprehension supplies that graph. The zero and successor equations follow from their definitions and coextension-invariance of finite cardinalities. Pulling back inductive predicates shows that original numbers map to core numbers; the represented image predicate contains zero and is successor-closed, so core induction proves surjectivity.

Quantified Infinity_e realizes every original n at a current property. The [core-number injectivity argument](infinity-core-number-isomorphism.md#2-the-short-injectivity-argument) applies: normalize an instance of m, apply equality of the two core images, and use original finite-cardinality exclusivity to obtain m=n. Thus the original N_e and the interpreted Peano number field are bijective, with matching represented numerical subsets and graphs. The counting base has not been changed to an unrelated externally supplied N.

Internal rationals, finite sums and Dedekind cuts are now available by graph comprehension, arithmetic recursion and the same cut-union supremum construction described in [the choice-free probability proof, §2](choice-free-faithful-probability.md#2-why-the-internal-mathematics-is-available-without-functional-choice). Their values and comparisons are current core objects. Internal Archimedeanness is relative to N_e; no external standardness or countable Choice has entered.

## 5. Applying the algebraic proof

All hypotheses of the finite-budget proof are now verified inside this local interpretation:

* the event Boolean algebra is represented, atomic and complete;
* finite atom subsets, numerical labels, finite sums and the relevant graph families are admitted;
* the real suprema and Archimedean bounds are internal to the interpreted Dedekind construction.

A faithful finite charge gives the finite-fibre labelling

    a ↦ min {n>0 : μ(a)≥1/n}.

Conversely, a finite-fibre labelling ℓ gives positive weights 2^(−n−1)/|ℓ⁻¹(n)| on its nonempty n-fibres. Finite atom subsums satisfy the budget bound. Their represented supremum, normalized at ⊤, is faithful and completely additive. These are exactly the proved arguments in the preceding notes, with every interpretation hypothesis now supplied by (A). No new selection is hidden in their reuse.

## What was removed, and what was not

For this **local graph-valued propositional theorem**, boxed Plenitude has been replaced by its separately sufficient current resources Actuality, Atomicity_t, and Boolean Completeness_t. The graph construction above removes the need for ambient operation representation and for modal constancy of the mathematical domains. Quantified Infinity_e remains indispensable to the stated Peano/real interpretation. Actuality is still assumed, not derived from any choice/completeness principle. No global or higher-type conclusion has been transferred to the weaker package.

Sources: `actuality-world-slice-core.md`, §§1–5; `infinity-core-number-isomorphism.md`; `canonical-atomic-probability.md`, §§1–4; and `choice-free-faithful-probability.md`. These are unpaginated local notes. Background definitions are `actuality`, `atomicity-t`, `boolean-completeness-t`, and `axiom-of-infinity-e`, with their existing source attributions. The multi-base graph extension and the reduced probability package are proved here; the original core proof and database records are unchanged.
