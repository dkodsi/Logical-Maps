# Models interpreted by logical observers

[Logical-observer guide](../classicism-results-2026-10-24-v2/LOGICAL-OBSERVERS.md#mathematics-through-observers) · [Integration register](README.md)

A logical observer can define another interpretation of the same typed language. Normalize the objects at each type using the observer, then identify normalized objects that no normalized predicate distinguishes in current truth. The resulting model is called its **core** in the proofs below. This construction uses admitted objects and predicates; it need not produce a full standard hierarchy.

## Construction and preservation

Let E be an admitted logical observer satisfying the whole identity E∘E = E. It preserves Boolean operations and every typed quantifier as whole operations. The all-type qualification describes one observer in the model; it is not a quantifier over types in the object language.

Over C, this interpretation always gives another model of C. Neither BF nor C5 is required. Functional Choice descends in both its current and necessary forms. For each permitted Functional Choice instance F and each relational type τ,

```math
\begin{aligned}
M\models\Box F&\quad\Longrightarrow\quad\mathrm{Core}(M,E)\models\Box F,\\
M\models\Box\mathrm{BC}_\tau&\quad\Longrightarrow\quad\mathrm{Core}(M,E)\models\Box\mathrm{BC}_\tau.
\end{aligned}
```

The completeness proof establishes the stronger comparison

```math
E(\mathrm{BC}_\tau)\le (\mathrm{BC}_\tau)^r,
```

where the right side is the normalized formula before quotienting. The order in the interpreted model is itself interpreted; it need not be the ambient order. [General construction and Functional Choice](proofs/observer-quotient-general.txt), §§1–7; [necessary completeness](proofs/observer-completeness-descent.txt), §§1–6. The [Functional Choice proof](proofs/observer-choice-preservation.txt), §§1–7, similarly establishes E(F) ≤ Fʳ. It uses a discharged C theorem with stable identity premises; it does not identify the interpreted modality with the original one.

## Commuting interpretations

If E and F are commuting idempotent logical observers, both qualified at every type, interpreting through E and then through the induced observer F̄ agrees with interpreting through E∘F:

```math
\mathrm{Core}(\mathrm{Core}(M,E),\overline F)\cong\mathrm{Core}(M,E\circ F).
```

This holds over C, retaining the quotient at every type. Finite iterations are independent of order and grouping; BF, Functionality and Choice are not required. [Proof](proofs/coherent-observers/iterated-cores.txt), §§2–5.

## Every model has a proper realization

Every pointed set-sized general C model K is isomorphic to the interpretation defined by a proper idempotent logical observer in another general C model M. The specified signature and individuals are preserved, and M's proposition algebra is the product of two copies of K's proposition algebra:

```math
\mathrm{Core}(M,E)\cong K,\qquad
\mathrm{Im}(E)\subsetneq D_t^M,\qquad
D_e^M=D_e^K,\qquad B_M\cong B_K\times B_K.
```

All higher objects are coded using objects already admitted in K. The construction preserves full Boolean Completeness and, separately, its necessary form. **Every model of C + ☐Functional Choice has a proper realization within C + ☐Functional Choice**, with the same signature, individuals and doubled proposition algebra. The [Choice construction](proofs/observer-choice-realization.txt), §§1–8, needs neither Infinity nor full function domains. Instancewise it uses BC at the translated type Tτ to obtain BC at τ, with T(e)=e, T(t)=tt and T(στ)=T(σ)T(τ); the same bound holds for the necessary instances. Properness concerns the observer's image, not abstract nonisomorphism of infinite models. [Complete construction](proofs/observer-proper-doubling.txt), §§1–8.

## Which current truths descend?

The positive transfer theorems have sharp limits.

| Ambient model | What the interpretation can lose |
| --- | --- |
| C5 + OS + ☐BF + Relational Choice + Transversal Choice | Relational Choice at (e,e) and Transversal Choice at e. [Finite-support countermodel](proofs/observer-choice-countermodel.txt). |
| C + OS + Strong Actuality + Zorn | Current BF. [Interpretation-root example](proofs/observer-action-realization.txt), §5. |
| C + Boolean Completeness + ☐BF + ☐OS | Boolean Completeness at t, even when the interpretation satisfies C5 + OS. [Countermodel](proofs/observer-current-completeness-countermodel.txt), §§1–7. |

Under C5, **Actuality + full Relational Choice** restores Relational Choice, Functional Choice and Transversal Choice in endpoint interpretations. [Proof](proofs/observer-actuality-choice.txt), §§1–4. The endpoint/C5 completeness theorem and the general necessary-completeness theorem retain their respective scopes.

Any set-sized family of pointed **C action models** can be realized as separate interpretations in a single model of OS + Strong Actuality + Zorn; the source may also satisfy pure Max(C). [Exact realization](proofs/observer-action-realization.txt), §§1–6. This family theorem keeps its action-model scope; the individual proper-realization theorem above covers arbitrary general/Henkin models.

## What determines the interpretation?

Over C + BF, two qualified idempotent observers with the same proposition image give isomorphic pure interpretations; named expansions need compatible interpretations of their constants. Full OS implies BF, so this positive result applies whenever OS holds. [Same-image theorem](proofs/observer-quotient-bf.txt), §6.

Without BF, even the pure theories can differ. A model with one individual and sixteen propositions has two truth-preserving idempotent logical observers with the same eight-element image. Their interpreted models disagree on whether some whole conjunction-preserving involution exchanges two distinct false atoms. The source and both interpretations satisfy ☐Boolean Completeness and ☐Atomicity at every relational type. The quotient identifies no distinct fixed objects, so quotient ambiguity does not explain the difference.

BFₜ fails in the source and both interpretations; this is not a counterexample to the positive OS result. [Countermodel and distinguishing sentence](proofs/observer-same-image-countermodel.txt), §§1–8.

These results extend the [C5 endpoint interpretation](../next-update/items/21-observer-classical-cores.md). The current Boolean Completeness transfer proved there retains its endpoint/C5 hypotheses; the general quotient theorem above concerns necessary completeness.

Mathematical arguments: OpenAI Codex, 26 October 2026 (`misc`). [Source provenance](SOURCE-MANIFEST.json) records the exact original and published proof hashes.
