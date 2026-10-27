# Results and certificate scope

Research submission: results, proofs and exact certificate scope.

[Main guide](MAIN-RESULTS.md) · [Exact evidence](evidence/RESULT-INDEX.md) · [Database reconciliation](DATABASE-INTEGRATION.md) · [Questions](CONJECTURES.md)

## Certified results

<a id="database-connections"></a>
### I. Resolved database questions and connections

- **Max + Atomicity (type t) ⇒ ⊥.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#max-atomicity).
- **Signature SP entails pure SP exactly when signature SP is inconsistent.** Lean certified: The signature-splitting lemma. [Proof and certificate](evidence/RESULT-INDEX.md#sp-signature-conflict).
- **Atomicity under C5 removes pure contingency.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#npc-atomicity).
- **Independence coexists with extensionality and strong Choice.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#signature-independence).
- **Choice and completeness produce Actuality and transversals.** Lean certified: RC + BC ⇒ TC; the sharp Actuality theorem, Actuality-based TC, and the same-type RC + BC and CBC + CCC consequences. [Proof and certificate](evidence/RESULT-INDEX.md#choice-completeness).
- **Logical Necessity and strong selection laws do not force Actuality.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#logical-necessity-separation).
- **Four rigidity principles coincide over ND and Boolean Completeness.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#rigidity-nd-bc).
- **ND and Boolean Completeness do not give Rigid Comprehension.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#oldnew-separation).
- **Strong Leibniz Biconditionals and Rigid Comprehension force modal stability.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#modal-propagation).
- **Rigidity has exact power, uniformization and algebraic descriptions.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#rigidity-classifications).
- **TR + RP does not imply WRP.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#finite-compression-separation).
- **Comprehension, completeness and choice do not force ☐Tame Rigidity.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#fixed-point-entrance).
- **Rigid Power at one type does not close the rigidity gap.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#colour-collapse-scope).
- **Canonical operations on coextension classes require Actuality.** Lean certified: Orbit averaging and finite code towers; orbit/Actuality equivalence at t and inhabited unary types. [Proof and certificate](evidence/RESULT-INDEX.md#coextension-operations).
- **Rigid Comprehension stabilizes a possible real structure.** Lean certified: Rigidification and simultaneous represented powers of every prescribed finite list of positive arities, at every closed admitted type and in arbitrary signatures. [Proof and certificate](evidence/RESULT-INDEX.md#analytic-rigidification).
- **Finiteness is classified by the base types occurring in a type.** Lean certified: Finiteness propagation, descent, and the exact classification by type. The four C5 base-infinity combinations and the stated two-stage model/finiteness/Functionality endpoints. [Proof and certificate](evidence/RESULT-INDEX.md#finite-type-propagation).
- **CH can vary despite boxed structural principles.** Lean certified: Opposite-CH components at type e and their coalesced C countermodel with ☐BF, constructed in Lean’s ambient metatheory. [Proof and certificate](evidence/RESULT-INDEX.md#ch-coalesced).
- **Maximalism is incompatible with Non-contingency of CH.** Lean certified: Maximalism + Non-contingency of CH ⇒ ⊥, using constructed type-e components in Lean’s ambient metatheory. [Proof and certificate](evidence/RESULT-INDEX.md#max-ch).

<a id="previously-known-results-formalized"></a>
#### Previously known results formalized

[Original attribution and certified scope](MAIN-RESULTS.md#previously-known-results-formalized).

- [C5 + Atomicity (type t) ⇒ No Pure Contingency](evidence/RESULT-INDEX.md#npc-atomicity)
- [C5 + ☐Rigid Comprehension ⇒ Second-Order Analytic Necessitism](evidence/RESULT-INDEX.md#analytic-rigidification)
- [Symmetric ideally-full model: old and new individuals](evidence/RESULT-INDEX.md#oldnew-separation)

<a id="established-principles"></a>
### II. Further results about established principles

- **Choice and Plenitude decompose into Actuality and inverse maps.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#sections-retractions).
- **C5 is exactly strong retractions of actual injections.** Lean certified: The C5 forward rules for persistent injectivity and strong retractions at all admitted relational types, the low-type converses to ☐ND (type t), and the per-map necessary-injectivity/strong-retraction equivalence. [Proof and certificate](evidence/RESULT-INDEX.md#c5-strong-retractions).
- **Functional Choice and ☐Functional Choice have no finite fixed-type basis.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#choice-no-finite-basis).
- **Maximalism forbids a numerical predecessor operation.** Lean certified: The no-predecessor theorem at every closed counting type; the total unique graph and Plenitude failure at e. [Proof and certificate](evidence/RESULT-INDEX.md#max-predecessor).
- **Frege number structure and transfer can be separated from stronger model claims.** Lean certified: The displayed Frege noncollapse and finiteness equivalences, number-map/Hume-class results, and C5–Actuality transfer results. [Proof and certificate](evidence/RESULT-INDEX.md#arithmetic-foundations).
- **Strong Possibility is an exact universal-identity theory.** Lean certified: The universal-core equivalence and the stated conditional disjunction criterion. [Proof and certificate](evidence/RESULT-INDEX.md#sp-criteria).
- **SP fixes the actual domain from the number of individual names.** Lean certified: The conditional monism/reflection lemma. [Proof and certificate](evidence/RESULT-INDEX.md#sp-individual-cardinality).

<a id="extensions-and-new-directions"></a>
### III. Extensions and new directions

- **Classicism can be reconstructed without primitive lambda.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#lambda-free-translation).
- **Beta identity plus a theorem rule yields contextual beta eta.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#beta-eta-conversion).
- **Endpoint separation and boxed Infinitary Comprehension reconstruct full standard models over λ-free H.** Lean certified: Full representation and converse for the native original-type λ-free H formulation, in Lean’s classical metatheory. The choice-free ZF argument retains its ordinary-proof status. [Proof and certificate](evidence/RESULT-INDEX.md#lambda-free-endpoint-comprehension).
- **Infinitary Comprehension and C5 characterize full standard models.** Lean certified: For universe-0 categorical premodels, term-denotation closure + unrestricted original-closed-type Infinitary Comprehension + ☐ND (type t) imply faithful full-standard representation; full standard models satisfy the corresponding infinitary axioms. [Proof and certificate](evidence/RESULT-INDEX.md#infinitary-comprehension).
- **Actual-truth evaluators and current extensional cores.** Lean certified: Actuality-core conversion and admitted-value lemmas. [Proof and certificate](evidence/RESULT-INDEX.md#evaluators-cores).
- **Stable atoms are exactly what diagonal separation requires.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#diagonal-characters).
- **Full identity observers have atomic and symmetry representations.** Lean certified: Simultaneous propositional separation for every finite list of closed quantifier types under C5 + Atomicity (type t), including its necessary schema; the converses and equivalence of the two schemas under C5 + Actuality. [Proof and certificate](evidence/RESULT-INDEX.md#full-identity-observers).
- **An actual evaluator commuting with modality forces Extensionality.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#evaluator-modal-commutation).
- **Logical observer separation: a strict hierarchy from BF to Extensionality.** Lean certified: H + OS ⇒ C + BF with explicit endpoint identities. Their omission is justified by the linked ordinary reduction proof. [Proof and certificate](evidence/RESULT-INDEX.md#logical-observers).
- **Observer separation over H: primitive packages, representation and higher types.** Lean certified: The foundational implication H + OS ⇒ C + BF, with explicit endpoint identities. [Proof and certificate](evidence/RESULT-INDEX.md#h-observer-space).
- **Profile Realization and the Boolean structure of worlds.** Lean certified: The finite-profile and atomic-profile results. [Proof and certificate](evidence/RESULT-INDEX.md#profile-world-algebra).
- **World orbits determine propositional Dedekind infinity.** Lean certified. [Proof and certificate](evidence/RESULT-INDEX.md#nominal-orbits).
- **Faithful probability has an exact finite-fibre condition and type ceiling.** Lean certified: Supported-real suprema, natural-number order and basic numeric operations; cut crossing and supported-real negation, subtraction and inverses. Numeric-operation laws retain ActualWorld, quantified Infinity and domain guards; induction and cases require ActualWorld alone. [Proof and certificate](evidence/RESULT-INDEX.md#probability).

## Sources and reproduction

Source proofs and accepted certificate evidence are linked in [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) and [the certificate index](evidence/CERTIFICATES.json).

The summaries and this scope note are generated from the canonical records. Follow [REPRODUCING.md](REPRODUCING.md) for drift checks, exact-source verification and intentional checksum refreshes.
