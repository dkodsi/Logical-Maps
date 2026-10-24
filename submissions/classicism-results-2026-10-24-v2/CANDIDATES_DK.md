# CANDIDATES_DK

The background is finitary relational C unless stated otherwise.

[Main results](MAIN-RESULTS.md) · [Integration review](DATABASE-INTEGRATION.md) · [Structured proposals](CANDIDATES_DK.json) · [Evaluation principles](#evaluation-principles) · [Infinitary extension](#infinitary-extension)

## Proposed principles

| Subject | Principle | Reason for inclusion |
|---|---|---|
| Observers | [Logical Observer Separation](#logical-observer-separation-r) | Recovers C + BF over H and has atomless models. Restrictions on its observers give a hierarchy through C5 + Atomicity to Extensionality. |
| Choice and rigidity | [Sections of Surjections](#sections-of-surjections-r) | Isolates the extra ingredient which, with Actuality, is exactly Functional Choice; countermodels show that neither conjunct can be omitted. |
| Choice and rigidity | [Retractions of Injections](#retractions-of-injections-r) | Gives the matching decomposition of Plenitude; requiring necessarily correct retractions instead gives exactly C5. |
| World structure | [Individual Profile Realization](#individual-profile-realization) | Adds realizable individual profiles beyond ☐Functional Choice, with exact full-model cardinality tests and a diagonal obstruction at relational input types. |
| World structure | [Numerical Lottery](#numerical-lottery-r) | Separates numerical variation from the Axiom of Infinity over ☐Plenitude; over ☐Functional Choice, its type-t instance is equivalent to the Axiom of Infinity (type t). |
| Infinitary principles | [Infinitary Comprehension](#infinitary-comprehension-r) | It extends the ordinary comprehension schema directly and characterizes full standard models with C5. |

<a id="observer-principles"></a>
## Observers

<a id="logical-observer-separation-r"></a>
### Logical Observer Separation

Relations are identical exactly when all suitably qualified logical observers agree on their instances.

```math
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,\mathrm{Good}_{\Delta}(E) \\
&\qquad \to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
```

The schema ranges over finite argument tuples $`\bar\sigma`$ and finite lists $`\Delta`$ of tested types. $`\mathrm{Good}_\Delta(E)`$ requires preservation of Boolean operations and the listed quantifiers as identities of whole operations, together with the translated equality laws. [Exact qualification and variants](proofs/h-observer-space/SUMMARY.md#logical-observer-separation-r).

- H + OS entails C + BF. **Lean certified** with explicit endpoint identities; [omitting them](proofs/logical-observer-endpoint-reduction.md) uses the ordinary reduction proof.
- Over C: Atomicity (type t) + BF ⇒ OS ⇒ BF, with neither converse valid.
- Endpoint separation is equivalent over H to C5 + Atomicity (type t). Given OS, uniqueness of the qualified observer is equivalent to Extensionality.

#### Observer restrictions

| Variant | Additional qualification | Main consequence |
|---|---|---|
| <a id="endpoint-logical-observer-separation-r"></a>[Endpoint](proofs/h-observer-space/SUMMARY.md#endpoint-logical-observer-separation-r) | Only ⊤ and ⊥ as outputs | Exactly C5 + Atomicity (type t) over H. |
| <a id="reversible-logical-observer-separation-r"></a>[Reversible](proofs/h-observer-space/SUMMARY.md#reversible-logical-observer-separation-r) | A qualified two-sided inverse | Gives C5 + ☐OS + No Pure Contingency, including in atomless models. |
| <a id="injective-logical-observer-separation-r"></a>[Injective](proofs/h-observer-space/SUMMARY.md#injective-logical-observer-separation-r) | Currently injective | Whether it gives logical left-inverse separation remains open. |
| <a id="native-necessity-logical-observer-separation-r"></a>[☐-preserving](proofs/h-observer-space/SUMMARY.md#native-necessity-logical-observer-separation-r) | Preserves native necessity | Gives ☐BF and .2; equivalent to injective separation over C5. |
| <a id="finite-image-logical-observer-separation-r"></a>[Finite-image](proofs/h-observer-space/SUMMARY.md#finite-image-logical-observer-separation-r) | Internally finite image | Strictly between OS and endpoint separation. |
| <a id="idempotent-native-necessity-logical-observer-separation-r"></a>[Idempotent ☐-preserving](proofs/h-observer-space/SUMMARY.md#idempotent-native-necessity-logical-observer-separation-r) | Also $`E\circ E=E`$ | Strictly stronger than ☐-preserving separation; with C5, exactly Extensionality. |
| <a id="bounded-stabilization-native-necessity-logical-observer-separation-r"></a>[Bounded stabilization](proofs/h-observer-space/SUMMARY.md#bounded-stabilization-native-necessity-logical-observer-separation-r) | $`E^{r+1}=E^r`$ for fixed $`r\ge1`$ | An unbounded strict hierarchy of ☐-preserving separation principles. |
| <a id="factive-logical-observer-separation-r"></a>[Factive](proofs/h-observer-space/SUMMARY.md#factive-logical-observer-separation-r) | Ep implies p | Exactly Extensionality at full scope over H. |
| <a id="central-logical-observer-separation-r"></a>[Central](proofs/h-observer-space/SUMMARY.md#central-logical-observer-separation-r) | Commutes with every qualified observer | Exactly Extensionality over C5. |

The [headline guide](proofs/h-observer-space/SUMMARY.md#headline-results) explains the main distinctions; the [full list of connections and definitions](proofs/h-observer-space/SUMMARY.md#logical-observer-principles) retains the proposal family and proof references.

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#logical-observers).

<a id="choice-and-rigidity-principles"></a>
## Choice and rigidity

<a id="sections-of-surjections-r"></a>
### Sections of Surjections

Every surjective operation between relational types has a pointwise right inverse.

```math
\forall f^{\sigma\tau}\, .\,\mathrm{Surj}(f)\to\exists g^{\tau\sigma}\, .\,\forall y^\tau\, .\,f(gy)=y\qquad(\sigma,\tau\ne e).
```

Here

```math
\mathrm{Surj}(f):=\forall y^\tau\, .\,\exists x^\sigma\, .\,fx=y.
```

- Over C: Functional Choice ⇔ Actuality + Sections of Surjections.
- Actuality does not imply Sections, and Sections do not imply Actuality. The full two-object chain and the atomless Boolean-valued construction provide the respective witnesses (§5).

<a id="strong-sections-of-surjections-r"></a>
#### Strong Sections of Surjections

Every actually surjective operation between relational types has a necessarily correct right inverse.

```math
\forall f^{\sigma\tau}\, .\,\mathrm{Surj}(f)\to\exists g^{\tau\sigma}\, .\,\Box\forall y^\tau\, .\,f(gy)=y\qquad(\sigma,\tau\ne e).
```

$`\mathrm{Surj}`$ is as defined under Sections of Surjections. The antecedent asserts actual surjectivity; the inverse equation holds necessarily.

- Over C: ☐Functional Choice ⇔ ☐Actuality + Strong Sections.
- Replacing Strong Sections by ordinary Sections fails, even beside ☐Actuality; the full two-object retract supplies the countermodel (§5).

**Sources:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md) (§§1–6) · [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md) (§§11–20).

**Lean certified:** The Functional Choice and ☐Functional Choice decompositions into Actuality and the corresponding section principles.

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#sections-retractions).

<a id="retractions-of-injections-r"></a>
### Retractions of Injections

Every injective operation between relational types has a pointwise left inverse.

```math
\forall f^{\sigma\tau}\, .\,\mathrm{Inj}(f)\to\exists g^{\tau\sigma}\, .\,\forall x^\sigma\, .\,g(fx)=x\qquad(\sigma,\tau\ne e).
```

Here

```math
\mathrm{Inj}(f):=\forall x,y^\sigma\, .\,fx=fy\to x=y.
```

- Over C: Plenitude ⇔ Actuality + Retractions of Injections.
- Requiring a necessarily correct inverse gives exactly C5 over C:

```math
\forall f^{\sigma\tau}\, .\,\mathrm{Inj}(f)\to\exists g^{\tau\sigma}\, .\,\Box\forall x^\sigma\, .\,g(fx)=x\qquad(\sigma,\tau\ne e).
```

**Sources:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md) (§§1–6) · [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md) (§§11–20).

**Lean certified:** The Plenitude decomposition; the constituent directions of the C5/strong-retraction characterization.

**Evidence:** [Choice and Plenitude decompose into Actuality and inverse maps](evidence/RESULT-INDEX.md#sections-retractions) · [C5 is exactly strong retractions of actual injections](evidence/RESULT-INDEX.md#c5-strong-retractions).

<a id="world-structure-principles"></a>
## World structure

<a id="individual-profile-realization"></a>
### Individual Profile Realization

One individual predicate can possibly agree with every admitted rigid individual property.

```math
\exists V^{et}\, .\,\forall X^{et}\, .\,\mathrm{Rigid}(X)\to\Diamond c_V(X).
```

For $`V,X^{et}`$, put

```math
c_V(X):=\forall x^e\, .\,Vx\leftrightarrow Xx.
```

Profiles range over admitted rigid individual properties. This differs from the database’s Actual Profile principle.

- Full S5 models with worlds $`\mathcal P(D)`$ validate this principle, ☐Functional Choice, and any prescribed nonempty finite or infinite individual set $`D`$. One-world full models refute it while satisfying ☐Functional Choice.
- Nominal models give C + ☐Plenitude + this principle without Functional Choice.
- Over C + ☐Plenitude, replacing $`e`$ by an unrestricted relational input type yields a diagonal contradiction.

<a id="atomic-individual-profile-realization"></a>
#### Atomic Individual Profile Realization

One individual predicate has an atomic agreement proposition for each admitted rigid individual property.

```math
\exists V^{et}\, .\,\forall X^{et}\, .\,\mathrm{Rigid}(X)\to\mathrm{Atom}_t(c_V(X)).
```

The agreement proposition $`c_V(X)`$ is defined under Individual Profile Realization. Profiles again range over admitted rigid individual properties.

- Implies Individual Profile Realization. Over C + ☐Plenitude, each rigid profile corresponds to exactly one world atom for the same $`V`$.
- Full S5 models with $`D=\mathbb N`$ and $`W=\mathcal P(\mathbb N)`$ satisfy the atomic version; $`D=\mathbb N`$ and $`W=\mathcal P(\mathcal P(\mathbb N))`$ satisfy the nonunique version but refute the atomic version. Both satisfy ☐Functional Choice in the ZFC metatheory.

**Sources:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) (§§2–4,12–15,35–36) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) (§§3–8).

**Lean certified:** The finite-profile and atomic-profile fragments.

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#profile-world-algebra).

<a id="numerical-lottery-r"></a>
### Numerical Lottery

A numerical quantity necessarily takes exactly one natural value, and every current natural value is possible.

```math
\begin{aligned}
&\exists L^{\nu_\kappa t}\, .\,\bigl(\Box\exists!n^{\nu_\kappa}\, .\,\mathbb N_\kappa n\land Ln\bigr) \\
&\qquad \land\bigl(\forall n^{\nu_\kappa}\, .\,\mathbb N_\kappa n\to\Diamond Ln\bigr).
\end{aligned}
```

The counting type $`\kappa`$ determines the Frege numerical type $`\nu_\kappa=(\kappa t)t`$, with finite-cardinality predicate $`\mathbb N_\kappa`$. The principle is a schema in $`\kappa`$.

- Over C + ☐Plenitude + Axiom of Infinity at $`\kappa`$: equivalent to an $`\mathbb N_\kappa`$-indexed independent propositional family, a nonzero partition of $`\top`$ indexed by $`\mathbb N_\kappa`$, and an admitted surjection $`\mathrm{Atoms}(t)\to\mathbb N_\kappa`$.
- Over C + ☐Functional Choice, the $`t`$-instance is equivalent to Axiom of Infinity (type t).
- Nominal examples satisfy ☐Plenitude and both base-type Infinity axioms while refuting numerical independence, so Infinity alone does not supply this structure without Choice.

**Sources:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) (§§23–27,34).

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#profile-world-algebra).

<a id="infinitary-extension"></a>
## Infinitary principles

<a id="infinitary-comprehension-r"></a>
### Infinitary Comprehension

Every infinitary formula defines a relation with the same truth conditions at every accessible point.

```math
\exists R^{\sigma_1\cdots\sigma_n t}\, .\,\Box\forall x_1\cdots x_n\, .\,\bigl(R[\bar x]\leftrightarrow A\bigr).
```

A is any classical formula built using arbitrary set-sized well-founded conjunctions and disjunctions, with any set-sized family of typed parameters; R is not free in A. Each instance holds for every simultaneous parameter assignment. The argument tuple is finite and may be empty.

- Over the λ-free base of H, full typed endpoint separation plus this schema characterizes full standard hierarchies in ZF. Finite instances reconstruct abstraction; the observer qualification can omit translated equality clauses. Whole-operation preservation remains expressible using composite representatives. See the [λ-free reconstruction](proofs/lambda-free-endpoint-comprehension.md).
- The resulting theory supplies C5, Atomicity, Actuality, Boolean Completeness, Plenitude and Rigid Comprehension. Its full-model representation is provable in ZF; Infinity and Extensionality remain optional.

**Sources:** [infinitary-comprehension.md](proofs/infinitary-comprehension.md) (§§1–4, 5 (source Theorem 5.3), and 6) · [infinitary-canonical-representation.md](proofs/infinitary-canonical-representation.md) (§5) · [intrinsic-observer-axioms.md](proofs/intrinsic-observer-axioms.md) (§§1–7) · [lambda-free-endpoint-comprehension.md](proofs/lambda-free-endpoint-comprehension.md) (§§1–6).

**Lean certified:** For the general boxed schema, term-denotation closure + unrestricted original-closed-type Infinitary Comprehension + ☐ND (type t) give faithful full-standard representation of universe-0 categorical premodels, with a separately certified full-standard converse.

**Evidence:** [Infinitary Comprehension and C5 characterize full standard models](evidence/RESULT-INDEX.md#infinitary-comprehension) · [Endpoint separation and unboxed range comprehension characterize full standard models in ZF](evidence/RESULT-INDEX.md#intrinsic-observer-axioms) · [Endpoint separation and boxed Infinitary Comprehension reconstruct full standard models over λ-free H](evidence/RESULT-INDEX.md#lambda-free-endpoint-comprehension).

<a id="evaluation-principles"></a>
## Evaluation principles

These six propositional operator requirements form a strict hierarchy over C. Their exact equivalents include all-type principles such as Gallin Extensional Comprehension and ☐Plenitude; the countermodels distinguish correctness, necessary bivalence, uniqueness and the order of modal quantification.

For $`E^{tt}`$, define

```math
\mathrm{Eval}(E):=\forall p^t\, .\,(p\to Ep=\top)\land(\neg p\to Ep=\bot).
```

### Truth Test

```math
\exists f^{tt}\, .\,\forall p^t\, .\,p\leftrightarrow fp=f\top.
```

**Equivalent over C:** Actuality.

### Correct Evaluation

```math
\exists E^{tt}\, .\,\mathrm{Eval}(E).
```

**Equivalent over C:** ND + Actuality.

### Correct Evaluation with ☐Bivalence

```math
\exists E^{tt}\, .\,\mathrm{Eval}(E)\land\bigl(\Box\forall p^t\, .\,Ep=\top\lor Ep=\bot\bigr).
```

**Equivalent over C:** Gallin Extensional Comprehension; equivalently ND + Strong Actuality.

### Unique Correct Evaluation

```math
\exists!E^{tt}\, .\,\mathrm{Eval}(E).
```

**Equivalent over C:** C5 + Actuality.

### ☐Correct Evaluation

```math
\Box\exists E^{tt}\, .\,\mathrm{Eval}(E).
```

**Equivalent over C:** ☐Plenitude.

### Uniform Correct Evaluation

```math
\exists E^{tt}\, .\,\Box\mathrm{Eval}(E).
```

**Equivalent over C:** Extensionality.

- Necessary bivalence constrains future output values without requiring correctness there.
- Unique Correct Evaluation quantifies over all correct evaluators, including those without necessary bivalence.
- The last two requirements distinguish an evaluator at each world from one fixed evaluator correct at every world.

**Sources:** [actual-truth-evaluator-ladder.md](source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md) (Six-level hierarchy and strictness arguments).

**Lean certified:** Actuality-core conversion and admitted-value lemmas.

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#evaluators-cores).

## Further equivalent formulations

### Diagonal Character Separation

Diagonal Character Separation is equivalent over C to ND (type $`t`$) + Atomicity (type $`t`$). Put

```math
w_E:=\forall p^t\, .\,Ep\to p,
```

```math
\begin{aligned}
&D(E):=E\bot=\bot\land(\forall p^t\, .\,Ep=\top\lor Ep=\bot) \\
&\qquad \land(\forall p^t\, .\,E(\neg p)=\neg(Ep))\land E(w_E).
\end{aligned}
```

The separation principle is

```math
\forall p,q^t\, .\,p=q\leftrightarrow\forall E^{tt}\, .\,D(E)\to(Ep\leftrightarrow Eq).
```

**Sources:** [diagonal-characters.md](proofs/diagonal-characters.md) (§§1–4).

**Lean certified.**

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#diagonal-characters).

### Complete Boolean Retractions

Every rigid Boolean subalgebra, complete for admitted families, at every relational type has a complete Boolean retraction. Over C + ☐Plenitude this is equivalent to ☐Functional Choice; the propositional-only version is insufficient.

For each relational type $`\tau`$, let $`\mathrm{CBA}_\tau(A)`$ say that $`A`$ is such a subalgebra, and $`\mathrm{CBHom}_\tau(r)`$ that $`r`$ preserves complements and all admitted meets. The principle is

```math
\begin{aligned}\forall A^{\tau t}\, .\,\mathrm{CBA}_\tau(A)\to\exists r^{\tau\tau}\, .\,\bigl[&\mathrm{CBHom}_\tau(r)\land\forall p^\tau\, A(rp)\\&\land\forall q^\tau\,(Aq\to rq=q)\bigr].\end{aligned}
```

**Sources:** [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) (§§16,18–19,38).

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#boolean-retractions-choice).
