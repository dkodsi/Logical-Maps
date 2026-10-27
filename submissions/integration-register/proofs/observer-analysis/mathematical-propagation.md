# Propagation of arithmetic, Infinity, analysis and CH

25 October 2026. Ordinary mathematical research by OpenAI Codex. This extends the witness-transport packet with the user's four proposed applications. No historical novelty, human review or new formal certificate is claimed.

## 1. What propagates

Here propagation means that a **current mathematical assertion** A implies □A. This differs from asking whether an already-modal necessity principle remains necessary. The fixed background is relational C; C5 is C with all-type boxed ND, and OS is ordinary whole-operation logical observer separation.

| Current assertion | Sufficient assumptions beyond C | Result and scope |
|---|---|---|
| A native first-order arithmetical sentence A | C5 | Both A→□A and ¬A→□¬A, at every counting type; already recorded, no OS or Infinity premise |
| Quantified Infinity Inf_σ | C5 | Inf_σ→□Inf_σ; in fact both finiteness and infinity are invariant |
| At least n objects of type σ, for a fixed external n | Current ND_σ | The same finite lower bound is necessary; no OS or BF needed |
| At most n objects of type σ, for a fixed external n | Current BF_σ | The same finite upper bound is necessary; no OS or ND needed |
| Universal first-order analytical truth at type σ, with the natural-numbers predicate | C5, one suitable OS instance, and current RC at σt, σσt, σσσt | Current truth propagates; neither all-type RC nor an infinitary qualification is needed |
| Universal CH or universal ¬CH among real structures at type σ | The same finite package | Whichever current universal assertion holds becomes necessary; no proof of CH itself |

For a simple stronger package covering every type and every finite second-order analytical sentence,

```math
C+OS+\mathrm{FunctionalChoice}
 \Longrightarrow\Box\mathrm{FunctionalChoice}
 \Longrightarrow\text{second-order analytic necessitism and necessity}
\tag{1}
```

Alternatively C5 + OS + current all-type Rigid Comprehension suffices, by the newly proved RC reflection and the existing C5 + □RC analytic theorem. The new contribution in these two routes is the observer bridge; the later analytic implications were already established.

**OS alone does not suffice for any of the four general propagation claims.** Arithmetic and Infinity have explicit local countermodels; the CH/analysis audit gives a relative coalesced-root countermodel with actual real structures at both evaluations. The [generic-point comparison](os-versus-rev-analysis.md) refutes the C5 + OS propagation claims, even with current SplitMono and BoxSep; Rev propagates both.

## 2. Arithmetic: C5 already proves the stronger result

Use the native Frege arithmetic at each σ, with numbers of type ν_σ=(σt)t. The recorded proof gives

```math
C5\vdash \Box A\lor\Box\neg A
\tag{2}
```

for every native first-order arithmetical sentence A. Its exact local ingredients are the modal dual of B, ND at ν_σ, and BF at ν_σ. It proves persistence of both truth and falsity, and therefore needs neither OS nor the I_σ guard retained in the database's Necessity of Arithmetic formulation.

Numbers, sums and products persist in C by their impredicative definitions. Modal symmetry handles falsity; stable identity handles equality atoms; BF handles the number quantifiers. Positive existential arithmetic truths consequently have a smaller persistence theorem already in C, but arbitrary arithmetic truth requires the stronger argument.

The source is Bacon's Theorem 4.4, transposed to the exact native Frege framework in [the recorded proof](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/c5-implies-necessity-of-arithmetic.yaml). The [arithmetic audit](arithmetic-audit.md) gives the proof outline, exact qualifications and countermodels to OS-only and □BF-only alternatives. This arithmetic headline is existing work.

## 3. Infinity: a positive theorem and a stronger boundary

Let

```math
\mathrm{Fin}_\sigma:=
 \exists Z^{(\sigma t)t}
 [\mathrm{FiniteCardinality}_\sigma(Z)\land Z(\top_\sigma)],
\qquad \mathrm{Inf}_\sigma:=\neg\mathrm{Fin}_\sigma
```

This is the quantified Infinity axiom, not the external schema of arbitrarily large finite sets. The existing internal-induction proof gives the discharged C theorem

```math
BF_\sigma\to(\mathrm{Fin}_\sigma\to\Box\mathrm{Fin}_\sigma)
\tag{3}
```

Under □BF_σ, its necessitation makes the persistence conditional necessary. Current ND_t supplies the modal dual of B. Thus a possible finite domain is possibly necessarily finite and hence finite now. Taking the contrapositive gives

```math
\boxed{C+ND_t+\Box BF_\sigma
 \vdash\mathrm{Inf}_\sigma\to\Box\mathrm{Inf}_\sigma}
\tag{4}
```

C5 supplies these premises at every σ. This also makes Fin_σ invariant. No optional assumption is necessitated: (3) is first discharged as a C theorem. Ordinary OS supplies BF, so it propagates current **finiteness** by (3), but this alone does not propagate Infinity in the opposite direction.

The [Infinity audit](infinity-audit.md) gives two rigorous boundaries:

* The existing root over all finite individual domains has both quantified Inf_e and Inf_t, but finite accessible leaves. It retains necessary OS and necessary BF.
* A new root over an internally finite Henkin ultraproduct keeps exactly the same individuals and their identities at both stages. It satisfies □OS, □BF, □ND_e and every necessary standard finite lower bound. Nonetheless Inf_e is true at the root and false at the leaf. The leaf is externally infinite but internally Frege-finite; the root's fuller current predicates exclude its nonstandard counting witnesses from the least inductive number predicate.

The second construction is a new ordinary countermodel specification in this packet. It proves that preserving individuals, their identities and every finite lower bound still does not preserve the **quantified internal** Infinity axiom. It does not say an externally infinite set becomes externally finite. ND_t fails there, so it does not challenge (4).

## 4. Analysis and CH: the finite comprehension bridge

At a fixed σ, write

```math
U_{\sigma,\varphi}:=
 \forall\mathfrak R
 (\mathrm{Real}_\sigma(\mathfrak R)\to\varphi(\mathfrak R))
\tag{5}
```

Real means the native complete ordered field with its natural-numbers predicate. Its completeness clause quantifies over **nonempty** bounded subproperties, as the user specified. First-order analytical φ may mention N. CH is a second-order analytical sentence, using unary subproperties and binary relation graphs for injections and bijections; it is not a first-order field sentence.

The local RC reflection theorem, applied at the three field-relation types, gives

```math
\begin{gathered}
C5+S_{t,\Delta}
 +RC_{\sigma t}+RC_{\sigma\sigma t}+RC_{\sigma\sigma\sigma t}\\
\Longrightarrow
\Box RC_{\sigma t}+\Box RC_{\sigma\sigma t}
 +\Box RC_{\sigma\sigma\sigma t},\\
\Delta=\{\sigma,\sigma t,\sigma\sigma t,\sigma\sigma\sigma t\}
\end{gathered}
\tag{6}
```

The plus signs denote jointly assumed formulas, not arithmetic operations. Each use of S has only a finite type list. The ordinary proof of C5 + □RC analytic necessitism uses precisely these three RC types for a rigid necessary real structure and represented unary and binary powers. Unary comprehension handles the carrier, N, completeness and least-inductive clauses; binary comprehension handles the order and relation witnesses; ternary comprehension handles addition and multiplication graphs. The family of rigid k-ary relations is defined directly and proved rigid using C5 and BF; no RC at the type of that family is needed. The [CH/analysis audit](ch-analysis-audit.md) records the exact prior proof locator and finite-premise audit.

Consequently (6)'s premises yield

```math
U_{\sigma,\varphi}\to\Box U_{\sigma,\varphi}
\tag{7}
```

for every first-order analytical φ and for CH and ¬CH. Adding the finitely many further RC instances at σ^kt needed for higher relation arities gives the corresponding finite second-order analytical window. Full all-type RC gives all these windows.

There is an existence subtlety in deriving (7). The bare non-contingency disjunction □U_φ∨□U_¬φ does not by itself give U_φ→□U_φ when there are currently no real structures: both current universals may be vacuously true. Analytic Necessitism supplies the missing existence transfer. If a real structure is possible, it supplies an actual rigid necessary one; current U_φ then excludes the contrary necessary disjunct. If no real structure is possible, □U_φ holds vacuously. Thus the necessitism route above justifies (7) without concealing an actual-existence premise.

## 5. Why OS alone does not settle analytical propagation

The obstacle in the direct observer calculation is precise. Moving E through Real(R) transforms its quantified subproperties only into the image of postcomposition by E. The result can assert completeness relative to that image without asserting completeness relative to **every** admitted subproperty of the transformed field. Current universal analytical truth therefore cannot automatically be applied to R^E as a real structure. CH also introduces existential relation witnesses for injections and bijections, where the earlier selector-image obstruction reappears.

The [CH/analysis audit](ch-analysis-audit.md) supplies a relative countermodel to the bare-OS implication. In an ambient constructible universe, take a countable model of ZFC + ¬CH and its internally full extensional Henkin hierarchy. Add an unrestricted current-row root. At type et the root has enough objects and full current relation extensions for a genuine ambient real field; its current real structures satisfy CH and the analytical sentence expressing that every real is constructible. At the accessible Henkin leaf both sentences fail. Both evaluations have actual real structures, so the discrepancy is not vacuity.

The reader of the leaf truth coordinate and identity are admitted, whole-operation logical observers; onto type projections verify the quantifier laws. The note checks the stronger retained observer and modal premises explicitly and states its metatheory. C5 fails at the root. The construction therefore proves a bare-C observer boundary, **not** failure under C5 + OS. No generic Boolean ultrafilter is assumed to preserve quantifiers.

The earlier C5 Boolean-valued countermodel with ordinary FC also fails analytical necessity, but it does not have OS, by the new OS + FC theorem. It cannot be reused to refute C5 + OS. For the stronger C5 background, the [symmetric limit](necessary-os-ch-inaccessible-countermodel.md) gives contingent CH under a strongly inaccessible cardinal, and the [two-Hechler model](necessary-os-analysis-countermodel.md) gives analytical contingency.

## 6. Necessity principles themselves already persist

The native Necessity of Arithmetic, Necessity of Analysis, Necessity of Second-Order Analysis and Non-contingency of CH are instancewise finite disjunctions of boxes. For any finite list of propositions B_i, C's S4 principles give

```math
(\Box B_1\lor\cdots\lor\Box B_n)
 \to\Box(\Box B_1\lor\cdots\lor\Box B_n)
\tag{8}
```

Use 4 on the true disjunct and necessitated disjunction introduction. Thus those already-modal principle instances propagate in C alone. This elementary fact must not be confused with proving the necessity principles from current arithmetic, CH or analytical truth. It does not turn current analytical truth into necessary truth.
