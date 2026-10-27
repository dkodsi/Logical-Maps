# Observer results and connections

[Unified guide: C and H maps, definitions and simplifications](../../LOGICAL-OBSERVERS.md).

[Detailed observer map](GRAPH.md) · [Main Results](../../MAIN-RESULTS.md#h-observer-separation) · [Theorem tables](MAP.md)

<a id="headline-results"></a>
## Headline results

A logical observer is an admitted operation on propositions preserving Boolean operations and quantifiers as whole-operation identities, with the equality laws needed over H. **OS** says that these observers distinguish any two distinct relations. Qualification uses a finite list of types; the principles below are full relational schemas unless a narrower scope is stated.

- **Logical separation recovers Classicism.** H + OS entails C + BF. **Lean certified** for the formulation with explicit endpoint identities; [the reduction](../logical-observer-endpoint-reduction.md) removes them. Atomicity (type t) + BF suffices for OS over C, but OS also has atomless models. [Proof and certificate scope](../../evidence/RESULT-INDEX.md#logical-observers).
- **Endpoint and unique observers locate familiar theories.** Requiring endpoint-valued observers gives exactly C5 + Atomicity (type t) over H; requiring OS and a unique qualified observer gives Extensionality. Under Extensionality, truth is itself endpoint-valued. Over C, every arrow in the following chain is strict:

```math
\small\text{Extensionality}\Rightarrow\mathrm{C5}+\mathrm{Atomicity}_t\Rightarrow\Box\mathrm{OS}\Rightarrow\mathrm{OS}\Rightarrow\mathrm{BF}.
```

  OS + Plenitude at (t,t) already gives endpoint separation. Over C5, ☐OS plus possible Actuality gives ☐Plenitude. [Hierarchy](../logical-observer-hierarchy.md) · [Plenitude bridge](plenitude-endpoint-bridge.md) · [Necessary OS](../logical-observers.md#8-necessary-os-and-possible-actuality).
- **Reversibility gives No Pure Contingency without atoms.** Separation by observers with qualified two-sided inverses (**Rev**) entails C5 + ☐OS + No Pure Contingency. It can hold in atomless models. One atom, Actuality, or one qualified finite-image observer raises Rev to endpoint separation. Over C5, Rev is exactly the claim that only ⊤ and ⊥ are fixed by every reversible logical observer. [Pure contingency](reversible-separation-and-pure-truth.md) · [Invariant propositions](GRAPH.md#reversibility-and-the-invariant-proposition-algebra).
- **Surjectivity, injection and admitted inverses give different theories.** Surjective separation (**SurjSep**) and separation by observers with logical left inverses (**SplitMono**) are incomparable; their conjunction remains strictly weaker than Rev. Over C5, SurjSep is Rev. Injective separation (**InjSep**) is weaker than Rev and stronger than OS, strictly over C5. SplitMono strictly implies InjSep, even over C5 with necessary all-type Relational Choice, Transversal Choice and Zorn. See [countermodel](rigid-souslin-injective-separation.md). [Inverse comparison](GRAPH.md#9-the-larger-region-above-c--bf) · [Countermodel and scope](../../CONJECTURES.md#observer-strength).
- **Preserving necessity has additional modal force.** Separation by logical observers preserving native necessity (**BoxSep**) entails ☐BF and .2. Over C5 it is exactly InjSep; outside C5 the two are incomparable. Requiring idempotence strictly strengthens BoxSep and gives Extensionality with C5. The fixed bounds $`E^{r+1}=E^r`$ form an unbounded strict hierarchy. [Modal comparison](native-box-logical-observers.md) · [Stabilization](GRAPH.md#an-unbounded-stabilization-hierarchy).
- **Symmetry laws give exact finite bounds.** With Rev, any fixed nontrivial group law on all reversible observers gives an exact finite bound on propositions: commutativity gives at most four, and the metabelian law at most eight. Internally finite separating families give corresponding internal-finiteness characterizations without a fixed numerical bound. Centrality among all logical observers and centrality among reversible observers give distinct theories. [Group laws](GRAPH.md#any-nontrivial-group-equation) · [Finite families](GRAPH.md#internally-finite-families-of-observers) · [Centrality](GRAPH.md#commuting-with-every-logical-observer).
- **Endpoint separation and comprehension recover full models.** Endpoint separation plus ☐Infinitary Comprehension characterizes full standard relational hierarchies over the specified λ-free base of H, in ZF. Finite instances reconstruct abstraction; neither Infinity nor Extensionality is imposed. [Formulation and proof](../lambda-free-endpoint-comprehension.md).

The broader investigation also classifies every finite package of independent primitive preservation clauses, factors full relational separation into propositional separation plus Functionality, and gives algebraic representations for weaker observer classes. [Primitive packages](GRAPH.md#1-independent-primitive-packages-the-exact-core) · [Higher types](GRAPH.md#2-the-spine-higher-types-and-preservation-strength) · [Representations](GRAPH.md#3-algebraic-structures-and-exact-representation).

<!-- BEGIN OBSERVER PRINCIPLE REFERENCE -->

<a id="logical-observer-principles"></a>
## Logical-observer principles and connections

<a id="logical-observer-separation-r"></a>
### Logical Observer Separation

Every pair of distinct relations can be distinguished at some arguments by a suitably qualified logical observer.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

The schema ranges over finite argument tuples $`\bar\sigma`$, including the empty tuple, and finite lists $`\Delta`$ of tested types. The following finite conjunction defines $`\mathrm{Good}_\Delta(E)`$.

```math
E\top=\top,\qquad E\bot=\bot.
```

Boolean operation identities:

```math
(\lambda p\, .\,E(\neg p))=(\lambda p\, .\,\neg Ep),
```

```math
(\lambda p,q\, .\,E(p\land q))=(\lambda p,q\, .\,Ep\land Eq),
```

```math
(\lambda p,q\, .\,E(p\lor q))=(\lambda p,q\, .\,Ep\lor Eq).
```

For each $`\sigma\in\Delta`$, quantifier operation identities:

```math
(\lambda F^{\sigma t}\, .\,E(\forall x^\sigma\, .\,Fx))=(\lambda F^{\sigma t}\, .\,\forall x^\sigma\, .\,E(Fx)),
```

```math
(\lambda F^{\sigma t}\, .\,E(\exists x^\sigma\, .\,Fx))=(\lambda F^{\sigma t}\, .\,\exists x^\sigma\, .\,E(Fx)).
```

For each $`\sigma\in\Delta`$, Equality laws:

```math
\forall x^\sigma\, .\,E(x=x),
```

```math
\forall x,y^\sigma\, .\,\forall F^{\sigma t}\, .\,E(x=y)\to(E(Fx)\to E(Fy)).
```

Over C, the equality laws follow from Boolean preservation. They support the formulation over H, where OS recovers C.

The uniform definition includes the endpoint identities used in the Lean certificate. The formulation omitting those identities gives an equivalent full separation theory; see the H-to-C proof.

- H + OS entails C + BF. **Lean certified** with explicit endpoint identities; [omitting them](../logical-observer-endpoint-reduction.md) uses the ordinary reduction proof.
- Over C: Atomicity + BF ⇒ OS ⇒ BF, with neither converse valid.
- Over C5 + Actuality: OS ⇔ Atomicity ⇔ ☐OS.
- OS does not imply Atomicity (type t), Actuality, ND, ☐OS, ☐BF or ☐Functionality.
- Over C5, ☐OS + ◇Actuality entails ☐Plenitude; replacing ☐OS by OS does not suffice.
- Over C, the variants below extend the strict hierarchy:

```math
\small\text{Extensionality}\ \Rightarrow\ \mathrm{C5}+\mathrm{Atomicity}\ \Rightarrow\ \Box\mathrm{OS}\ \Rightarrow\ \mathrm{OS}\ \Rightarrow\ \mathrm{BF}.
```

- Over C, $`\mathrm{Good}_\Delta(E)\leftrightarrow\Box\mathrm{Good}_\Delta(E)`$; requiring the qualification necessarily does not strengthen separation.
- Over H, OS plus uniqueness of the qualified logical observer at one fixed finite list is equivalent to Extensionality; no endpoint restriction is needed.
- Over C5, propositional separation by Boolean observers preserving the universal quantifier at t is equivalent to full OS.
- Endpoint separation is equivalent over H to C5 + ☐OS + one atom; the boxed propositional $`\mathrm{Good}_{\{t\}}`$ separation instance suffices in place of ☐OS.
- Even the stronger qualified left-inverse separation principle does not imply C5, ☐OS, its own boxed schema, ☐BF or ☐Functionality; see the [all-maps model](finite-block-symmetry-left-inverse.md), §7.
- The [ternary Cantor model](ternary-cantor-observer-model.md) has full endpoint-fixing separation for each separate M/Q/P, V/Q/P and N/Q/P class, even necessarily and with boxed BF and Functionality, while Boolean separation fails.
- Qualified left-inverse separation lies strictly between reversible separation and OS, and is incomparable with ☐OS even over C5. With internal finiteness of all propositions, full left-inverse, reversible and endpoint separation coincide.
- Over C + BF, each finite-list left-inverse separation instance is exactly the corresponding reversible instance or ordinary separation together with one qualified left-inverse pair having a true kernel element. The full-H statement is an external schema of alternatives; see the [decomposition](left-inverse-separation-decomposition.md).
- Over H, OS + Plenitude at (t,t) is equivalent to endpoint separation; full Plenitude may replace the single instance. Already C + BF (type t) + Plenitude at (t,t) is exactly C5 + Actuality. See the [Plenitude bridge](plenitude-endpoint-bridge.md).
- C5 + ☐OS need not imply qualified left-inverse separation, even when every admitted proposition injection is onto and propositions are atomless; see the [linear/circular fibre model](linear-circular-fibre-left-inverse-gap.md).
- Separation by currently surjective logical observers lies strictly between Rev and OS and is incomparable with qualified left-inverse separation, even over C + ☐BF + ☐OS. Under C5 it is equivalent to Rev. The [omega-chain classification](omega-chain-surjective-observers.md) and finite-block model supply the distinctions.
- The [fixed-point symmetry criterion](fixed-point-symmetry-left-inverse-separation.md) strengthens the qualitative-contrast model to C5 + SplitMono without ☐OS or ☐SplitMono.
- SurjSep + SplitMono is strictly stronger than either factor and strictly weaker than Rev. Even ☐SurjSep + ☐SplitMono + C + ☐BF does not imply Rev, witnessed by the [full ℤ×ℕ model](full-cancellative-monoid-observers.md). Separate witness families are allowed.
- Over C + BF (type t), Onto(E) implies ☐Onto(E), with E a free parameter. Nevertheless SurjSep implies neither ☐OS nor ☐SurjSep, even with ☐BF and ☐Functionality; see the [root truth-profile model](root-truth-profile-surjective-separation.md). Rev ⇒ ☐SurjSep ⇒ SurjSep and ☐SurjSep ⇒ ☐OS are strict. SurjSep does not imply ☐BF, with failure at every admitted type in the integer-shift predecessor model.
- Over C5, [canonical admitted adjoints](canonical-adjoints-and-image-factorization.md) give exact individual-observer tests for injection, surjection and reversibility. A Boolean observer commutes with native necessity or possibility exactly when it is injective; this test needs no quantifier-preservation premise.
- BoxSep, separation by logical observers commuting with native necessity, implies ☐BF and .2, hence ☐Functionality. Over C5 it is equivalent to InjSep and lies strictly between Rev and OS. It is incomparable with InjSep and SplitMono over C + BF, and with ☐OS over C + ☐BF; see [native necessity](native-box-logical-observers.md).
- IdemBoxSep strictly strengthens BoxSep and becomes Extensionality with C5. The finite-frame join theorem, C5 injective decomposition and scoped modal reflection are in the [updated atlas](GRAPH.md).
- Fixed finite stabilization bounds give an unbounded strict native-necessity hierarchy, including a single infinite countermodel to every fixed bound. Over C5, finite relative-generation separation is exactly Rev without assuming injection; J alone does not give K. See the [observer atlas](GRAPH.md).
- Over C5, canonical local-support separation is exactly Rev. Boolean Completeness (type t) plus Zorn at t gives exact controlled-inverse criteria; admitted true local homogeneity plus OS gives SplitMono without J. See the [support and selection map](GRAPH.md#canonical-local-support-and-selection).
- Over C5, central logical separation is Extensionality and fixed-degree separation is Rev. OS reflects each assumed Boolean Completeness instance into necessity; completeness at t remains strictly below the tt-to-Actuality route. See the [full observer map](GRAPH.md).
- Over C5, Rev is exactly triviality of the propositions fixed by all reversible Good-t observers. Centrality, group exponents and finite images have exact finite-domain characterizations; see the [full map](GRAPH.md).
- With Rev, any fixed nontrivial group law on all reversible observers gives an exact finite proposition bound. Without Rev, it gives an exact invariant-component condition over C5. Internally finite separating families give the corresponding full separation theory plus FinAll. See the [theorem map](MAP.md).
- Even necessary full OS does not imply that every admitted proper propositional filter has an admitted ultrafilter extension; the finite-partition construction gives the countermodel. This is a boundary on admitted extension, not an identification of observers with ultrafilters.

<a id="endpoint-logical-observer-separation-r"></a>
#### Endpoint Logical Observer Separation

Logical observers with outputs restricted to ⊤ and ⊥ distinguish every pair of distinct relations.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{End}(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{End}(E):=\forall p^t\, .\,Ep=\top\lor Ep=\bot.
```

The types and $`\mathrm{Good}_\Delta`$ are as above. In a full model with fixed domains and an admitted evaluation operation, an endpoint observer reports whether $`p`$ is true at a fixed possible world; it need not report the truth here.

Endpoint-valuedness differs from $`\Box\forall p(Ep\leftrightarrow p)`$: the latter gives the identity observer over C, whose outputs may remain contingent.

- Over H, the full typed schema is equivalent to C5 + Atomicity, without Actuality.
- Over C, propositional separation testing quantifiers only at t already suffices. The full schema and its separately boxed form are equivalent.
- Strictly stronger than ☐OS and strictly weaker than Extensionality over C.
- Given endpoint separation, Extensionality is equivalent to there being a unique qualified endpoint observer; uniqueness at any one fixed finite list of tested types suffices.
- Under C5, propositional atoms and endpoint observers qualified at $`t`$ correspond bijectively: $`E_a(p)=\Box(a\to p)`$ and $`a_E=\forall p(Ep\to p)`$. Such observers qualify at every finite type list.
- Equivalent to C5 + ☐OS + one atom, and to C5 plus one atom and the single boxed propositional $`\mathrm{Good}_{\{t\}}`$ separation instance.
- Equivalent over H to OS + Plenitude at (t,t), OS + full Plenitude, C5 + OS + Actuality, and C5 + OS + Boolean Completeness. Both OS and Plenitude are current premises.
- Together with boxed Infinitary Comprehension, it characterizes full standard hierarchies over the λ-free base of H, in ZF. In this package the initial qualification may omit translated equality clauses; they follow after reconstruction. See the [exact formulation](../lambda-free-endpoint-comprehension.md).

**Additional sources:** [lambda-free-endpoint-comprehension.md](../lambda-free-endpoint-comprehension.md) (§§1–5).

<a id="reversible-logical-observer-separation-r"></a>
#### Reversible Logical Observer Separation

Logical observers with qualified inverses distinguish every pair of distinct relations.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{Rev}_\Delta(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

Put $`I=\lambda p.p`$ and $`(E\circ F)(p)=E(Fp)`$.

```math
\mathrm{Rev}_\Delta(E):=\exists F^{tt}\, .\,\mathrm{Good}_\Delta(F)\land E\circ F=I\land F\circ E=I.
```

- Over C, equivalent to propositional separation by whole conjunction-preserving involutions. Their Boolean and all-type quantifier laws follow; no extra Good clause is required. [Simple formulation and proof](../reversible-propositional-separation.md).
- Over H, equivalent to involutive separation and to its separately boxed schema; entails C5 + ☐OS + No Pure Contingency, without atoms or Actuality.
- Strictly weaker than endpoint separation and strictly stronger than C5 + ☐OS, even in atomless models. Incomparable with finite-image separation.
- Together with Actuality, the existence of one atom, or the existence of one qualified observer at t with finitely many outputs, equivalent to C5 + Atomicity. The single observer need not separate.
- Forces the proposition algebra to be either atomless or atomic with a true atom.
- Equivalent over H to full logical separation by necessarily bijective observers. Over C5, current bijectivity suffices.
- Over C, equivalent to full separation by invertible observers preserving universal quantification at every finite type list containing t; Boolean preservation and the inverse quantifier laws follow.
- Equivalent over H to full logical separation by observers admitting a same-list qualified right inverse. Qualified left-inverse separation is strictly weaker, even with C5 and its own boxed schema; it need not imply No Pure Contingency.
- Even C5 + ☐SplitMono + No Pure Contingency does not imply reversible separation, as the [component-shift model](component-shift-symmetry-reversible-gap.md) shows.
- Implies noncontingency for every pure formula with finitely many individual parameters and finitely many first-order relation parameters whose values on all tuples are endpoints. Arbitrary higher-type parameters are not covered.
- If every admitted injective proposition operation is onto, full left-inverse and reversible separation coincide. C5 + Rev with that condition still need not imply endpoint separation, as the [two-colour model](finite-pinning-dedekind-propositions.md) shows.
- Equivalent over H to C5 + separation by currently surjective Good observers. The [explicit section](surjective-logical-observers.md) uses the greatest kernel element and a definable fibre representative, without Choice; C5 cannot be omitted.
- SurjSep + SplitMono is a strict weakening, even with both conjuncts boxed. The positive model-family theorem gives ☐SurjSep for full cancellative monoids and also ☐SplitMono when a specified infinite sequence of distinct units is available; a nonunit refutes C5 and hence Rev.
- Strictly stronger than ☐SurjSep, which is strictly stronger than SurjSep and than ☐OS. Individual onto qualification persists over C + BF (type t), while surjective separation need not persist.
- Over C5, equivalent to separation by Good observers with any fixed finite relative image-generation bound, without an injectivity premise; also equivalent to separation by Good observers each having a currently true local Boolean transversal.
- Over C5, exactly separation by Good observers with full or currently true local-transversal support, equivalently by the range of the canonical support normalization. Individual normalized observers need not be injective.
- Over C5, equivalent to separation by Good observers with any fixed fibre-degree bound n≥1; no injectivity, Boolean Completeness or Zorn is needed. The same-profile involution theorem applies to each such observer.
- Over C, let S_pt assert propositional separation by pointwise conjunction-preserving involutions. Then Rev ↔ ☐S_pt ↔ S_pt + BF_t. A fixed necessarily accepting witness instead gives Extensionality. S_pt + OneAtom ↔ ND_t + Atomicity_t.
- The converse from first-order endpoint-parameter noncontingency to Rev fails even over C5 + ☐SplitMono. Over C5, noncontingency for endpoint-valued proposition families invariant under admitted surjective order automorphisms is equivalent to Rev.

**Additional sources:** [reversible-propositional-separation.md](../reversible-propositional-separation.md) (§§1–3).

<a id="surjective-logical-observer-separation-r"></a>
#### Surjective Logical Observer Separation

Every proposition is an output; all tests jointly distinguish relations.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{Onto}(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{Onto}(E):=\forall q^t\, .\,\exists p^t\, .\,Ep=q.
```

- Rev ⇒ SurjSep ⇒ OS, with both converses false. Over C5, SurjSep is equivalent to Rev.

**Additional sources:** [surjective-logical-observers.md](surjective-logical-observers.md) (§§1–5).

<a id="logical-left-inverse-separation-r"></a>
#### Logical Left-Inverse Separation

Each observer can be undone by an admitted logical observer qualified at the same types.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{Left}_\Delta(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{Left}_\Delta(E):=\exists F^{tt}\, .\,\mathrm{Good}_\Delta(F)\land F\circ E=I.
```

- Rev ⇒ SplitMono ⇒ InjSep ⇒ OS. SplitMono strictly implies InjSep, even over C5 with necessary all-type Relational Choice, Transversal Choice and Zorn. See [countermodel](rigid-souslin-injective-separation.md).

**Additional sources:** [split-inverse-logical-observers.md](split-inverse-logical-observers.md) (§§1–5).

<a id="injective-logical-observer-separation-r"></a>
#### Injective Logical Observer Separation

Currently injective logical observers distinguish every pair of distinct relations. Write InjSep for the full schema.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{Inj}(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{Inj}(E):=\forall p,q^t\, .\,Ep=Eq\to p=q.
```

- SplitMono implies InjSep, which implies OS. Over C5, Rev ⇒ InjSep ⇔ BoxSep ⇒ OS has both outer implications strict.
- Over C5, qualified left inverses of an individual injective Good-t observer correspond exactly to its admitted Boolean transversals.
- The regular-open nonsplitting model fails OS, so it does not refute InjSep ⇒ SplitMono.
- SplitMono strictly implies InjSep, even over C5 with necessary all-type Relational Choice, Transversal Choice and Zorn. See [countermodel](rigid-souslin-injective-separation.md).
- Over C5, the full theory is exactly Rev or (OS and J_{t}), where J asserts one injective Good-t observer and a true proposition with no nonzero image part. SplitMono has the same decomposition with K_{t}, and K_{t} implies J_{t}; see [the decomposition](injective-separation-decomposition.md).
- Over C5, K implies J strictly. A J witness with any fixed finite image-generation bound gives K; the earlier countermodel to J ⇒ K fails OS. The [rigid Souslin countermodel](rigid-souslin-injective-separation.md) refutes InjSep ⇒ SplitMono, even over C5 with necessary all-type Relational Choice, Transversal Choice and Zorn.

<a id="native-necessity-logical-observer-separation-r"></a>
#### Logical Observer Separation with ☐ Preservation

Logical observers commuting with native necessity distinguish every pair of distinct relations. Write BoxSep for the full schema.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{BoxComm}(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{BoxComm}(E):=(\lambda p^t.E(\Box p))=(\lambda p^t.\Box(Ep)),\qquad\Box p:=(p=\top).
```

- Over H, implies OS + ☐BF + .2, hence ☐Functionality. The entire consequence bundle does not imply BoxSep.
- Over C5, equivalent to InjSep at the same output type and finite list. Rev ⇒ BoxSep ⇒ OS has both implications strict.
- Incomparable with InjSep and SplitMono over C + BF, and with ☐OS over C + ☐BF. Implies neither C5 nor its own boxed schema.
- Reflects every current universal modal law and the specified predicate-universal first-order modal fragment to necessity; see [the exact grammar](native-box-reflection.md). The .3 and 5 conclusions are conditional. Necessary .2 already follows from C + BF (type t) + .2.
- Failure of persistence already occurs on a ten-point full poset satisfying B₂ and ☐OS + ☐BF + ☐Functionality + ☐Atomicity (type t) + ☐.2.
- Over C at every fixed relational output and finite list, Actuality plus internally finite-image BoxSep is exactly Fin_t(All) plus BoxSep. At full scope C is recovered over H; Actuality remains on the finite-image side.
- Full FinBoxSep is exactly BoxSep plus internal finiteness, and derives Actuality and necessary finiteness. Over C the fixed-instance theorem without Actuality holds whenever Δ contains a relational type. FinBoxSep need not persist even with necessary finiteness.

<a id="finite-image-logical-observer-separation-r"></a>
#### Finite-Image Logical Observer Separation

Logical observers with finitely many outputs distinguish every pair of distinct relations.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{FinIm}(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

Put $`\mathrm{Im}_E=\lambda r^t.\exists p^t(Ep=r)`$. Then

```math
\mathrm{FinIm}(E):=\exists Z^{(tt)t}\, .\,\mathrm{FiniteCardinality}_t(Z)\land Z(\mathrm{Im}_E).
```

This uses the [database’s Frege finiteness definition](../../source/topics/classicism/background.md#notation). It is a single finitary condition, with no common bound on the number of outputs.

- Strictly stronger than OS and strictly weaker than endpoint separation; incomparable with reversible separation, C + Atomicity + BF, and ☐OS.
- Together with C5, equivalent to C5 + Atomicity.

<a id="idempotent-native-necessity-logical-observer-separation-r"></a>
#### Idempotent Logical Observer Separation with ☐ Preservation

Idempotent logical observers commuting with native necessity distinguish every pair of distinct relations. Write IdemBoxSep for the full schema.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{BoxComm}(E)\land E\circ E=E\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{BoxComm}(E):=(\lambda p^t.E(\Box p))=(\lambda p^t.\Box(Ep)),\qquad\Box p:=(p=\top).
```

- Strictly implies BoxSep. Over H, C5 + IdemBoxSep is equivalent to Extensionality.
- Incomparable with Rev and End; either conjunction is Extensionality. Neither C5, .3 nor ☐IdemBoxSep follows from IdemBoxSep.
- In full models with singleton individuals on finite rooted posets, holds exactly when every pair of frame points has a join. The specified two-antichain family has exact BoxSep and IdemBoxSep thresholds.

<a id="bounded-stabilization-native-necessity-logical-observer-separation-r"></a>
#### Logical Observer Separation with Bounded Stabilization and ☐ Preservation

For each fixed external integer r≥1, logical observers commuting with native necessity and satisfying E^(r+1)=E^r distinguish every pair of distinct relations. Write B_r for the full schema.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{BoxComm}(E)\land E^{r+1}=E^r\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{BoxComm}(E):=(\lambda p^t.E(\Box p))=(\lambda p^t.\Box(Ep)),\qquad\Box p:=(p=\top).
```

The integer $`r\ge1`$ is a fixed external index. Powers of $`E`$ are finite term iterates; the schema introduces no object-language quantifier over bounds.

- B₁ is IdemBoxSep. Every successive implication B_r ⇒ B_{r+1} is strict, as is each B_r ⇒ BoxSep. The separately boxed hierarchy is strict too.
- For each fixed r, adding C5, Rev or End gives exactly Extensionality; B_r is incomparable with Rev and End.
- One full infinite frame has ☐BoxSep and ☐OS + ☐BF + ☐Functionality + ☐Atomicity (type t) + ☐.2 but fails every fixed B_r on one common proposition pair.
- For every fixed r≥2, B_r need not persist even in a finite full poset: the same ten-point model has B₂ but fails ☐BoxSep and every ☐B_r. B₁ is hereditary only within the stated full poset family.

<a id="factive-logical-observer-separation-r"></a>
#### Factive Logical Observer Separation

Factive logical observers distinguish every pair of distinct relations.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{Fact}(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{Fact}(E):=\forall p^t\, .\,Ep\to p.
```

The types and $`\mathrm{Good}_\Delta`$ are as above. Negation preservation and factivity imply $`\forall p(Ep\leftrightarrow p)`$.

Under Extensionality, truth is endpoint-valued: every true proposition is $`\top`$ and every false proposition is $`\bot`$, so the identity observer alone separates all propositions.

- Over H, each instance is equivalent to Extensionality at its relational type. At type t it is the Fregean Axiom.
- Over C, one propositional instance suffices for full Extensionality; adding the endpoint restriction gives no further strength.
- Over H, OS together with factivity of every qualified observer at one fixed finite list is also equivalent to full Extensionality. Universal factivity alone does not suffice.

<a id="central-logical-observer-separation-r"></a>
#### Central Logical Observer Separation

Observers commuting with every logical observer at the same finite qualification list distinguish every pair of distinct relations. Write CentreSep for the full schema.

```math
\forall X,Y^{\bar\sigma t}\, .\,\Bigl[\forall E^{tt}\, .\,\bigl(\mathrm{Good}_\Delta(E)\land \mathrm{Cent}_\Delta(E)\bigr)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr)\Bigr]\to X=Y.
```

```math
\mathrm{Cent}_\Delta(E):=\mathrm{Good}_\Delta(E)\land\forall G^{tt}\,[\mathrm{Good}_\Delta(G)\to E\circ G=G\circ E].
```

Commutation is identity of whole operations, and ranges over every admitted same-list Good observer. A chosen pairwise commuting family is a different condition.

- Over H, equivalent to IdemBoxSep plus at most four proposition objects, and equivalent to its separately boxed schema. Centrality within the reversible group instead gives C5 plus the same bound; the two principles are incomparable and their conjunction is Extensionality.
- Over C5, equivalent to Extensionality; the propositional instance at any finite Δ containing t already suffices.
- CentreSep + Rev and CentreSep + End are each equivalent to Extensionality. CentreSep is incomparable with Rev and End over H.
- In full finite rooted-poset models with singleton individuals, holds exactly on the singleton and two-point chain. The latter has ☐CentreSep without C5 or Extensionality.

**Sources:** [logical-observers.md](../logical-observers.md) (§§1–8) · [operator-representation.md](../operator-representation.md) (§§2–6) · [logical-observer-hierarchy.md](../logical-observer-hierarchy.md) (§§1–8) · [logical-observer-endpoint-reduction.md](../logical-observer-endpoint-reduction.md) (§§1–4) · [observer-lattice.md](../observer-lattice.md) (§§4–6) · [observer-lattice-models.md](../observer-lattice-models.md) (§§1–3) · [modal-selectors-and-quantifier-reduction.md](../modal-selectors-and-quantifier-reduction.md) (§§1–5) · [logical-separation-with-contingent-barcan.md](logical-separation-with-contingent-barcan.md) (§§2–5) · [necessary-separation-and-atoms.md](necessary-separation-and-atoms.md) (§§1–4) · [reversible-separation-and-pure-truth.md](reversible-separation-and-pure-truth.md) (§§1–5) · [finite-block-symmetry-reversible-gap.md](finite-block-symmetry-reversible-gap.md) (§§1–8) · [reversible-quantifier-observers.md](reversible-quantifier-observers.md) (§§1–4) · [local-conjugacy-and-reversible-observers.md](local-conjugacy-and-reversible-observers.md) (§§2–6) · [split-inverse-logical-observers.md](split-inverse-logical-observers.md) (§§1–4) · [finite-block-symmetry-left-inverse.md](finite-block-symmetry-left-inverse.md) (§§1–7) · [ternary-cantor-observer-model.md](ternary-cantor-observer-model.md) (§§1–9) · [fork-one-sided-inverse-separation.md](fork-one-sided-inverse-separation.md) (§§1–5) · [component-shift-symmetry-reversible-gap.md](component-shift-symmetry-reversible-gap.md) (§§1–8) · [left-inverse-separation-decomposition.md](left-inverse-separation-decomposition.md) (§§1–6) · [finite-pinning-dedekind-propositions.md](finite-pinning-dedekind-propositions.md) (§§1–5) · [plenitude-endpoint-bridge.md](plenitude-endpoint-bridge.md) (§§1–5) · [surjective-logical-observers.md](surjective-logical-observers.md) (§§1–7) · [linear-circular-fibre-left-inverse-gap.md](linear-circular-fibre-left-inverse-gap.md) (§§1–10) · [omega-chain-surjective-observers.md](omega-chain-surjective-observers.md) (§§1–6) · [fixed-point-symmetry-left-inverse-separation.md](fixed-point-symmetry-left-inverse-separation.md) (§§1–7) · [full-cancellative-monoid-observers.md](full-cancellative-monoid-observers.md) (§§1–7) · [root-truth-profile-surjective-separation.md](root-truth-profile-surjective-separation.md) (§§1–7) · [canonical-adjoints-and-image-factorization.md](canonical-adjoints-and-image-factorization.md) (§§2–7) · [integer-shift-predecessor-contingent-barcan.md](integer-shift-predecessor-contingent-barcan.md) (§§1–7) · [native-box-logical-observers.md](native-box-logical-observers.md) (§§1–7) · [injective-observers-and-boolean-transversals.md](injective-observers-and-boolean-transversals.md) (§§1–6) · [idempotent-native-box-observers.md](idempotent-native-box-observers.md) (§§1–7) · [injective-separation-decomposition.md](injective-separation-decomposition.md) (§§1–6) · [native-box-reflection.md](native-box-reflection.md) (§§1–5) · [bounded-stabilization-native-box-observers.md](bounded-stabilization-native-box-observers.md) (§§1–6) · [finite-relative-image-generation.md](finite-relative-image-generation.md) (§§1–6) · [injective-gap-without-split-kernel.md](injective-gap-without-split-kernel.md) (§§1–5) · [exterior-arm-posets-native-box-nonpersistence.md](exterior-arm-posets-native-box-nonpersistence.md) (§§1–5) · [local-transversal-support.md](local-transversal-support.md) (§§1–6) · [zorn-local-transversal-selection.md](zorn-local-transversal-selection.md) (§§1–5) · [local-homogeneity-and-split-observers.md](local-homogeneity-and-split-observers.md) (§§1–4) · [bounded-fibre-degree-logical-observers.md](bounded-fibre-degree-logical-observers.md) (§§1–6) · [finite-image-native-box-observers.md](finite-image-native-box-observers.md) (§§1–5) · [central-logical-observers.md](central-logical-observers.md) (§§1–5) · [finite-colour-propositional-completeness.md](finite-colour-propositional-completeness.md) (§§2–6) · [reversible-fixed-proposition-characterization.md](reversible-fixed-proposition-characterization.md) (§§1–5) · [central-separation-and-four-propositions.md](central-separation-and-four-propositions.md) (§§1–5) · [finite-image-box-reflection.md](finite-image-box-reflection.md) (§§1–5) · [centre-of-reversible-logical-observers.md](centre-of-reversible-logical-observers.md) (§§1–5) · [invariant-components-and-local-support.md](invariant-components-and-local-support.md) (§§1–5) · [bounded-exponent-reversible-observers.md](bounded-exponent-reversible-observers.md) (§§1–5) · [group-identities-reversible-observers.md](group-identities-reversible-observers.md) (§§1–6) · [invariant-components-and-group-identities.md](invariant-components-and-group-identities.md) (§§1–5) · [internally-finite-observer-families.md](internally-finite-observer-families.md) (§§1–5) · [pointwise-reversible-separation.md](../../../integration-register/proofs/pointwise-reversible-separation.md) (Numbered theorem and proof sections) · [order-invariant-parameters.md](../../../integration-register/proofs/observer-parameters/order-invariant-parameters.md) (Numbered theorem and proof sections) · [observer-filter-extension-countermodel.md](../../../integration-register/proofs/observer-filter-extension-countermodel.md) (Numbered theorem and proof sections).

**Evidence:** [Proofs and certificates](../../evidence/RESULT-INDEX.md#logical-observers).

<!-- END OBSERVER PRINCIPLE REFERENCE -->
