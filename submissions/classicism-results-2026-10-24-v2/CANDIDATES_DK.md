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

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,\mathrm{Good}_{\Delta}(E) \\
&\qquad \to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

The schema ranges over finite tuples $\bar\sigma$ of argument types, including the empty tuple, and finite sets $\Delta$ of tested types. $\mathrm{Good}_{\Delta}(E)$ consists of the following clauses:

Boolean operation identities:

$$
\begin{aligned}
&(\lambda p\, .\,E(\neg p))=(\lambda p\, .\,\neg Ep), \\
&(\lambda p,q\, .\,E(p\land q))=(\lambda p,q\, .\,Ep\land Eq), \\
&(\lambda p,q\, .\,E(p\lor q))=(\lambda p,q\, .\,Ep\lor Eq).
\end{aligned}
$$

For each $\sigma\in\Delta$, quantifier operation identities:

$$
\begin{aligned}
&(\lambda F^{\sigma t}\, .\,E(\forall x^\sigma\, .\,Fx))=(\lambda F^{\sigma t}\, .\,\forall x^\sigma\, .\,E(Fx)), \\
&(\lambda F^{\sigma t}\, .\,E(\exists x^\sigma\, .\,Fx))=(\lambda F^{\sigma t}\, .\,\exists x^\sigma\, .\,E(Fx)).
\end{aligned}
$$

For each $\sigma\in\Delta$, Equality laws:

$$
\begin{aligned}
&\forall x^\sigma\, .\,E(x=x), \\
&\forall x,y^\sigma\, .\,\forall F^{\sigma t}\, .\,E(x=y)\to(E(Fx)\to E(Fy)).
\end{aligned}
$$

Over C, the equality laws follow from Boolean preservation. They support the formulation over H, where OS recovers C.

Boolean preservation makes $E\top$ true and $E\bot$ false over H; over C it gives $E\top=\top$ and $E\bot=\bot$. Including these identities leaves the full separation theory unchanged: see the [reduction proof](proofs/logical-observer-endpoint-reduction.md).

- H + OS entails C + BF. **Lean certified** with explicit endpoint identities; [omitting them](proofs/logical-observer-endpoint-reduction.md) uses the ordinary reduction proof.
- Over C: Atomicity (type t) + BF ⇒ OS ⇒ BF, with neither converse valid.
- Over C5 + Actuality: OS ⇔ Atomicity (type t) ⇔ ☐OS.
- OS does not imply Atomicity (type t), Actuality, ND, ☐OS, ☐BF or ☐Functionality.
- Over C5, ☐OS + ◇Actuality entails ☐Plenitude; replacing ☐OS by OS does not suffice.
- Over C, the variants below extend the strict hierarchy:

  $$
  \small\text{Extensionality}\ \Rightarrow\ \mathrm{C5}+\mathrm{Atomicity}_t\ \Rightarrow\ \Box\mathrm{OS}\ \Rightarrow\ \mathrm{OS}\ \Rightarrow\ \mathrm{BF}.
  $$
- Over C, $\mathrm{Good}_\Delta(E)\leftrightarrow\Box\mathrm{Good}_\Delta(E)$; requiring the qualification necessarily does not strengthen separation.
- Over H, OS plus uniqueness of the qualified logical observer at one fixed finite list is equivalent to Extensionality; no endpoint restriction is needed.
- Over C5, propositional separation by Boolean observers preserving the universal quantifier at t is equivalent to full OS.
- Endpoint separation is equivalent over H to C5 + ☐OS + one atom; the boxed propositional $\mathrm{Good}_{\{t\}}$ separation instance suffices in place of ☐OS.
- Even the stronger qualified left-inverse separation principle does not imply C5, ☐OS, its own boxed schema, ☐BF or ☐Functionality; see the [all-maps model](proofs/h-observer-space/finite-block-symmetry-left-inverse.md), §7.
- The [ternary Cantor model](proofs/h-observer-space/ternary-cantor-observer-model.md) has full endpoint-fixing separation for each separate M/Q/P, V/Q/P and N/Q/P class, even necessarily and with boxed BF and Functionality, while Boolean separation fails.
- Qualified left-inverse separation lies strictly between reversible separation and OS, and is incomparable with ☐OS even over C5. With internal finiteness of all propositions, full left-inverse, reversible and endpoint separation coincide.
- Over C + BF, each finite-list left-inverse separation instance is exactly the corresponding reversible instance or ordinary separation together with one qualified left-inverse pair having a true kernel element. The full-H statement is an external schema of alternatives; see the [decomposition](proofs/h-observer-space/left-inverse-separation-decomposition.md).
- Over H, OS + Plenitude at (t,t) is equivalent to endpoint separation; full Plenitude may replace the single instance. Already C + BF (type t) + Plenitude at (t,t) is exactly C5 + Actuality. See the [Plenitude bridge](proofs/h-observer-space/plenitude-endpoint-bridge.md).
- C5 + ☐OS need not imply qualified left-inverse separation, even when every admitted proposition injection is onto and propositions are atomless; see the [linear/circular fibre model](proofs/h-observer-space/linear-circular-fibre-left-inverse-gap.md).
- Separation by currently surjective logical observers lies strictly between Rev and OS and is incomparable with qualified left-inverse separation, even over C + ☐BF + ☐OS. Under C5 it is equivalent to Rev. The [omega-chain classification](proofs/h-observer-space/omega-chain-surjective-observers.md) and finite-block model supply the distinctions.
- The [fixed-point symmetry criterion](proofs/h-observer-space/fixed-point-symmetry-left-inverse-separation.md) strengthens the qualitative-contrast model to C5 + SplitMono without ☐OS or ☐SplitMono.
- SurjSep + SplitMono is strictly stronger than either factor and strictly weaker than Rev. Even ☐SurjSep + ☐SplitMono + C + ☐BF does not imply Rev, witnessed by the [full ℤ×ℕ model](proofs/h-observer-space/full-cancellative-monoid-observers.md). Separate witness families are allowed.
- Over C + BF (type t), Onto(E) implies ☐Onto(E), with E a free parameter. Nevertheless SurjSep implies neither ☐OS nor ☐SurjSep, even with ☐BF and ☐Functionality; see the [root truth-profile model](proofs/h-observer-space/root-truth-profile-surjective-separation.md). Rev ⇒ ☐SurjSep ⇒ SurjSep and ☐SurjSep ⇒ ☐OS are strict. SurjSep does not imply ☐BF, with failure at every admitted type in the integer-shift predecessor model.
- Over C5, [canonical admitted adjoints](proofs/h-observer-space/canonical-adjoints-and-image-factorization.md) give exact individual-observer tests for injection, surjection and reversibility. A Boolean observer commutes with native necessity or possibility exactly when it is injective; this test needs no quantifier-preservation premise.
- BoxSep, separation by logical observers commuting with native necessity, implies ☐BF and .2, hence ☐Functionality. Over C5 it is equivalent to InjSep and lies strictly between Rev and OS. It is incomparable with InjSep and SplitMono over C + BF, and with ☐OS over C + ☐BF; see [native necessity](proofs/h-observer-space/native-box-logical-observers.md).
- IdemBoxSep strictly strengthens BoxSep and becomes Extensionality with C5. The finite-frame join theorem, C5 injective decomposition and scoped modal reflection are in the [updated atlas](proofs/h-observer-space/GRAPH.md).
- Fixed finite stabilization bounds give an unbounded strict native-necessity hierarchy, including a single infinite countermodel to every fixed bound. Over C5, finite relative-generation separation is exactly Rev without assuming injection; J alone does not give K. See the [observer atlas](proofs/h-observer-space/GRAPH.md).
- Over C5, canonical local-support separation is exactly Rev. Boolean Completeness (type t) plus Zorn at t gives exact controlled-inverse criteria; admitted true local homogeneity plus OS gives SplitMono without J. See the [support and selection map](proofs/h-observer-space/GRAPH.md#canonical-local-support-and-selection).
- Over C5, central logical separation is Extensionality and fixed-degree separation is Rev. OS reflects each assumed Boolean Completeness instance into necessity; completeness at t remains strictly below the tt-to-Actuality route. See the [full observer map](proofs/h-observer-space/GRAPH.md).
- Over C5, Rev is exactly triviality of the propositions fixed by all reversible Good-t observers. Centrality, group exponents and finite images have exact finite-domain characterizations; see the [full map](proofs/h-observer-space/GRAPH.md).
- With Rev, any fixed nontrivial group law on all reversible observers gives an exact finite proposition bound. Without Rev, it gives an exact invariant-component condition over C5. Internally finite separating families give the corresponding full separation theory plus FinAll. See the [theorem map](proofs/h-observer-space/MAP.md).

<a id="native-necessity-logical-observer-separation-r"></a>
#### Logical Observer Separation with ☐ Preservation

Logical observers commuting with native necessity distinguish every pair of distinct relations. Write BoxSep for the full schema.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Good}_\Delta(E)\land \mathrm{BoxComm}(E)]\\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

$$
\mathrm{BoxComm}(E):=(\lambda p^t.E(\Box p))=(\lambda p^t.\Box(Ep)),\qquad\Box p:=(p=\top).
$$

- Over H, implies OS + ☐BF + .2, hence ☐Functionality. The entire consequence bundle does not imply BoxSep.
- Over C5, equivalent to InjSep at the same output type and finite list. Rev ⇒ BoxSep ⇒ OS has both implications strict.
- Incomparable with InjSep and SplitMono over C + BF, and with ☐OS over C + ☐BF. Implies neither C5 nor its own boxed schema.
- Reflects every current universal modal law and the specified predicate-universal first-order modal fragment to necessity; see [the exact grammar](proofs/h-observer-space/native-box-reflection.md). The .3 and 5 conclusions are conditional. Necessary .2 already follows from C + BF (type t) + .2.
- Failure of persistence already occurs on a ten-point full poset satisfying B₂ and ☐OS + ☐BF + ☐Functionality + ☐Atomicity (type t) + ☐.2.
- Over C at every fixed relational output and finite list, Actuality plus internally finite-image BoxSep is exactly Fin_t(All) plus BoxSep. At full scope C is recovered over H; Actuality remains on the finite-image side.
- Full FinBoxSep is exactly BoxSep plus internal finiteness, and derives Actuality and necessary finiteness. Over C the fixed-instance theorem without Actuality holds whenever Δ contains a relational type. FinBoxSep need not persist even with necessary finiteness.

<a id="idempotent-native-necessity-logical-observer-separation-r"></a>
#### Idempotent Logical Observer Separation with ☐ Preservation

Idempotent logical observers commuting with native necessity distinguish every pair of distinct relations. Write IdemBoxSep for the full schema.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Good}_\Delta(E)\land \mathrm{BoxComm}(E)\land E\circ E=E]\\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

$$
\mathrm{BoxComm}(E):=(\lambda p^t.E(\Box p))=(\lambda p^t.\Box(Ep)),\qquad\Box p:=(p=\top).
$$

- Strictly implies BoxSep. Over H, C5 + IdemBoxSep is equivalent to Extensionality.
- Incomparable with Rev and End; either conjunction is Extensionality. Neither C5, .3 nor ☐IdemBoxSep follows from IdemBoxSep.
- In full models with singleton individuals on finite rooted posets, holds exactly when every pair of frame points has a join. The specified two-antichain family has exact BoxSep and IdemBoxSep thresholds.

<a id="bounded-stabilization-native-necessity-logical-observer-separation-r"></a>
#### Logical Observer Separation with Bounded Stabilization and ☐ Preservation

For each fixed external integer r≥1, logical observers commuting with native necessity and satisfying E^(r+1)=E^r distinguish every pair of distinct relations. Write B_r for the full schema.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Good}_\Delta(E)\land \mathrm{BoxComm}(E)\land E^{r+1}=E^r]\\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

$$
\mathrm{BoxComm}(E):=(\lambda p^t.E(\Box p))=(\lambda p^t.\Box(Ep)),\qquad\Box p:=(p=\top).
$$

The integer $r\ge1$ is a fixed external index. Powers of $E$ are finite term iterates; the schema introduces no object-language quantifier over bounds.

- B₁ is IdemBoxSep. Every successive implication B_r ⇒ B_{r+1} is strict, as is each B_r ⇒ BoxSep. The separately boxed hierarchy is strict too.
- For each fixed r, adding C5, Rev or End gives exactly Extensionality; B_r is incomparable with Rev and End.
- One full infinite frame has ☐BoxSep and ☐OS + ☐BF + ☐Functionality + ☐Atomicity (type t) + ☐.2 but fails every fixed B_r on one common proposition pair.
- For every fixed r≥2, B_r need not persist even in a finite full poset: the same ten-point model has B₂ but fails ☐BoxSep and every ☐B_r. B₁ is hereditary only within the stated full poset family.

<a id="injective-logical-observer-separation-r"></a>
#### Injective Logical Observer Separation

Currently injective logical observers distinguish every pair of distinct relations. Write InjSep for the full schema.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Good}_\Delta(E)\land \mathrm{Inj}(E)]\\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

$$
\mathrm{Inj}(E):=\forall p,q^t\, .\,Ep=Eq\to p=q.
$$

- SplitMono implies InjSep, which implies OS. Over C5, Rev ⇒ InjSep ⇔ BoxSep ⇒ OS has both outer implications strict.
- Over C5, qualified left inverses of an individual injective Good-t observer correspond exactly to its admitted Boolean transversals.
- The regular-open nonsplitting model fails OS, so it does not refute InjSep ⇒ SplitMono.
- Whether InjSep implies SplitMono remains unresolved over H and over C5.
- Over C5, the full theory is exactly Rev or (OS and J_{t}), where J asserts one injective Good-t observer and a true proposition with no nonzero image part. SplitMono has the same decomposition with K_{t}, and K_{t} implies J_{t}; see [the decomposition](proofs/h-observer-space/injective-separation-decomposition.md).
- Over C5, K implies J strictly. A J witness with any fixed finite image-generation bound gives K; the countermodel to J ⇒ K fails OS, leaving the separation comparison open.

<a id="finite-image-logical-observer-separation-r"></a>
#### Finite-Image Logical Observer Separation

Logical observers with finitely many outputs distinguish every pair of distinct relations.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Good}_{\Delta}(E)\land\mathrm{FinIm}(E)] \\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

Put $\mathrm{Im}_E=\lambda r^t.\exists p^t(Ep=r)$. Then

$$
\mathrm{FinIm}(E):=\exists Z^{(tt)t}\, .\,\mathrm{FiniteCardinality}_t(Z)\land Z(\mathrm{Im}_E).
$$

This uses the [database’s Frege finiteness definition](source/topics/classicism/background.md#notation). It is a single finitary condition, with no common bound on the number of outputs.

- Strictly stronger than OS and strictly weaker than endpoint separation; incomparable with reversible separation, C + Atomicity (type t) + BF, and ☐OS.
- Together with C5, equivalent to C5 + Atomicity (type t).

<a id="reversible-logical-observer-separation-r"></a>
#### Reversible Logical Observer Separation

Logical observers with qualified inverses distinguish every pair of distinct relations.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Good}_{\Delta}(E)\land\mathrm{Rev}_\Delta(E)] \\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

Put $I=\lambda p.p$ and $(E\circ F)(p)=E(Fp)$.

$$
\mathrm{Rev}_\Delta(E):=\exists F^{tt}\, .\,\mathrm{Good}_\Delta(F)\land E\circ F=I\land F\circ E=I.
$$

- Over H, equivalent to involutive separation and to its separately boxed schema; entails C5 + ☐OS + No Pure Contingency, without atoms or Actuality.
- Strictly weaker than endpoint separation and strictly stronger than C5 + ☐OS, even in atomless models. Incomparable with finite-image separation.
- Together with Actuality, the existence of one atom, or the existence of one qualified observer at t with finitely many outputs, equivalent to C5 + Atomicity (type t). The single observer need not separate.
- Forces the proposition algebra to be either atomless or atomic with a true atom.
- Equivalent over H to full logical separation by necessarily bijective observers. Over C5, current bijectivity suffices.
- Over C, equivalent to full separation by invertible observers preserving universal quantification at every finite type list containing t; Boolean preservation and the inverse quantifier laws follow.
- Equivalent over H to full logical separation by observers admitting a same-list qualified right inverse. Qualified left-inverse separation is strictly weaker, even with C5 and its own boxed schema; it need not imply No Pure Contingency.
- Even C5 + ☐SplitMono + No Pure Contingency does not imply reversible separation, as the [component-shift model](proofs/h-observer-space/component-shift-symmetry-reversible-gap.md) shows.
- Implies noncontingency for every pure formula with finitely many individual parameters and finitely many first-order relation parameters whose values on all tuples are endpoints. Arbitrary higher-type parameters are not covered.
- If every admitted injective proposition operation is onto, full left-inverse and reversible separation coincide. C5 + Rev with that condition still need not imply endpoint separation, as the [two-colour model](proofs/h-observer-space/finite-pinning-dedekind-propositions.md) shows.
- Equivalent over H to C5 + separation by currently surjective Good observers. The [explicit section](proofs/h-observer-space/surjective-logical-observers.md) uses the greatest kernel element and a definable fibre representative, without Choice; C5 cannot be omitted.
- SurjSep + SplitMono is a strict weakening, even with both conjuncts boxed. The positive model-family theorem gives ☐SurjSep for full cancellative monoids and also ☐SplitMono when a specified infinite sequence of distinct units is available; a nonunit refutes C5 and hence Rev.
- Strictly stronger than ☐SurjSep, which is strictly stronger than SurjSep and than ☐OS. Individual onto qualification persists over C + BF (type t), while surjective separation need not persist.
- Over C5, equivalent to separation by Good observers with any fixed finite relative image-generation bound, without an injectivity premise; also equivalent to separation by Good observers each having a currently true local Boolean transversal.
- Over C5, exactly separation by Good observers with full or currently true local-transversal support, equivalently by the range of the canonical support normalization. Individual normalized observers need not be injective.
- Over C5, equivalent to separation by Good observers with any fixed fibre-degree bound n≥1; no injectivity, Boolean Completeness or Zorn is needed. The same-profile involution theorem applies to each such observer.

<a id="endpoint-logical-observer-separation-r"></a>
#### Endpoint Logical Observer Separation

Logical observers with outputs restricted to ⊤ and ⊥ distinguish every pair of distinct relations.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Good}_{\Delta}(E)\land\mathrm{End}(E)] \\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

$$
\mathrm{End}(E):=\forall p^t\, .\,Ep=\top\lor Ep=\bot.
$$

The types and $\mathrm{Good}_\Delta$ are as above. In a full model with fixed domains and an admitted evaluation operation, an endpoint observer reports whether $p$ is true at a fixed possible world; it need not report the truth here.

Endpoint-valuedness differs from $\Box\forall p(Ep\leftrightarrow p)$: the latter gives the identity observer over C, whose outputs may remain contingent.

- Over H, the full typed schema is equivalent to C5 + Atomicity (type t), without Actuality.
- Over C, propositional separation testing quantifiers only at t already suffices. The full schema and its separately boxed form are equivalent.
- Strictly stronger than ☐OS and strictly weaker than Extensionality over C.
- Given endpoint separation, Extensionality is equivalent to there being a unique qualified endpoint observer; uniqueness at any one fixed finite list of tested types suffices.
- Under C5, propositional atoms and endpoint observers qualified at $t$ correspond bijectively: $E_a(p)=\Box(a\to p)$ and $a_E=\forall p(Ep\to p)$. Such observers qualify at every finite type list.
- Equivalent to C5 + ☐OS + one atom, and to C5 plus one atom and the single boxed propositional $\mathrm{Good}_{\{t\}}$ separation instance.
- Equivalent over H to OS + Plenitude at (t,t), OS + full Plenitude, C5 + OS + Actuality, and C5 + OS + Boolean Completeness. Both OS and Plenitude are current premises.

<a id="factive-logical-observer-separation-r"></a>
#### Factive Logical Observer Separation

Factive logical observers distinguish every pair of distinct relations.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Good}_{\Delta}(E)\land\mathrm{Fact}(E)] \\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

$$
\mathrm{Fact}(E):=\forall p^t\, .\,Ep\to p.
$$

The types and $\mathrm{Good}_\Delta$ are as above. Negation preservation and factivity imply $\forall p(Ep\leftrightarrow p)$.

Under Extensionality, truth is endpoint-valued: every true proposition is $\top$ and every false proposition is $\bot$, so the identity observer alone separates all propositions.

- Over H, each instance is equivalent to Extensionality at its relational type. At type t it is the Fregean Axiom.
- Over C, one propositional instance suffices for full Extensionality; adding the endpoint restriction gives no further strength.
- Over H, OS together with factivity of every qualified observer at one fixed finite list is also equivalent to full Extensionality. Universal factivity alone does not suffice.

<a id="central-logical-observer-separation-r"></a>
#### Central Logical Observer Separation

Observers commuting with every logical observer at the same finite qualification list distinguish every pair of distinct relations. Write CentreSep for the full schema.

$$
\begin{aligned}
&\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,[\mathrm{Cent}_\Delta(E)]\\
&\qquad\to\forall\bar z^{\bar\sigma}\, .\,(E(X[\bar z])\leftrightarrow E(Y[\bar z])).
\end{aligned}
$$

$$
\mathrm{Cent}_\Delta(E):=\mathrm{Good}_\Delta(E)\land\forall G^{tt}\,[\mathrm{Good}_\Delta(G)\to E\circ G=G\circ E].
$$

Commutation is identity of whole operations, and ranges over every admitted same-list Good observer. A chosen pairwise commuting family is a different condition.

- Over H, equivalent to IdemBoxSep plus at most four proposition objects, and equivalent to its separately boxed schema. Centrality within the reversible group instead gives C5 plus the same bound; the two principles are incomparable and their conjunction is Extensionality.
- Over C5, equivalent to Extensionality; the propositional instance at any finite Δ containing t already suffices.
- CentreSep + Rev and CentreSep + End are each equivalent to Extensionality. CentreSep is incomparable with Rev and End over H.
- In full finite rooted-poset models with singleton individuals, holds exactly on the singleton and two-point chain. The latter has ☐CentreSep without C5 or Extensionality.

**Sources:** [logical-observers.md](proofs/logical-observers.md) (§§1–8) · [operator-representation.md](proofs/operator-representation.md) (§§2–6) · [logical-observer-hierarchy.md](proofs/logical-observer-hierarchy.md) (§§1–8) · [logical-observer-endpoint-reduction.md](proofs/logical-observer-endpoint-reduction.md) (§§1–4) · [observer-lattice.md](proofs/observer-lattice.md) (§§4–6) · [observer-lattice-models.md](proofs/observer-lattice-models.md) (§§1–3) · [modal-selectors-and-quantifier-reduction.md](proofs/modal-selectors-and-quantifier-reduction.md) (§§1–5) · [logical-separation-with-contingent-barcan.md](proofs/h-observer-space/logical-separation-with-contingent-barcan.md) (§§2–5) · [necessary-separation-and-atoms.md](proofs/h-observer-space/necessary-separation-and-atoms.md) (§§1–4) · [reversible-separation-and-pure-truth.md](proofs/h-observer-space/reversible-separation-and-pure-truth.md) (§§1–5) · [finite-block-symmetry-reversible-gap.md](proofs/h-observer-space/finite-block-symmetry-reversible-gap.md) (§§1–8) · [reversible-quantifier-observers.md](proofs/h-observer-space/reversible-quantifier-observers.md) (§§1–4) · [local-conjugacy-and-reversible-observers.md](proofs/h-observer-space/local-conjugacy-and-reversible-observers.md) (§§2–6) · [split-inverse-logical-observers.md](proofs/h-observer-space/split-inverse-logical-observers.md) (§§1–4) · [finite-block-symmetry-left-inverse.md](proofs/h-observer-space/finite-block-symmetry-left-inverse.md) (§§1–7) · [ternary-cantor-observer-model.md](proofs/h-observer-space/ternary-cantor-observer-model.md) (§§1–9) · [fork-one-sided-inverse-separation.md](proofs/h-observer-space/fork-one-sided-inverse-separation.md) (§§1–5) · [component-shift-symmetry-reversible-gap.md](proofs/h-observer-space/component-shift-symmetry-reversible-gap.md) (§§1–8) · [left-inverse-separation-decomposition.md](proofs/h-observer-space/left-inverse-separation-decomposition.md) (§§1–6) · [finite-pinning-dedekind-propositions.md](proofs/h-observer-space/finite-pinning-dedekind-propositions.md) (§§1–5) · [plenitude-endpoint-bridge.md](proofs/h-observer-space/plenitude-endpoint-bridge.md) (§§1–5) · [surjective-logical-observers.md](proofs/h-observer-space/surjective-logical-observers.md) (§§1–7) · [linear-circular-fibre-left-inverse-gap.md](proofs/h-observer-space/linear-circular-fibre-left-inverse-gap.md) (§§1–10) · [omega-chain-surjective-observers.md](proofs/h-observer-space/omega-chain-surjective-observers.md) (§§1–6) · [fixed-point-symmetry-left-inverse-separation.md](proofs/h-observer-space/fixed-point-symmetry-left-inverse-separation.md) (§§1–7) · [full-cancellative-monoid-observers.md](proofs/h-observer-space/full-cancellative-monoid-observers.md) (§§1–7) · [root-truth-profile-surjective-separation.md](proofs/h-observer-space/root-truth-profile-surjective-separation.md) (§§1–7) · [canonical-adjoints-and-image-factorization.md](proofs/h-observer-space/canonical-adjoints-and-image-factorization.md) (§§2–7) · [integer-shift-predecessor-contingent-barcan.md](proofs/h-observer-space/integer-shift-predecessor-contingent-barcan.md) (§§1–7) · [native-box-logical-observers.md](proofs/h-observer-space/native-box-logical-observers.md) (§§1–7) · [injective-observers-and-boolean-transversals.md](proofs/h-observer-space/injective-observers-and-boolean-transversals.md) (§§1–6) · [idempotent-native-box-observers.md](proofs/h-observer-space/idempotent-native-box-observers.md) (§§1–7) · [injective-separation-decomposition.md](proofs/h-observer-space/injective-separation-decomposition.md) (§§1–6) · [native-box-reflection.md](proofs/h-observer-space/native-box-reflection.md) (§§1–5) · [bounded-stabilization-native-box-observers.md](proofs/h-observer-space/bounded-stabilization-native-box-observers.md) (§§1–6) · [finite-relative-image-generation.md](proofs/h-observer-space/finite-relative-image-generation.md) (§§1–6) · [injective-gap-without-split-kernel.md](proofs/h-observer-space/injective-gap-without-split-kernel.md) (§§1–5) · [exterior-arm-posets-native-box-nonpersistence.md](proofs/h-observer-space/exterior-arm-posets-native-box-nonpersistence.md) (§§1–5) · [local-transversal-support.md](proofs/h-observer-space/local-transversal-support.md) (§§1–6) · [zorn-local-transversal-selection.md](proofs/h-observer-space/zorn-local-transversal-selection.md) (§§1–5) · [local-homogeneity-and-split-observers.md](proofs/h-observer-space/local-homogeneity-and-split-observers.md) (§§1–4) · [bounded-fibre-degree-logical-observers.md](proofs/h-observer-space/bounded-fibre-degree-logical-observers.md) (§§1–6) · [finite-image-native-box-observers.md](proofs/h-observer-space/finite-image-native-box-observers.md) (§§1–5) · [central-logical-observers.md](proofs/h-observer-space/central-logical-observers.md) (§§1–5) · [finite-colour-propositional-completeness.md](proofs/h-observer-space/finite-colour-propositional-completeness.md) (§§2–6) · [reversible-fixed-proposition-characterization.md](proofs/h-observer-space/reversible-fixed-proposition-characterization.md) (§§1–5) · [central-separation-and-four-propositions.md](proofs/h-observer-space/central-separation-and-four-propositions.md) (§§1–5) · [finite-image-box-reflection.md](proofs/h-observer-space/finite-image-box-reflection.md) (§§1–5) · [centre-of-reversible-logical-observers.md](proofs/h-observer-space/centre-of-reversible-logical-observers.md) (§§1–5) · [invariant-components-and-local-support.md](proofs/h-observer-space/invariant-components-and-local-support.md) (§§1–5) · [bounded-exponent-reversible-observers.md](proofs/h-observer-space/bounded-exponent-reversible-observers.md) (§§1–5) · [group-identities-reversible-observers.md](proofs/h-observer-space/group-identities-reversible-observers.md) (§§1–6) · [invariant-components-and-group-identities.md](proofs/h-observer-space/invariant-components-and-group-identities.md) (§§1–5) · [internally-finite-observer-families.md](proofs/h-observer-space/internally-finite-observer-families.md) (§§1–5).

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#logical-observers).

<a id="choice-and-rigidity-principles"></a>
## Choice and rigidity

<a id="sections-of-surjections-r"></a>
### Sections of Surjections

Every surjective operation between relational types has a pointwise right inverse.

$$
\forall f^{\sigma\tau}\, .\,\mathrm{Surj}(f)\to\exists g^{\tau\sigma}\, .\,\forall y^\tau\, .\,f(gy)=y\qquad(\sigma,\tau\ne e).
$$

Here

$$
\mathrm{Surj}(f):=\forall y^\tau\, .\,\exists x^\sigma\, .\,fx=y.
$$

- Over C: Functional Choice ⇔ Actuality + Sections of Surjections.
- Actuality does not imply Sections, and Sections do not imply Actuality. The full two-object chain and the atomless Boolean-valued construction provide the respective witnesses (§5).

<a id="strong-sections-of-surjections-r"></a>
#### Strong Sections of Surjections

Every actually surjective operation between relational types has a necessarily correct right inverse.

$$
\forall f^{\sigma\tau}\, .\,\mathrm{Surj}(f)\to\exists g^{\tau\sigma}\, .\,\Box\forall y^\tau\, .\,f(gy)=y\qquad(\sigma,\tau\ne e).
$$

$\mathrm{Surj}$ is as defined under Sections of Surjections. The antecedent asserts actual surjectivity; the inverse equation holds necessarily.

- Over C: ☐Functional Choice ⇔ ☐Actuality + Strong Sections.
- Replacing Strong Sections by ordinary Sections fails, even beside ☐Actuality; the full two-object retract supplies the countermodel (§5).

**Sources:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md) (§§1–6) · [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md) (§§11–20).

**Lean certified:** The Functional Choice and ☐Functional Choice decompositions into Actuality and the corresponding section principles.

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#sections-retractions).

<a id="retractions-of-injections-r"></a>
### Retractions of Injections

Every injective operation between relational types has a pointwise left inverse.

$$
\forall f^{\sigma\tau}\, .\,\mathrm{Inj}(f)\to\exists g^{\tau\sigma}\, .\,\forall x^\sigma\, .\,g(fx)=x\qquad(\sigma,\tau\ne e).
$$

Here

$$
\mathrm{Inj}(f):=\forall x,y^\sigma\, .\,fx=fy\to x=y.
$$

- Over C: Plenitude ⇔ Actuality + Retractions of Injections.
- Requiring a necessarily correct inverse gives exactly C5 over C:

  $$
  \forall f^{\sigma\tau}\, .\,\mathrm{Inj}(f)\to\exists g^{\tau\sigma}\, .\,\Box\forall x^\sigma\, .\,g(fx)=x\qquad(\sigma,\tau\ne e).
  $$

**Sources:** [functional-choice-by-sections.md](source/research/2026-10-22/notes/functional-choice-by-sections.md) (§§1–6) · [choice-uniformization.md](source/research/2026-10-22/notes/choice-uniformization.md) (§§11–20).

**Lean certified:** The Plenitude decomposition; the constituent directions of the C5/strong-retraction characterization.

**Evidence:** [Choice and Plenitude decompose into Actuality and inverse maps](evidence/RESULT-INDEX.md#sections-retractions) · [C5 is exactly strong retractions of actual injections](evidence/RESULT-INDEX.md#c5-strong-retractions).

<a id="world-structure-principles"></a>
## World structure

<a id="individual-profile-realization"></a>
### Individual Profile Realization

One individual predicate can possibly agree with every admitted rigid individual property.

$$
\exists V^{et}\, .\,\forall X^{et}\, .\,\mathrm{Rigid}(X)\to\Diamond c_V(X).
$$

For $V,X^{et}$, put

$$
c_V(X):=\forall x^e\, .\,Vx\leftrightarrow Xx.
$$

Profiles range over admitted rigid individual properties. This differs from the database’s Actual Profile principle.

- Full S5 models with worlds $\mathcal P(D)$ validate this principle, ☐Functional Choice, and any prescribed nonempty finite or infinite individual set $D$. One-world full models refute it while satisfying ☐Functional Choice.
- Nominal models give C + ☐Plenitude + this principle without Functional Choice.
- Over C + ☐Plenitude, replacing $e$ by an unrestricted relational input type yields a diagonal contradiction.

<a id="atomic-individual-profile-realization"></a>
#### Atomic Individual Profile Realization

One individual predicate has an atomic agreement proposition for each admitted rigid individual property.

$$
\exists V^{et}\, .\,\forall X^{et}\, .\,\mathrm{Rigid}(X)\to\mathrm{Atom}_t(c_V(X)).
$$

The agreement proposition $c_V(X)$ is defined under Individual Profile Realization. Profiles again range over admitted rigid individual properties.

- Implies Individual Profile Realization. Over C + ☐Plenitude, each rigid profile corresponds to exactly one world atom for the same $V$.
- Full S5 models with $D=\mathbb N$ and $W=\mathcal P(\mathbb N)$ satisfy the atomic version; $D=\mathbb N$ and $W=\mathcal P(\mathcal P(\mathbb N))$ satisfy the nonunique version but refute the atomic version. Both satisfy ☐Functional Choice in the ZFC metatheory.

**Sources:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) (§§2–4,12–15,35–36) · [structural-world-representation.md](source/research/2026-10-22/notes/structural-world-representation.md) (§§3–8).

**Lean certified:** The finite-profile and atomic-profile fragments.

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#profile-world-algebra).

<a id="numerical-lottery-r"></a>
### Numerical Lottery

A numerical quantity necessarily takes exactly one natural value, and every current natural value is possible.

$$
\begin{aligned}
&\exists L^{\nu_\kappa t}\, .\,\bigl(\Box\exists!n^{\nu_\kappa}\, .\,\mathbb N_\kappa n\land Ln\bigr) \\
&\qquad \land\bigl(\forall n^{\nu_\kappa}\, .\,\mathbb N_\kappa n\to\Diamond Ln\bigr).
\end{aligned}
$$

The counting type $\kappa$ determines the Frege numerical type $\nu_\kappa=(\kappa t)t$, with finite-cardinality predicate $\mathbb N_\kappa$. The principle is a schema in $\kappa$.

- Over C + ☐Plenitude + Axiom of Infinity at $\kappa$: equivalent to an $\mathbb N_\kappa$-indexed independent propositional family, a nonzero partition of $\top$ indexed by $\mathbb N_\kappa$, and an admitted surjection $\mathrm{Atoms}(t)\to\mathbb N_\kappa$.
- Over C + ☐Functional Choice, the $t$-instance is equivalent to Axiom of Infinity (type t).
- Nominal examples satisfy ☐Plenitude and both base-type Infinity axioms while refuting numerical independence, so Infinity alone does not supply this structure without Choice.

**Sources:** [world-cardinality-ucp-20261022.md](source/research/2026-10-22/notes/world-cardinality-ucp-20261022.md) (§§23–27,34).

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#profile-world-algebra).

<a id="infinitary-extension"></a>
## Infinitary principles

<a id="infinitary-comprehension-r"></a>
### Infinitary Comprehension

Every infinitary formula defines a relation with the same truth conditions at every accessible point.

$$
\exists R^{\sigma_1\cdots\sigma_n t}\,\Box\forall x_1\cdots x_n\,\bigl(R[\bar x]\leftrightarrow A\bigr).
$$

A is any classical formula built using arbitrary set-sized well-founded conjunctions and disjunctions, with any set-sized family of typed parameters; R is not free in A. Each instance holds for every simultaneous parameter assignment. The argument tuple is finite and may be empty.

Over H + full typed endpoint separation, the following unboxed range scheme suffices for the same full-model characterization:

$$
\exists R^{\sigma t}\,\forall x^\sigma\,\left(Rx\leftrightarrow\bigvee_{i\in I}x=a_i\right).
$$

Here σ is any original input type, including e; I and the simultaneous parameter family are arbitrary sets. The representation is provable in ZF. See the [intrinsic formulation](proofs/intrinsic-observer-axioms.md).

- With C5, it characterizes full standard relational hierarchies among set-sized models. Atomicity follows; neither Axiom of Infinity is needed. See also the [Arbitrary Atomic Joins characterization](MAIN-RESULTS.md#full-standard-gallin), which assumes propositional Atomicity. The unboxed range formulation over H + endpoint separation has the same original typed reducts; this comparison concerns model classes and canonical expansions.
- The infinitary logical base gives Actuality and propositional Atomicity. Comprehension supplies arbitrary joins, Boolean Completeness, all-type Atomicity and Rigid Comprehension.
- The full-model representation is provable in ZF. Functional Choice holding in every full hierarchy is equivalent to the ambient Axiom of Choice; in ZFC all full hierarchies satisfy ☐Functional Choice. Finite full hierarchies show that neither Axiom of Infinity follows.
- For every infinite regular κ, a model satisfies C5, Atomicity and all instances with fewer than κ parameters, irrespective of formula size, while failing the unrestricted schema.

**Sources:** [infinitary-comprehension.md](proofs/infinitary-comprehension.md) (§§1–4, 5 (source Theorem 5.3), and 6) · [infinitary-canonical-representation.md](proofs/infinitary-canonical-representation.md) (§5) · [intrinsic-observer-axioms.md](proofs/intrinsic-observer-axioms.md) (§§1–7).

**Lean certified:** For the general boxed schema, term-denotation closure + unrestricted original-closed-type Infinitary Comprehension + ☐ND (type t) give faithful full-standard representation of universe-0 categorical premodels, with a separately certified full-standard converse.

**Evidence:** [Infinitary Comprehension and C5 characterize full standard models](evidence/RESULT-INDEX.md#infinitary-comprehension) · [Endpoint separation and unboxed range comprehension characterize full standard models in ZF](evidence/RESULT-INDEX.md#intrinsic-observer-axioms).

<a id="evaluation-principles"></a>
## Evaluation principles

These six propositional operator requirements form a strict hierarchy over C. Their exact equivalents include all-type principles such as Gallin Extensional Comprehension and ☐Plenitude; the countermodels distinguish correctness, necessary bivalence, uniqueness and the order of modal quantification.

For $E^{tt}$, define

$$
\mathrm{Eval}(E):=\forall p^t\, .\,(p\to Ep=\top)\land(\neg p\to Ep=\bot).
$$

### Truth Test

$$
\exists f^{tt}\, .\,\forall p^t\, .\,p\leftrightarrow fp=f\top.
$$

**Equivalent over C:** Actuality.

### Correct Evaluation

$$
\exists E^{tt}\, .\,\mathrm{Eval}(E).
$$

**Equivalent over C:** ND + Actuality.

### Correct Evaluation with ☐Bivalence

$$
\exists E^{tt}\, .\,\mathrm{Eval}(E)\land\bigl(\Box\forall p^t\, .\,Ep=\top\lor Ep=\bot\bigr).
$$

**Equivalent over C:** Gallin Extensional Comprehension; equivalently ND + Strong Actuality.

### Unique Correct Evaluation

$$
\exists!E^{tt}\, .\,\mathrm{Eval}(E).
$$

**Equivalent over C:** C5 + Actuality.

### ☐Correct Evaluation

$$
\Box\exists E^{tt}\, .\,\mathrm{Eval}(E).
$$

**Equivalent over C:** ☐Plenitude.

### Uniform Correct Evaluation

$$
\exists E^{tt}\, .\,\Box\mathrm{Eval}(E).
$$

**Equivalent over C:** Extensionality.

- Necessary bivalence constrains future output values without requiring correctness there.
- Unique Correct Evaluation quantifies over all correct evaluators, including those without necessary bivalence.
- The last two requirements distinguish an evaluator at each world from one fixed evaluator correct at every world.

**Sources:** [actual-truth-evaluator-ladder.md](source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md) (Six-level hierarchy and strictness arguments).

**Lean certified:** Actuality-core conversion and admitted-value lemmas.

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#evaluators-cores).

## Further equivalent formulations

### Diagonal Character Separation

Diagonal Character Separation is equivalent over C to ND (type $t$) + Atomicity (type $t$). Put

$$
w_E:=\forall p^t\, .\,Ep\to p,
$$

$$
\begin{aligned}
&D(E):=E\bot=\bot\land(\forall p^t\, .\,Ep=\top\lor Ep=\bot) \\
&\qquad \land(\forall p^t\, .\,E(\neg p)=\neg(Ep))\land E(w_E).
\end{aligned}
$$

The separation principle is

$$
\forall p,q^t\, .\,p=q\leftrightarrow\forall E^{tt}\, .\,D(E)\to(Ep\leftrightarrow Eq).
$$

**Sources:** [diagonal-characters.md](proofs/diagonal-characters.md) (§§1–4).

**Lean certified.**

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#diagonal-characters).

### Complete Boolean Retractions

Every rigid Boolean subalgebra, complete for admitted families, at every relational type has a complete Boolean retraction. Over C + ☐Plenitude this is equivalent to ☐Functional Choice; the propositional-only version is insufficient.

For each relational type $\tau$, let $\mathrm{CBA}_\tau(A)$ say that $A$ is such a subalgebra, and $\mathrm{CBHom}_\tau(r)$ that $r$ preserves complements and all admitted meets. The principle is

$$
\begin{aligned}\forall A^{\tau t}\, .\,\mathrm{CBA}_\tau(A)\to\exists r^{\tau\tau}\, .\,\bigl[&\mathrm{CBHom}_\tau(r)\land\forall p^\tau\, A(rp)\\&\land\forall q^\tau\,(Aq\to rq=q)\bigr].\end{aligned}
$$

**Sources:** [structural-algebraic-core.md](source/research/2026-10-22/notes/structural-algebraic-core.md) (§§16,18–19,38).

**Evidence:** [Proofs and certificates](evidence/RESULT-INDEX.md#boolean-retractions-choice).
