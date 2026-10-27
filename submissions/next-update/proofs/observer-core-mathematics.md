# Mathematics and full standardness in observer cores

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`).

## 1. Setting and results

Use the C5 model and idempotent Good_t observer E of [Logical retractions and typed cores](observer-classical-cores.md), Sections 1-5. In its actual-function presentation, identity at every type is crisp. The same E obeys all typed quantifier laws. Write

```math
r_e=\mathrm{id},\qquad r_t=E,\qquad r_{\sigma\tau}(f)=r_\tau\circ f\circ r_\sigma,\qquad C_\sigma=\mathrm{Fix}(r_\sigma)
```

The fixed hierarchy $`M_E`$ is a C5 Henkin model. An arrow is represented by its normalized ambient extension, and restricts injectively to a function between the fixed domains. Every $`r_{\sigma}`$ is onto $`C_{\sigma}`$. At relational types it is a Boolean retraction. The core quantifiers compute the original infima over the fixed domains. This construction and the already proved current FC/BC inheritance are inputs, not new claims here.

The new conclusions are:

- An endpoint core is full standard exactly when each of its predicate Boolean algebras is externally complete; arbitrary external joins of singleton predicates suffice.
- Quantified individual Infinity has the exact value $`\mathrm{Infinity}_e^c=E(\mathrm{Infinity}_e)`$. In particular, ☐Infinity at e descends.
- Relational Choice and Transversal Choice descend when E regards the ambient instance as true; their necessary instances therefore descend.
- Crisp relational structures on individuals retain their first-order theories. Internal induction alone does not establish standardness.

All assertions distinguish original current truth, E-observed truth, and truth computed inside the normalized model.

## 2. Full standardness and external completeness

In this section E is endpoint-valued. Thus $`C_{t}`$={0,1} and the core is an ordinary extensional two-valued Henkin hierarchy. Identify $`C_{\sigma t}`$ with a Boolean subalgebra of P($`C_{\sigma}`$) by current extension. This is injective by core extensionality. It contains every singleton: for a in $`C_{\sigma}`$ the normalized ambient predicate

```math
H_a(x):=(r_\sigma(x)=a)
```

is admitted, fixed, and restricts to the characteristic function of {a}. For σ=e omit $`r_{e}`$. It also contains complements of all singletons.

**Theorem 2.1.** The following conditions are equivalent:

- **(i)** Every admitted arrow domain of the core is the full external function space between its argument and value domains.
- **(ii)** $`C_{\sigma t}=\mathcal P(C_\sigma)`$ for every admitted σ.
- **(iii)** Every $`C_{\sigma t}`$ is an externally complete Boolean algebra.
- **(iv)** For every σ and external $`A\subseteq C_\sigma`$, the family $`\{H_a:a\in A\}`$ has a supremum in $`C_{\sigma t}`$.

Proof. (i) implies (ii), and (ii) implies (iii) implies (iv). For (iv)->(ii), let J be that supremum. It contains A, since it bounds each H_a. If b is not in A but belongs to J, the available predicate J and not H_b is another upper bound and is strictly below J, a contradiction. Thus J has exactly the extension A. Notice that no unproved preservation of external joins by evaluation was used.

For (ii)->(i), let f:$`C_{\sigma}`$->$`C_{\tau}`$ be an arbitrary external function, where τ is relational. Code pairs (x,y) by their core haecceities

```math
H_{(x,y)}(u,v):=(u=x\land v=y),\qquad\chi=\sigma\tau t
```

Pair codes are injective by core extensionality. By (ii) at chi, the external subset {H_(x,f(x)):x in $`C_{\sigma}`$} has an admitted characteristic predicate A. Hence G(x,y):=A(H_(x,y)) is an admitted core graph of f. Write τ=rho_1...rho_k t and define

```math
F(x,z_1,\ldots,z_k):=\exists y.\,(G(x,y)\land y[z_1,\ldots,z_k])
```

For k=0 use y itself as the last conjunct. Lambda closure supplies F. The unique graph witness is f(x), so F(x) and f(x) agree at all their arguments. Core extensionality makes them identical. This represents every external f, as required. No function type ending in e is used.

**Corollary 2.2.** If each ambient predicate algebra $`D_{\sigma t}`$ is externally complete, every endpoint core is full standard.

Indeed, given any external family A of fixed predicates, let j be its ambient supremum and put k=$`r_{\sigma t}`$(j). Monotonicity makes k an upper bound. If u is a fixed upper bound, j≤u and k≤r(u)=u. Thus k is its supremum in the fixed algebra. Apply Theorem 2.1. We only need ambient suprema of the external singleton families occurring in (iv); completeness of unrelated operation algebras is unnecessary.

This is a genuine weaker test than requiring all ambient function spaces to be full. It concerns external Boolean joins of explicit point predicates. It is not the native internal BC schema, whose families must be admitted.

**Internal principles do not imply fullness.** Start with the full standard two-valued relational hierarchy over omega in the usual ZFC metatheory. It satisfies full FC, full BC, and the quantified $`\mathrm{Infinity}_e`$ axiom. Take a countable elementary submodel in the countable many-sorted Henkin presentation (including the countably many term-operation symbols needed for lambda closure). Every sort is countable; the e-sort is infinite. All those internal sentences remain true. The admitted observer E=id is endpoint-valued, and its core is the entire submodel. But its predicate sort et is countable whereas P($`D_{e}`$) is uncountable. Thus its core is not full standard. This also excludes internal FC+BC+Infinity as a substitute for the external-completeness premise in Corollary 2.2.

## 3. Quantified individual Infinity

Return to an arbitrary idempotent logical E, not necessarily endpoint. Let π=et, κ=(et)t, and h=$`r_{\kappa}`$. Write N, 0 and S for the original Frege natural-cardinality predicate, zero and successor. Put superscript c on their interpretations inside $`M_E`$. All these are the definitions in topics/classicism/background.md, not a separately assumed number sort.

For a fixed cardinal Y, its ambient normalized extension satisfies

```math
Y(P)=E(Y(r_\pi(P)))
```

In particular, hZ(P)=E(Z($`r_{\pi}`$(P))) for every original cardinal Z. The universal individual property 1_pi is fixed by $`r_{\pi}`$.

**Lemma 3.1.** h(0)=0^c and h(SZ)=S^c(hZ), for every original Z.

The zero equation follows from E commuting with universal quantification over e and negation. For successor, let P be a core individual predicate. Deletion P-minus-y:=lambda u.P(u) and u≠y is again a core predicate: individual inequality is crisp and E fixes both endpoints. Consequently

```math
\begin{aligned}h(SZ)(P)&=E(\exists y.\,(P(y)\land Z(P\mathbin{-}y)))\\&=\exists y.\,(P(y)\land E(Z(P\mathbin{-}y)))\\&=\exists y.\,(P(y)\land hZ(P\mathbin{-}y))\\&=S^c(hZ)(P)\end{aligned}
```

The first and last expressions are fixed cardinal objects, so their agreement on all core predicates gives identity. This is why keeping the entire individual domain, rather than replacing it by a quotient, matters.

**Lemma 3.2.** For every original Z,

```math
E(N(Z))\le N^c(hZ)\tag{3.1}
```

Take any core predicate W on core cardinals. Its original normalized extension obeys W h=W and E W=W. By Lemma 3.1 and surjectivity of h, the original induction assertion for this W has exactly its core value:

```math
\begin{aligned}&W(0)\land\forall Z.\,(W(Z)\to W(SZ))\\&\quad=W(0^c)\land\forall Y\in C_\kappa.\,(W(Y)\to W(S^cY))\end{aligned}\tag{3.2}
```

The original definition of N(Z) implies the corresponding induction conditional for W. Apply the Boolean homomorphism E to that inequality. The right-hand W-values and induction assertion in (3.2) are E-fixed. Then take the infimum over core W. The result is (3.1). This argument uses E-observed naturalness, not an illicit assertion that N(Z) is crisp.

**Lemma 3.3.** For every fixed Y,

```math
N^c(Y)=\exists Z.\,(E(N(Z))\land hZ=Y)\tag{3.3}
```

Define the ambient extension of the right-hand predicate by

```math
I(Y):=\exists Z.\,(E(N(Z))\land hZ=hY)
```

It is fixed: it is invariant under h on its input, and E commutes with the displayed existential quantifier, fixes its first conjunct by idempotence, and fixes its equality conjunct by C5. Lemma 3.2 gives I(Y)≤N^c(Y) for fixed Y.

Conversely I is an inductive predicate of the core. Original N(0)=1 and forall Z[N(Z)->N(SZ)]=1 are logical induction facts. Applying E and using its whole quantifier law gives E(N(0))=1 and

```math
\bigl(\forall Z.\,(E(N(Z))\to E(N(SZ)))\bigr)=1
```

These facts and Lemma 3.1 show I(0^c)=1 and closure under S^c. The core induction definition therefore gives N^c(Y)≤I(Y), proving (3.3). The existential in (3.3) ranges over original cardinals. This is an image theorem; it does not assert injectivity of h on natural cardinalities.

**Theorem 3.4.** As a proposition in Im(E),

```math
\mathrm{Infinity}_e^c=E(\mathrm{Infinity}_e)\tag{3.4}
```

By (3.3), the core assertion that some natural cardinal holds of the universal individual property is equivalent, with identical Boolean value, to

```math
\begin{aligned}&\exists Z.\,(E(N(Z))\land hZ(1_\pi))\\&\quad=\exists Z.\,(E(N(Z))\land E(Z(1_\pi)))\\&\quad=E(\exists Z.\,(N(Z)\land Z(1_\pi)))\end{aligned}
```

The first equivalence substitutes hZ for the core-cardinal witness; hZ is fixed and h is onto. Negating gives exactly (3.4).

Consequences and precise scope:

- If original $`\mathrm{Infinity}_e`$ is necessary, its value is 1 and (3.4) makes core $`\mathrm{Infinity}_e`$ necessary as well, hence true.
- If E is truth-correct on this one sentence, actual $`\mathrm{Infinity}_e`$ holds iff core $`\mathrm{Infinity}_e`$ holds. No global truth-correctness is needed.
- If E is endpoint-valued, the common canonical endpoint core determines one shared observed verdict on quantified $`\mathrm{Infinity}_e`$: all endpoint observers agree, by the canonical isomorphism of their cores.
- Every finite individual lower-bound sentence has exactly the same truth in M and $`M_E`$, without an E-correctness premise: the individuals and their crisp identities are unchanged. Thus $`\mathrm{Infinity\ schema}_e`$ transfers in both directions.
- None of this sends original $`\mathrm{Infinity}_t`$ to target $`\mathrm{Infinity}_t`$. An endpoint core has just two propositions. Taking all original propositions as a newly interpreted individual sort is a different construction, not an application of (3.4) at t.

The image/pullback method is adapted from the earlier Actuality world-slice Infinity proof, cited in Section 7. Its new content here is the exact E-observed identity for arbitrary idempotent observers, which avoids the truth-correctness available in an actual-world slice.

## 4. Observed Relational Choice and Transversal Choice

**Theorem 4.1.** If E($`\mathrm{RC}_{\sigma,\tau}`$) is currently true, $`M_E`$ satisfies that Relational Choice instance. The output τ MAY BE e.

Let R be a serial core relation, extended as its normalized ambient function. Write $`\mathrm{Fix}_\tau`$(y) for $`r_{\tau}`$(y)=y, or 1 when τ=e. Form

```math
U(x,y):=R(r_\sigma(x),y)\land\mathrm{Fix}_\tau(y)
```

Its values are E-fixed; it is originally serial because every $`r_{\sigma}`$(x) has a fixed core witness. Consequently E(Serial(U)) is true. Expand the assumed observed RC instance using E's Boolean and whole quantifier laws. It supplies an original S such that the pointwise observed graph

```math
S_E(x,y):=E(S(x,y))
```

is ACTUALLY total, single-valued, and a subrelation of U. In this expansion E(y=z)=(y=z), using crisp all-type identity. The existential over S is legitimate because E commutes with that relation-type quantifier too.

Every selected y is fixed, by U's guard. Now take

```math
T(x,y):=E(S(r_\sigma(x),r_\tau(y)))=r_{\sigma\tau t}(S)(x,y)
```

This is a core relation. On core inputs it is exactly S_E, so its selected outputs are core objects and remain unique. It is a functional subrelation of R in $`M_E`$. This proves the theorem even for individual output.

**Corollary 4.2.** Necessary RC instances descend. Current RC also descends when E is truth-correct on the corresponding RC sentence, or whenever the relevant guarded relations have current selectors with E-fixed values. Persistent selector witnesses suffice in C5: their values satisfy p≤Box(p), and crisp identity makes every such p an endpoint. Thus ambient RC plus suitable graph-type Rigid Comprehension is one sufficient current hypothesis. All-type versions are not silently localized to a single unspecified comprehension instance.

**Theorem 4.3.** If E($`\mathrm{TC}_\sigma`$) is currently true, $`M_E`$ satisfies $`\mathrm{TC}_\sigma`$.

Let R be a core equivalence relation. Extend it to all original objects by leaving every nonfixed object in its own singleton class:

```math
V(x,y):=(\mathrm{Fix}(x)\land\mathrm{Fix}(y)\land R(x,y))\lor(\neg\mathrm{Fix}(x)\land x=y)
```

This is an actual equivalence relation with E-fixed values, so E regards it as an equivalence relation as well. Expanding observed TC gives a predicate F whose observed predicate E o F is an actual V-transversal. On a class containing fixed elements every member is fixed. Therefore $`r_{\sigma t}`$(F) restricts to a core transversal of R. This proves the result, including σ=e. Necessary TC consequently descends.

Why current RC/TC was not asserted without qualification: normalizing an arbitrary selector puts E directly on the predicate head. Current truth of its graph entries need not be preserved by E. The original FC argument avoids this because its witness is an OPERATION used as an argument of the already fixed relation. No counterexample to unrestricted current RC descent is claimed here; that further question is left open by this note.

## 5. Arithmetic and crisp individual structures

Let a relational signature on e be interpreted by ambient predicates with endpoint values at every individual tuple. Every such predicate is fixed by every logical observer: no input normalization is needed at e. Its individual extension is exactly the same in the core.

**Theorem 5.1.** Every first-order sentence in this relational structure has the same truth in the original model and any idempotent observer core. Indeed its Boolean value is the same endpoint in both.

Proof is induction on formulas. Relation atoms agree by hypothesis and individual equality agrees by crisp identity. Boolean cases are immediate. Quantifiers run over the same individuals. An infimum or supremum of endpoint values with its ordinary quantifier truth clause is the relevant endpoint. This proves the quantifier step and hence the theorem.

This applies to arithmetic coded by Zero:et, Succ:eet, Add:eeet, Mul:eeet. An ambient crisp presentation of a first-order arithmetic structure is retained with its whole first-order theory. Its first-order induction instances are retained, but this does not make a nonstandard structure standard or supply all external subsets. Likewise a crisp injective, non-surjective individual graph remains such a graph in the core; no forbidden ee operation is introduced. Thus represented Dedekind infinity with a crisp witness survives directly.

If the endpoint core is full standard by Theorem 2.1 and the shared individual domain is externally infinite, its native quantified $`\mathrm{Infinity}_e`$ holds by the standard finite-cardinality interpretation. The ambient Infinity schema already ensures this external infinitude. This is a separate sufficient route, explicitly using external fullness.

There is a sharper arithmetic conclusion under those same hypotheses. The core's native Frege natural-cardinality domain is exactly

```math
\{(S^c)^n(0^c):n\in\mathbb N_{\mathrm{standard}}\}
```

Every displayed numeral is natural by ordinary finite induction. Conversely, fullness admits the characteristic predicate of this external orbit; it is inductive, so the core's impredicative definition of N excludes every object outside the orbit. The numerals are distinct, since the n-th one holds exactly of the individual properties with n members, and an infinite individual set has properties of every finite size. The defined Sum and Prod relations then give the ordinary addition and multiplication graphs: finite induction proves the intended pairs belong to their impredicative closures, and fullness admits the intended external graphs as tests excluding all other pairs. Thus this is standard Frege arithmetic, not merely a Henkin structure satisfying internal induction. Fullness also supplies all external subsets of this number domain, so its ordinary relational second- order arithmetic has full standard semantics. This conclusion would be false if external fullness were replaced just by internal FC and BC.

## 6. Scope

Theorems 2.1, 3.4 and 4.1 are the principal new mathematical additions. They address respectively external semantic fullness, impredicative cardinality induction, and observed graph selection. The scalar equality in (3.4) is stronger and more informative than a one-way inheritance claim. Ordinary current quantified Infinity and ordinary current RC must not be substituted for their observed or necessary versions without an additional argument.

The original core's current FC and BC inheritance remains available, instance by instance. In an endpoint core, extensionality additionally identifies the usual relational-output RC/FC forms once RC is available; individual outputs continue to use graphs. Internal Choice, Completeness, and Infinity remain compatible with a proper Henkin hierarchy, as the countable example in Section 2 shows.

## 7. Sources

- [The C5 core construction](observer-classical-cores.md), §§1–4: typed fixed domains, canonical isomorphism and Functional Choice/Boolean Completeness inheritance.
- [Actuality world-slice core](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/actuality-world-slice-core.md), §§5, 7–8: the earlier truth-correct slice and image/pullback Infinity argument. Its assumptions and projection differ.
- [The database notation](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/background.md) and [quantified Infinity at e](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/principles/axiom-of-infinity-e.yaml) fix the Frege definitions.

The fullness criterion uses Boolean algebra and typed graph coding. Downward Löwenheim–Skolem supplies the Henkin counterexample. Its proof concerns the constructed classical core; the exact Infinity and observed-choice transfer theorems retain C5 and the original individual domain.
