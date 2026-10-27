# Necessary observers and cardinal representatives of real subproperties

Ordinary mathematical continuation by OpenAI Codex, 25 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated. No native records, Lean files, compilation targets or historical-novelty claims are changed.

The preceding positive continuation used persistent well-orders to obtain persistent cardinal representatives. This note isolates the weaker property actually sufficient for CH propagation. It also shows exactly what current CH contributes to that property. The missing implication is stated explicitly; this is not an unrestricted C5 + □OS proof.

## 1. Persistent cardinal profiles

Work in C5 + □OS. Fix a counting base with native I*, and let N be its persistent Frege natural-number property. It suffices to use the target type σ as the counting base whenever a real structure at σ is possible: the positive continuation, §10, proves that this supplies necessary I*σ.

For a persistent property Z, let q_Z assert that there is an admitted family of pairwise distinct Dedekind cuts of the fixed rational codes, indexed by Z. The [semantic continuation](necessary-os-ch-semantic-continuation.md), §4, and the positive continuation, §7, prove:

1. q_Z is noncontingent.
2. Relative to any current real structure with carrier X, q_Z is equivalent to the existence of an admitted injection Z → X.
3. Existence or nonexistence of an admitted injection or bijection between two persistent carriers is noncontingent.

Persistence is the native boxed condition P(Z), not merely constancy of the current membership extension. Since P(Z) is boxed, C5 also makes its truth noncontingent. All cardinal comparisons in this note use admitted relation graphs.

Consequently every current real carrier has the same profile on persistent test carriers:

```math
Z\longmapsto (Z\hookrightarrow X)
\quad\text{for persistent }Z
\tag{1}
```

is the endpoint profile Z ↦ q_Z. This statement does not itself assert that the profile has a persistent representative.

## 2. One uncountable persistent cut family gives a current representative

Suppose a current real structure on X satisfies CH. If a persistent Z satisfies

```math
q_Z\quad\text{and}\quad Z\not\hookrightarrow N,
\tag{2}
```

then Z is currently equinumerous with X. Indeed q_Z gives an injection into X. Its image is an admitted subproperty of X and is not countable. Current CH makes that image equinumerous with X, and composition gives Z ≈ X. No well-order of Z or X is used.

There is a useful necessary bound. For every selected test type ρ,

```math
\Box\forall W^{\rho t}\,
 [P(W)\land q_W\to W\hookrightarrow Z]
\tag{3}
```

Currently the implication follows by realizing the W-indexed cuts in X and using X ≈ Z. For each W, its antecedent and consequent are noncontingent under P(W); if P(W) is false, that falsity is itself necessary. Thus the whole displayed implication is necessary for each W. C5 Barcan collects these instances under the W-quantifier. This is a schema in the test type, not an object-language quantifier over types.

Equations (2) also persist. Every possible real field therefore contains an uncountable copy of Z, and no persistent cut-family carrier can exceed Z in the injection ordering. These conclusions do not rule out a possible real carrier or intermediate subset that lacks a persistent cardinal representative. They identify the exact limitation of the profile bound.

## 3. Necessary cardinal representation suffices for CH propagation

Fix a finite list T of allowed representative types. Define CR_{σ,T} as follows:

> For every native real structure at σ and every admitted subproperty A of its carrier, there is a persistent property Z at one of the types in T and an admitted bijection A ≈ Z.

The finite choice of types is a finite disjunction, so this is an ordinary sentence of the fixed language. It does not demand that Z have the same extension as A, that its elements be drawn from A's type, that the bijection be persistent, or that representatives be selected uniformly by an operation.

Then

```math
\mathrm{C5}+\Box\mathrm{OS}+\Box\mathrm{CR}_{\sigma,T}
\vdash
H_\sigma\land U_{\sigma,\mathrm{CH}}
\to\Box U_{\sigma,\mathrm{CH}}
\tag{4}
```

Here Hσ is existence of a real structure, and U_{σ,CH} is the native universal CH sentence. To prove (4), choose a current CH real structure with carrier X₀. Suppose a possible real structure on X has an admitted subproperty A witnessing failure of CH. At that world, necessary CR supplies persistent carriers Z and Y and admitted bijections

```math
X\approx Z,\qquad A\approx Y
\tag{5}
```

Thus q_Z and q_Y hold there. Neither Z nor Y injects into the fixed N: real fields are uncountable, and A is the uncountable subset witnessing failure. All four facts are noncontingent. They therefore hold currently as well. Realize both cut families in X₀. Current CH gives

```math
Z\approx X_0\approx Y
\tag{6}
```

The two outer carriers are persistent, so Y ≈ Z is necessary. At the supposed failure world, compose this bijection with (5). It gives A ≈ X, contradicting that A witnesses failure of CH.

The parameters from a possible world are legitimate typed parameters: C5 supplies the Barcan principles which turn the possible existential counterexample into an existential choice of parameters with the possible matrix. P(Z) and P(Y) are boxed conditions and hold throughout once true there. No current optional premise is illicitly necessitated.

The same argument applies starting at any possible CH real world. At that world, native real-field categoricity and transport of relation graphs make the existence of one CH real structure imply the universal CH sentence required in (4). Hence, under the premises of (4), if any CH real structure is possible, every possible real structure satisfies CH. If none is possible, every possible real structure satisfies ¬CH. Therefore

```math
\mathrm{C5}+\Box\mathrm{OS}+\Box\mathrm{CR}_{\sigma,T}
\vdash
\Box U_{\sigma,\mathrm{CH}}\ \lor\
\Box U_{\sigma,\neg\mathrm{CH}}
\tag{7}
```

As usual, (7) by itself does not settle literal propagation of a vacuous current U_CH when there is no current real structure. Formula (4) retains its actual-existence premise. This note does not infer noncontingency of Hσ from CR.

There is a useful directional asymmetry. For propagating an actual CH failure, it is enough to have current persistent cardinal representatives of the counterexample subset and its real carrier. If these representatives are Z and Y respectively, then q_Z, q_Y, Z ↛ N and Y ↛ Z hold. They are endpoint facts. At any possible real field satisfying CH, the Z-indexed cut family would make Z equinumerous with that field, and the Y-indexed cut family would then inject Y into Z, a contradiction. Thus these current representatives already imply □U_{σ,¬CH}. This is the persistent negative certificate in the [semantic continuation](necessary-os-ch-semantic-continuation.md), §5. The positive direction needs representatives of the hypothetical future counterexample; current CR cannot simply supply them.

## 4. Under current CH, the only current cardinal-representation issue is the continuum

Assume a current CH real structure on X and an admitted bijection between X and a persistent carrier Z of type κ. Every current admitted subproperty A of X then has a persistent cardinal representative at one of the two fixed types κ and ν, where ν is the Frege number type.

For an uncountable A, current CH gives A ≈ X ≈ Z. For a countable A, an injection into N identifies it with an admitted subproperty B of N. Such a B is either bounded or unbounded in the natural-number order. In the bounded case, induction on a bound with B as parameter gives an admitted bijection with a finite numerical initial segment. In the unbounded case, the least element and successive least greater elements give an admitted increasing enumeration by N. Its graph is the least relation closed under the defining successor step; number induction gives totality and uniqueness, and induction on the elements of B gives onto-ness. Empty B is represented by the empty property. No choice of arbitrary witnesses is involved.

N and its initial segments are persistent by C5 arithmetic, including for numerical parameters. Thus these are persistent representatives of the countable case. Conversely, cardinal representation of every real subproperty includes representation of the whole carrier X. Therefore current CH gives the following exact reduction, allowing the fixed number type in the representative list:

```math
\begin{array}{c}
\text{the current real carrier has a persistent cardinal representative}
\end{array}
\quad\Longleftrightarrow\quad
\begin{array}{c}
\text{all its current admitted subproperties have persistent}\
\text{cardinal representatives at the fixed allowed types.}
\end{array}
\tag{8}
```

This is a current reduction. It neither supplies the continuum representative nor propagates the cardinal-representation statement to possible worlds where CH might fail. In particular, it cannot be combined with (7) by simply replacing necessary CR with current CR.

## 5. Cardinal representation does not require a well-order

Here is a conditional model comparison, without a claim about its metatheoretic consistency strength. Let M be any model of ZF in which its real numbers cannot be well-ordered. Take the internally full, two-valued typed interpretation over M, with individual domain ω^M and relational types interpreted by the corresponding internal full function sets. Its proposition algebra is 2.

In this interpretation all property applications are endpoints. Every admitted property is persistent and is its own cardinal representative, via the identity relation. Consequently CR_{σ,{σ}} holds necessarily at every type. C5 holds, and the identity observer is fully qualified and supplies every ordinary observer-separation instance by extensionality of the internal functions.

At σ=et the domain is P(ω)^M, which cannot be well-ordered in M since it has the same cardinality as the reals. Thus the persistent well-order premise on that domain fails. A well-order of its associated cut-code domain would also induce a well-order of P(ω)^M, using the canonical singleton and evaluation embeddings into the higher full function sets, so that premise fails as well.

This verifies, relative to the stated M, that cardinal representation can hold while the earlier well-order hypotheses fail. It does not give contingent CH: the two-valued model has only one truth evaluation. Its purpose is solely to distinguish the new sufficient hypothesis from well-orderability.

## 6. What these reductions leave open

The endpoint cut profile proves (3), but does not produce an uncountable Z satisfying (2). The persistent property of rigid rational cuts is not a general remedy: it describes cuts whose membership values are already endpoints, and need not represent all currently admitted real values.

The entire cut-code domain does contain a code for every admitted cut. It therefore gives a current quotient presentation of the continuum by coextension of cut rows. It does not, merely as a quotient presentation, give an admitted injection of that quotient into a persistent carrier or a persistent transversal. The earlier cut-code well-order argument supplied exactly this missing selector. Identity of cut-code objects cannot replace coextension: codes with the same current rational cut can remain distinct intensional objects.

Thus the new positive route reduces unrestricted CH propagation to a weaker-looking assertion than persistent well-orderability—necessary cardinal representation of real subproperties—but does not establish that assertion from C5 + □OS or from current CH. The subsequent [finite-bit forcing countermodel](necessary-os-ch-cardinal-representation-countermodel.md) refutes unconditional cardinal representation even under C5 + □Rev with one persistent necessarily complete real-field tuple: a generic real subset has no persistent cardinal representative at any finite type. CH is necessarily false in that model. Consequently it does not refute CH propagation or the narrower conjecture that current CH supplies a persistent representative for the continuum. No unrestricted CH implication is claimed here.
