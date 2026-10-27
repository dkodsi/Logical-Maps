# An atomless CH countermodel from symmetric repairs

The [finite-support limit](necessary-os-ch-inaccessible-countermodel.md) proves the contingent-CH theorem from a strongly inaccessible cardinal. The countable-height construction below is a separate sufficient construction under the stronger Mahlo hypothesis.

**Later reduction, 26 October:** [a revised finite-support limit](necessary-os-ch-inaccessible-countermodel.md) proves the same native countermodel conclusion from a strongly inaccessible cardinal. This original Mahlo construction and its proof are retained. The revised proof does not claim that the countable-height Mahlo argument itself works from an inaccessible.

**Result.** In that set-theoretic construction there is an atomless relational Henkin model of

```math
\mathrm{C5}+\Box\mathrm{OS}_{\rm all}
```

with one persistent, necessarily complete real field at carrier type e, in which native CH is contingent. In particular, current CH does **not** propagate to necessary CH. The opposite universal side is contingent too. Completeness throughout means completeness for **nonempty bounded admitted subproperties**, as stipulated for this project.

The idea is to repair every admitted uncountable real subset by adding a bijection with the real line. Symmetry prevents the individual repairs from forming a global choice function. A second component adds a coloring that the repairs never use; its two color classes remain incomparable. Proper coordinate compressions connect the two components, and separately supported small automorphisms supply observer separation.

The large-cardinal assumption is a sufficient hypothesis for this construction. No claim that it is necessary, or that Con(ZFC) alone suffices, is made.

## 1. The two preservation inputs

Let V satisfy ZFC with a Mahlo cardinal κ, and let W be its symmetric Solovay model. In W write R for the real line; κ is ω₁ and W satisfies ZF + DC. Ground reals and countable real graphs are the fixed data in the construction.

For an uncountable A⊆R, let J(A) consist of countable partial bijections R→A, ordered by extension. Free coloring factors consist of countable partial functions R→2. These forcings have canonical lower bounds for descending countable sequences, obtained by graph union.

The [countable repair theorem](necessary-os-ch-countable-repair.md), §§1–4, applies to a W-specified countable-height iteration with countably many selected coordinates and targets depending only on earlier selected coordinates. It proves that the forcing adds no reals and no injection κ→R. Its Mahlo reflection argument constructs one full diagram over a small ZFC universe: all its old real inputs and all the old members of each target are exhausted at every selected coordinate. Mutually generic extensions of that diagram are compatible. Old-value reflection then excludes κ→R.

The same proof has a second consequence. For such a local repair forcing Q, an independent coloring factor unused by its targets gives two uncountable color classes C₀,C₁ with

```math
Q\times\mathrm{Color}\Vdash
 C_0\not\hookrightarrow C_1\quad\hbox{and}\quad
 C_1\not\hookrightarrow C_0.                         \tag{1}
```

For one direction, choose the full repair diagram over the small universe N first, then color every N-real outside the initial countable color domain 0. A captured injection from the 0-cell into the 1-cell would, by old-value reflection, give in N an injection from its continuum minus a countable set into a countable set. Reverse the colors for the other direction. No repair target depends on the extra coloring. Both cells remain uncountable: a new countable enumeration would be an old real, while a generic coloring has both colors outside every old countable set.

The external inputs for the Solovay reconstruction, as distinguished from the new repair proof, are Larson–Zapletal, [*Geometric set theory*](https://people.clas.ufl.edu/zapletal/files/balanced14.pdf), Facts 1.7.12–1.7.14, printed pp. 32–33. The detailed local note gives the witness-bound reflection argument instead of applying a preservation theorem for Suslin forcing to this more general iteration.

## 2. The symmetric repair component T

Use the concrete countable-support iteration P of length κ described in [centralizer localization](necessary-os-ch-centralizer-localization.md), §§1–7. Its base consists of κ blocks, each with countably many free coloring coordinates. At each subsequent stage α, take all previously supported raw Boolean rows

```math
a:R\longrightarrow B_\alpha,
```

and κ copies of a repair coordinate for each row. The target is the row's evaluated subset if it is uncountable, and R otherwise. Raw rows are distinct coordinate labels even when their current extensions coincide.

The group Γ acts on base blocks and, at repair stages, by canonical earlier-row transport followed by fiberwise copy permutations. A listed copy permutation may have one uniform ground part and a part moving only countably many literal pairs (a,ξ). There are countably many listed stages, bounded below the final κ. A countable prefix may have listed stages cofinal in that prefix.

Designated operators D are small automorphisms, within-block proper compressions, and their finite compositions and Γ-conjugates. A small automorphism moves only countably many base blocks and countably many repair pairs. A compression shifts n to n+1 in one base block and acts at subsequent repair stages by

```math
(a,\xi)\longmapsto(j\circ a,\xi).
```

The normal filter is generated by

```math
\mathrm{Fix}(S)\cap\bigcap_{d\in D_0}C_\Gamma(d)
                                                        \tag{2}
```

for countable protected coordinate sets S and countable D₀⊆D. **Global uniform copy permutations are not designated observers.** Adding their centralizers would admit relations depending on uncountably many repair coordinates and destroy the localization proof.

The cited localization note proves that this filter is normal and countably complete. Its backward support closure retains the earlier dependencies of every protected or exceptional raw row; its rectangular closure synchronizes copy moves along countable designated-operator orbits. Supports for earlier rows use prefix operators with canonical tail extensions. These provisions are part of the construction.

Most importantly, every symmetric subset of a ground set is a name over an **actual complete projection** onto one countable-height dependent repair diagram Q. The projection drops unselected graphs. A stronger selected condition lifts by retaining the other graphs, whose range assertions remain valid under the stronger earlier prefix. Relative homogeneity in the fibers shows that the original name is measurable in this local forcing. This establishes generic reduction, not just a countable list of nominal supports.

The full forcing is countably closed and adds no reals. Its symmetric model T satisfies ZF + DC. The local theorem also gives κ↛R in T. Every symmetric subset A⊆R occurs below a countable stage bound, because its local coordinates have a countable supremum below κ. A later repair coordinate supplies a bijection R→A if A is uncountable. Its graph is symmetric: protect that coordinate and a support for its raw target row. Therefore

```math
T\models\forall A\subseteq R\,
       [A\hookrightarrow\omega\ \lor\ A\approx R].       \tag{3}
```

Countability normalization is unambiguous across these models: an enumeration of a real subset is coded by a real, and none of the forcing extensions adds reals. In particular a set uncountable in T cannot secretly be countable in the full forcing extension.

This is a CH-true component without a well-ordering of R. An initial generic coloring remains Bernstein: every old perfect set has points of both colors by density, and all perfect-set codes are old. Thus it also avoids the earlier obstruction to using a perfect-set-property component as the target of the comparison maps.

## 3. The unused-color component F

Take the forcing P×Color_extra. The same single group Γ acts on P and fixes the extra coloring factor pointwise; use the filter (2). Call its symmetric model F. There are no additional, independently acting component groups.

The P-repair targets are exactly those from §2. None uses the extra coloring. For every symmetric real relation in F, the localization proof gives a complete projection onto

```math
Q\times\mathrm{Color}_{\rm extra},                    \tag{4}
```

where Q is a countable-height repair diagram from W. Indeed, the support closure is the same closure of T-coordinates. In the relative-homogeneity argument first arrange a common local condition, including its extra-color graph; all subsequent Γ actions fix that graph. The projection and lifting argument otherwise remain unchanged.

If F had an injection between the extra color classes, its graph would consequently belong to a genuine extension by (4). The injection assertion is absolute between these same-real models: it concerns the fixed graph, the fixed color classes, and elements of the same R. This contradicts (1). Hence F has two incomparable uncountable real subsets.

If (3) held in F, both color classes would be bijective with R, so they would be equinumerous. Therefore

```math
F\models\neg\mathrm{CH}.                            \tag{5}
```

The argument does not infer the symmetric verdict from an unrelated full-forcing CH verdict. It excludes every symmetric candidate injection by its own local generic projection.

## 4. Complete and supported comparison maps

Let B_T=RO(P) and B_F=RO(P×Color_extra), computed in W. There is a natural complete embedding i:B_T→B_F. Fix one base block β. Compress its inner coordinates by n↦n+1, and send the extra coloring into the freed coordinate (β,0). This defines a complete embedding

```math
h:B_F\longrightarrow B_T,\qquad hi=j_\beta.             \tag{6}
```

Completeness here follows from the explicit strong projection in [stage-preserving compressions](necessary-os-ch-stage-preserving-compressions.md), §§1–4. It drops off-image repair coordinates and pulls back the others. Normalized targets agree because complete embeddings preserve the old-real-coded countability test. The coordinatewise lifting proof works at every countable prefix and at κ: every condition has countably many bounded stage coordinates, and validity is checked along its prefixes.

The row-index domain is closed under compression. If a is supported by H, then j∘a is supported by H∩CΓ(j). Thus every image repair coordinate used by this construction exists.

The map i is equivariant. The map h is supported by

```math
C_\Gamma(j_\beta)\cap\mathrm{Fix}(\text{block }\beta).
                                                        \tag{7}
```

On P-generators this follows from hi=jβ; on the extra generator it follows because its image coordinate is fixed. Complete Boolean generation gives the assertion on all of B_F. The two components use the same Γ action; independent large copy or block permutations are not introduced.

## 5. The supported typed hierarchy and C5

Put B=B_T×B_F, the Boolean algebra of a two-way lottery. This is different from the forcing product used to define F. Γ acts simultaneously on both components. Define

```math
D_e=R,\qquad
 D_t=B_{\rm sym}
   =\{b\in B:\mathrm{Stab}_\Gamma(b)\text{ belongs to the filter}\}.
                                                        \tag{8}
```

The action on R is trivial. At every admitted relational arrow type take all supported W-functions between the previously constructed domains. **The proposition domain is the supported part, not the full ambient completion.**

Interpret quantifiers by W-indexed meets and joins in B. Their values are supported: a group element fixing the formula's parameters permutes its input domain and hence fixes its quantified value. Lambda abstraction is equivariant for the same reason. Boolean operations and the typed quantifier operations are invariant functions. This verifies closure under the fixed relational language.

The endpoint-valued characteristic predicate of any admitted singleton is supported by that object. Leibniz equality is consequently crisp at every type: one for identical domain objects, zero for distinct objects. Native necessity is the global top test. The ordinary typed Boolean interpretation, together with these necessary identities and distinctions, gives C5.

For actual classical truth, use a generic ultrafilter on the internally computed completion B in the usual countable-model presentation. Internal Choice is unnecessary. For an internal family f:I→B, the conditions below its join have a dense refinement below some f(i); meeting this dense set makes existential truth equivalent to truth of one admitted instance. Complements handle universal quantifiers. This is the direct generic truth argument already recorded in [the choice-free typed model](necessary-os-ch-cardinal-representation-countermodel.md), §§3–4.

Every concrete forcing condition is supported: protect its countably many coordinates and intersect supports for their prefix-HS rows. Its Boolean value is therefore in B_sym. The supported algebra is dense in B. Below a nonzero condition a fresh base-color bit has two incompatible extensions, each still supported. Thus the actual proposition algebra in (8) is atomless, not just its ambient completion.

## 6. Necessary observer separation

Small automorphisms already witness weak homogeneity of P. Given p,q, move their countably many occupied base blocks apart. At each active repair stage move only the transformed p's countably many used pairs onto fresh copies. Continue through the countably many active stages. Graph union then gives compatibility. The resulting automorphism d is small, hence designated and supported by CΓ(d).

Consequently, for every nonzero b∈B_T,

```math
\bigvee_{d\ \mathrm{small}}d(b)=1.                       \tag{9}
```

Define complete unital Boolean maps on B by

```math
E_T(b,c)=(b,ib),\qquad E_F(b,c)=(hc,c).                 \tag{10}
```

They are supported by §4. A supported Boolean map sends supported values to supported values by intersecting their supports, so these maps restrict to admitted objects of type tt. Completeness preserves every admitted quantifier meet and join; endpoints and Boolean operations are preserved as well. Thus the whole-operation qualification identities hold for every finite external type list. The same applies to small automorphisms and compositions of these maps.

Lift each small d to the simultaneous product automorphism d̃. If b≠0, then

```math
\bigvee_d\widetilde dE_T(b,c)=(1,1).
```

If c≠0, injectivity of h and (9) give

```math
\bigvee_d\widetilde dE_TE_F(b,c)=(1,1).                 \tag{11}
```

Every nonzero propositional difference therefore has full orbit under admitted qualified observers. For distinct higher-type predicates, choose an argument tuple at which their proposition values differ and use the same cover. All OS instances have value one, hence all their separately boxed, object-variable-closed instances hold. This establishes □OS in its fixed schema sense.

The [independent cover note](necessary-os-ch-small-observer-cover.md), §§2–6, contains the detailed calculation. It does not require homogeneity of F. The cross-component maps are not reversible; no Rev premise has been inserted.

## 7. Exact native CH values and nonvacuity

On the entire carrier D_e=R use the endpoint-valued old field operations, order, natural-number predicate, zero and one. These data are invariant, so the same real structure is persistent in both components.

Admitted finite-arity relations on R are exactly supported Boolean rows, equivalently the canonical symmetric names for subsets of finite powers of R. Both full forcings add no reals. Thus every nonempty bounded admitted real subproperty has its old-real supremum: its rational cut is a real code and remains old. The native induction and ordered-field clauses hold too. The displayed tuple therefore satisfies Real_e with value (1,1).

The correspondence with all symmetric real relations also makes native CH on this tuple exactly (3) in T and (5) in F. For any other admitted real structure on an admitted subset of R, complete ordered-field categoricity is available inside the relevant ZF symmetric model. Its isomorphism is a symmetric relation on R², so it is admitted. The CH verdict is consequently the same for every such structure, wherever it exists.

Write the native universal sides as

```math
U_{e,\mathrm{CH}}
   =\forall\mathcal R\,[\mathrm{Real}_e(\mathcal R)
                              \to\mathrm{CH}(\mathcal R)],
```

and define U_{e,¬CH} similarly. Categoricity supplies the lower bounds, and the total persistent real-field witness supplies the matching upper bounds. Exactly

```math
\|U_{e,\mathrm{CH}}\|=(1,0),\qquad
 \|U_{e,\neg\mathrm{CH}}\|=(0,1).                       \tag{12}
```

Neither value is top. Therefore both □U_{e,CH} and □U_{e,¬CH} have value zero. Their disjunction, the native noncontingency instance, fails. At a generic point on T, U_{e,CH} is true and □U_{e,CH} is false. At a point on F, the opposite universal side is true and fails to be necessary.

These are genuine changes in CH, with real existence necessary and witnessed by the same persistent field. No vacuous universal assertion, change to the completeness convention, or infinitary extension of the object language is used.

## 8. Research status and exact scope

This construction gives a negative answer to the remaining atomless C5 + □OS propagation question under the stated Mahlo/Solovay hypothesis. Analysis had already been settled negatively by the [two-Hechler construction](necessary-os-analysis-countermodel.md), under a weaker metatheory. Rev remains a positive propagation principle and is not claimed for the present model.

The component proofs were audited as ordinary mathematics: separate research agents checked the countable local preservation argument, the centralizer localization and actual generic projections, and the supported comparison-map and observer-cover calculations. These checks are not human verification, native proved records, or Lean certificates. The stronger Mahlo assumption is retained explicitly. Native database entries and published proofs have not been changed; no compilation is needed.
