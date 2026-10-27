# Removing Mahlo by a finite-support stage limit

**Result.** Starting with ZFC and a strongly inaccessible cardinal, the symmetric repair construction yields an atomless relational Henkin model of C5 + □OS in which native CH at carrier e is contingent. The same ground real field exists necessarily. Its completeness clause concerns **nonempty bounded admitted subproperties**.

The change is to use only finitely many active repair stages in a forcing condition and a common finite stage bound in each symmetry generator. Centralizers still constrain the canonical actions at all later stages. Every admitted real subset then has a finite-height generic dependency diagram, so the previously proved finite local preservation theorem suffices. The full forcing limit may add reals; the symmetric models do not.

## 1. The finite preservation input

Let V satisfy ZFC with a strongly inaccessible cardinal κ, and let W be the symmetric Solovay model derived from κ. In W, write R for its real line; W satisfies ZF + DC and κ=ω₁.

Use the finite local theorem in [symmetric repair](necessary-os-ch-symmetric-repair.md), §4. A W-specified finite-height iteration Q, with countably many selected coordinates at each height, consists of free countable-partial colorings and repair forcings J(A), where A is forced to be an uncountable subset of the fixed R and depends only on earlier selected coordinates. The theorem gives

```math
Q\Vdash\mathrm{ZF+DC},\quad
\mathbb R=\check R,\quad
\omega_1=\check\kappa,\quad
\check\kappa\not\hookrightarrow\check R
\tag{1}
```

It also gives the independent-unused-color theorem from that note’s §6:

```math
Q\times\mathrm{Col}\Vdash
C_0\not\hookrightarrow C_1\ \land\ C_1\not\hookrightarrow C_0,
\tag{2}
```

where the repair targets ignore the extra coloring, and both cells are uncountable. These are the finite full-diagram arguments over small ZFC universes; no Mahlo reflection is used. The Solovay reconstruction input is Larson–Zapletal, [*Geometric set theory*, author’s draft](https://people.clas.ufl.edu/zapletal/files/balanced14.pdf), Facts 1.7.12–1.7.14, printed pp. 32–33, as specified in the linked proof.

## 2. The limit forcing and its bounded generators

At the base use κ blocks, each containing countably many independent free colorings of R. At every finite repair stage n, use all prefix-supported raw Boolean rows a:R→B_n, with κ copies of J(Â) for each row. The normalized target Â is a’s evaluated subset when that subset is uncountable at that finite prefix, and R otherwise. Distinct raw rows remain distinct labels.

Each finite forcing P_n has concrete countable graph conditions and is countably closed. Let

```math
P_\omega=\bigcup_{n<\omega}P_n
\tag{3}
```

be the finite-support stage limit, using the canonical complete embeddings of prefixes. Thus each condition has a finite stage-height bound, though it may use countably many coordinates and graph edges within that bound. Do not replace (3) by the inverse limit of arbitrary countable-stage conditions.

The group Γ and designated operators D follow the restricted construction in [centralizer localization](necessary-os-ch-centralizer-localization.md), §1, with one modification: every operator’s listed stages have a finite bound. An automorphism acts by canonical transport of raw rows and fiberwise copy permutations. A listed component is a uniform ground copy permutation followed by an action moving countably many literal coordinate pairs. Designated operators are the small automorphisms, within-block proper compressions, finite compositions, and Γ-conjugates. Uniform global copy permutations are not designated solely because their listed stage is finite.

The filter generators are

```math
H(S,D_0)=\mathrm{Fix}(S)\cap
\bigcap_{d\in D_0}C_\Gamma(d),
\tag{4}
```

where S and D₀ are countable and **one finite m bounds every protected coordinate in S and every listed exceptional stage of every d∈D₀**. Canonical row transport above m is still constrained by the centralizer equations. The generator is not merely the inverse image of an unconstrained finite-stage stabilizer.

Finite intersections and conjugations preserve the class (4): take the maximum of the finitely many relevant bounds, including the conjugating automorphism’s bound, and the union of the countable data. Thus this is a normal filter. It is not asserted to be countably complete at the ω-stage; a countable family of generators can have unbounded finite heights. No global DC theorem is inferred from this filter.

The recursive convention remains essential. A support for a row at stage n uses prefix operators and imports them by canonical tail extension, without introducing new later exceptions. At stage n+1 first use the already supported prefix rows, then extend the operators and form the next filter. This gives a genuine stage recursion.

## 3. Finite-height generic localization

Let x⊆check U be a supported name, U∈W, and choose a generator (4) fixing it. Apply the dependency closure from [the independent audit](necessary-os-ch-centralizer-audit.md), §§1–4. Include exception endpoints, close raw rows under the countably many designated maps and partial inverses, protect countable rectangles O×F_O, and include the earlier local systems of every retained or exceptional row.

Every imported row lies at a strictly earlier finite stage. Its support operators are extended canonically, so their import does not create exceptions above that row’s prefix. Consequently the entire countable saturation remains under the original common finite bound m. It yields a fixed finite-height diagram Q with countably many coordinates and with each retained target measurable over earlier retained coordinates.

Projection drops all other graph coordinates. Given q≤π_Q(p), use q on retained coordinates and keep p’s off-system graphs. Their range assertions remain valid under the strengthened prefixes. This lift has finite height, bounded by the maximum of p’s height and m. Therefore π_Q is an actual complete generic projection Pω→Q.

For relative homogeneity, first align compatible Q-parts of p and q. Protect all designated base blocks. At every active repair stage use a common small copy permutation on each designated row orbit, fixing the protected and exceptional indices. The exact commutation identity is

```math
\sigma_{da}\pi_{d,a}=\pi_{d,ga}\sigma_a
\tag{5}
```

Away from exceptions, copy indices are fixed by d and σ is constant on its row orbits. At exceptions, the prefix fixes the exceptional row and σ fixes both endpoints. Dependency closure provides those fixed rows. Above the common generator bound all designated actions are canonical, so the same orbitwise calculation applies without introducing later dependency requirements. Only finitely many stages from p and q need listed aligning components. Thus the aligning automorphism belongs to Γ and to the support of x.

Conditions with compatible projections cannot force contradictory membership in x. The projected membership name is equivalent to x, giving

```math
\text{every supported subset of a ground set has an actual
finite-height generic localization.}
\tag{6}
```

This is a statement about whole names, not individual membership values. The Q-name is itself prefix-supported: protecting its countably many coordinates fixes the local forcing and its ground arguments. Equivalently, above a bound on all listed data, canonical continuation lifts the relevant prefix action and commutes with all later canonical operator actions. Hence the localized membership row is an actual later repair index.

## 4. The symmetric target T

Let T be the hereditary symmetric model for Pω and (4). The ordinary normal-filter construction gives ZF. We make no claim here that the full forcing Pω is countably closed or adds no reals.

Instead, localize any symmetric name for a subset of ω by (6). Its actual Q-generic extension has the same reals as W by (1). Therefore

```math
\mathbb R^T=R
\tag{7}
```

Likewise, a symmetric graph for an injection κ→R would localize to a genuine finite Q-extension, contradicting (1). All ordinals below κ are already countable in W, so T still has ω₁=κ. The absence of κ→R also excludes a well-ordering of R in T.

For A⊆R in T, choose its finite localization and a supported membership row at a finite prefix P_n. If A were countable in that full finite-prefix extension, its enumeration would have an old real code, since P_n adds no reals. The enumeration would then belong to W⊆T. Thus T-uncountability implies uncountability at this finite prefix, and normalization at the next repair stage selects A itself. Its generic bijection R→A is symmetric, supported by its repair coordinate and target row. Hence

```math
T\models\forall A\subseteq R\,
[A\hookrightarrow\omega\ \lor\ A\approx R]
\tag{8}
```

This countability argument compares T with the appropriate finite prefix. It does not compare T with the full Pω-extension, which may contain new enumeration codes.

## 5. The unused-color component F

Form Pω×Col_extra, with Γ acting only on Pω, and use the same filter (4). Call its symmetric model F. None of the Pω repair targets uses this extra coloring.

For any supported F-name x⊆check U, construct Q from its Pω support and retain the entire extra factor. Projection is

```math
(p,r)\longmapsto(\pi_Q(p),r)
\tag{9}
```

After strengthening two compatible projected conditions to a common Q-part and common extra-color condition, the relative automorphism from §3 fixes the extra condition and aligns their Pω-parts. Thus x is a name in an actual Q×Col_extra generic extension. This argument does not require x to have been a T-name.

Localizing names for subsets of ω proves R^F=R, since each finite Q×Col adds no reals. The extra color cells are uncountable in F: every enumeration there has an old real code, whereas generic density puts each color outside every old countable real set.

An F-injection graph between the cells would localize by (9). Its injection property is bounded and absolute between the local extension and the full extension for that fixed graph and those fixed cells. This contradicts (2). Hence C₀ and C₁ are incomparable and uncountable in F. If C₀ were bijective with R, the inclusion C₁⊆R would yield C₁↪C₀. Therefore F fails (8).

## 6. Complete comparison maps at the finite-support limit

Let B_T=RO(Pω) and B_F=RO(Pω×Col_extra), computed in W. The natural inclusion gives a complete embedding i:B_T→B_F. Fix a base block β. Shift its inner coordinates n↦n+1 and send the extra coloring to the freed coordinate (β,0). The resulting map h:B_F→B_T satisfies

```math
hi=j_\beta
\tag{10}
```

At each finite prefix these are the complete maps proved in [stage-preserving compressions](necessary-os-ch-stage-preserving-compressions.md). Normalization commutes with them because countability at a finite prefix is expressed by old-real enumeration codes, and complete maps preserve the resulting joins and meets. These finite-prefix maps cohere.

Their ω-limit projections drop off-image coordinates and pull back the rest. Given q≤π(p), retain p off the image and use q on the image. The result has finite stage support and satisfies every active range assertion by the finite-prefix lifting proof. This proves completeness at the limit without a limit closure or no-new-reals assertion.

Images of supported raw rows remain supported by intersecting with CΓ(jβ). The map i is equivariant. The map h is supported by CΓ(jβ)∩Fix(block β), using (10) on the Pω generators and the fixed image of the extra generator. This is a valid generator with a finite bound. Thus the comparison maps remain admitted under the revised filter.

## 7. Typed interpretation, observer separation, and native CH

Use B=B_T×B_F, the lottery Boolean algebra, with the simultaneous Γ action. Set D_e=R and let D_t be the supported part of B. At relational arrow types take all supported W-functions between the previously constructed domains, exactly as in [the Mahlo synthesis](necessary-os-ch-mahlo-countermodel.md), §§5–7. Normality and finite intersections of supports suffice for lambda abstraction, Boolean operations, and quantifier closure; countable completeness of the ω-stage filter is not used. Quantifier operations are invariant and their values retain the supports of their parameters.

Supported singleton characteristic predicates make whole-object identity crisp at every type, so the same typed interpretation gives C5. Concrete conditions are supported: they have finite stage height and countably many prefix-supported coordinates, whose support intersections share that finite bound. Supported Boolean values are consequently dense in B. Fresh independent base-color bits show atomlessness.

Every pair of concrete Pω conditions is aligned by a small automorphism with a finite stage bound. Such an automorphism is designated and supported by its own centralizer. Thus the complete orbit-cover calculation from [small observer cover](necessary-os-ch-small-observer-cover.md), §§2–6, remains valid. With

```math
E_T(b,c)=(b,ib),\qquad E_F(b,c)=(hc,c),
\tag{11}
```

complete supported Boolean maps give the whole-operation qualification identities at every specified finite type list. The small automorphisms and their compositions with (11) cover every nonzero propositional difference. Pointwise evaluation handles higher-type differences. Every separately closed OS instance has value top, and hence □OS holds in the fixed schema sense.

Admitted finite-arity relations on the fixed R are exactly the HS Boolean rows and hence exactly the symmetric real relations of T or F. A row for one component extends to a global pair row by zero in the other component; the shared Γ action therefore loses no component witness. Currying preserves the correspondence because the action on R is trivial.

The old field operations and natural-number subset are invariant. Every admitted bounded real subproperty or rational cut localizes to a finite Q or Q×Col extension, where no reals are added. Thus its nonempty bounded instance has its old-real supremum. Equivalently, both symmetric ZF models have exactly the old real line, whose usual field is complete internally. Unsupported new cuts in a full Pω-extension are not admitted predicates. The fixed field therefore satisfies Real_e with value (1,1).

Within either symmetric ZF model, complete ordered-field categoricity follows from rational Dedekind cuts without Choice. Its isomorphism between any admitted real structure on a subset of R and the standard field is a symmetric relation and is admitted. From (8), the opposite F-verdict, and the persistent standard-field witness, the exact universal values are

```math
\|U_{e,\mathrm{CH}}\|=(1,0),\qquad
\|U_{e,\neg\mathrm{CH}}\|=(0,1)
\tag{12}
```

Native necessity is the top test. Both corresponding necessary universal assertions therefore have value zero. CH is true at the T component and fails to be necessary; the opposite side behaves analogously at F.

## 8. Exact reduction achieved

This proof removes the Mahlo hypothesis by changing the limit forcing and filter, rather than by asserting that the earlier countable-height witness-reflection argument works below Mahlo. Only the finite local theorem, available from an inaccessible Solovay ground, is used. The full finite-support forcing may add reals and the final symmetric filter need not preserve global DC; neither assertion is needed for the conclusions proved above.

The stronger goal of obtaining the countermodel relative to Con(ZFC) alone remains unresolved by this construction. No compactness or finite-fragment claim is being used to erase the inaccessible hypothesis.

The metatheory audit proves an inaccessible lower bound for the common-ground, persistent-real-field architecture under its stated assumptions, and identifies why direct Truss substitution and uniform real coding of the higher predicates do not supply the missing reduction. These are scoped obstructions, not a lower bound for every native Henkin model of C5 + □OS.
