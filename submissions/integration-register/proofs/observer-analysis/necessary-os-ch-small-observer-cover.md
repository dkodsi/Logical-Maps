# Small automorphisms and the two-component observer cover

Date: 26 October 2026. Ordinary conditional research lemma; direct
attribution `misc`, §§1–5. No native record or formalization claim.

This note checks the observer-cover obligation for the revised repair
construction. It does not prove the separate local preservation and
symmetric localization theorems. The embedding mechanism is recorded in
[the stage-preserving compression note](necessary-os-ch-stage-preserving-compressions.md).

## 1. Exact hypotheses

Work over $`W\models\mathrm{ZF}+\mathrm{DC}`$, with
$`\kappa=\omega_1^W`$. Let $`T`$ be the length-$`\kappa`$, countable-support
repair forcing with a dense concrete graph presentation. A condition has
countably many stage/raw-row/copy-index/real-graph entries. Its stage
support is bounded below $`\kappa`$. At stage zero the free-color factors
are indexed by blocks $`\beta<\kappa`$, each with inner indices
$`n\in\omega`$. Later factors are indexed by raw rows and copy indices
$`\xi<\kappa`$.

**Raw-row restriction.** The target index set at a stage consists only of
rows already hereditarily symmetric in the preceding prefix system. It is
closed under the prefix group and the specified compressions. Using all
ambient Boolean rows would not justify the small automorphisms or the
dependency-localization induction.

The group $`\Gamma`$ includes the coherent automorphisms with countably
moved base blocks and countably many moved literal pairs
$`(a,\xi)`$ at countably many bounded listed stages. Later effects of a
listed component are the canonical renamings of raw-row indices. Call
these *small automorphisms*. Their inverses have the same form. The normal
filter contains $`C_\Gamma(d)`$ for every small automorphism $`d`$.

The filter also contains centralizers of the designated injective block
compressions $`j_\beta`$, and pointwise stabilizers of any countable list
of whole forcing coordinates. In particular, it may protect an entire
base block. The filter's normality, and its compatibility with the required
localization theorem, are separate hypotheses here. Global uniform copy
permutations need not be admitted as observers and are not used below.

## 2. Small automorphisms suffice for weak homogeneity of T

Let $`p,q\in T`$ be concrete conditions. At stage zero move the countably
many blocks used by $`p`$ onto fresh blocks outside those used by either
condition, using disjoint swaps. This permutation moves only countably
many blocks. The resulting zero-stage conditions have disjoint occupied
coordinates.

Continue through the countable union of the stage supports of $`p,q`$.
Suppose an earlier prefix action has been constructed and the transformed
prefix of $`p`$ is compatible with the prefix of $`q`$. At the next active
stage, the transformed $`p`$ uses countably many raw rows and copy indices.
For each such row, move its used copy indices onto fresh indices outside
both conditions' used indices at that row. Use disjoint swaps, choosing
fresh indices by the ordinal order. Only countably many literal coordinate
pairs are moved in total. The transformed and original graphs now occupy
disjoint coordinates, so their union is a condition above the compatible
prefix: each range-validity assertion remains forced by the corresponding
stronger prefix.

At limit stages retain the coherent previously defined action and the
union of the graph data. Countable support and boundedness ensure that the
final automorphism $`d`$ has the stipulated small form. Thus

```math
\forall p,q\in T\;\exists d\text{ small}\quad d(p)\parallel q \tag{1}
```

There is no need for a uniform permutation at all raw rows. All the rows
at which the constructed permutation acts are prefix-HS, by the index
restriction in §1 and closure under the earlier group action.

Let $`B_T=\mathrm{RO}(T)`$. Equation (1) implies, for every nonzero
$`b\in B_T`$,

```math
\bigvee_{d\text{ small}}d(b)=1                         \tag{2}
```

For if a nonzero condition lay below the complement of that join, choose
a condition below $`b`$ and apply (1). This proof is internal to $`W`$ and
uses its Boolean completion and its set of small automorphisms.

## 3. Why these automorphisms are admitted observers

For a group acting on a Boolean algebra, the action on functions is by
conjugation. The Boolean function $`b\mapsto d(b)`$ is fixed by every
element of $`C_\Gamma(d)`$; hence it is supported by the stipulated
filter. Normality ensures that it sends supported Boolean elements to
supported Boolean elements.

If a relation $`F`$ is supported by $`H_F`$, then its pointwise image
$`d\circ F`$ is supported by $`H_F\cap C_\Gamma(d)`$. The same argument
iterates through every finite relational type. Completeness of the
Boolean automorphism gives, for every admitted family,

```math
d\left(\bigwedge_xF(x)\right)=\bigwedge_xd(F(x)),        \tag{3}
```

and likewise for joins. It preserves negation and endpoints. Whole
identities hold as identities of the corresponding functions;
crisp equality values are endpoints and therefore fixed. Thus these are
qualified observers at every finite type, and their inverses are admitted
too. This is the support step absent from the earlier bounded-stage
construction; forcing weak homogeneity alone would not establish it.

## 4. Supported maps between T and F

Let $`F=T\times\mathrm{Color}_{\mathrm{extra}}`$, with the extra coloring
unused in the repair targets of $`T`$. Let

```math
i:B_T\longrightarrow B_F,
 \qquad h:B_F\longrightarrow B_T                         \tag{4}
```

be complete embeddings. Here $`i`$ is the natural product inclusion, and
$`h`$ sends the extra coloring into base coordinate $`(\beta,0)`$, while
compressing the $`T`$-part by $`j_\beta`$. Consequently

```math
h i=j_\beta                                           \tag{5}
```

Let the simultaneous group act on $`F`$ by its action on $`T`$ and fix the
extra coloring factor pointwise. Then $`i`$ is equivariant. The map $`h`$
is supported by

```math
C_\Gamma(j_\beta)\cap\mathrm{Fix}(\text{block }\beta) \tag{6}
```

Indeed, (5) proves equivariance on the $`T`$-generators for a group element
in (6). The extra generator is sent into the pointwise fixed coordinate
$`(\beta,0)`$. These generators determine the complete embedding, so
equivariance holds on all of $`B_F`$. This verification uses the concrete
generator description of $`h`$; an abstract complete embedding would not
suffice. No automorphisms of the extra coloring factor are needed.

## 5. The product cover has Boolean value one

On $`B=B_T\times B_F`$, define

```math
E_T(b,c)=(b,i b),\qquad E_F(b,c)=(h c,c)                \tag{7}
```

They are complete unital Boolean homomorphisms. The supports in §4 show
that they and all their pointwise higher-type images are admitted. The
same proof as (3) makes them qualified observers. They need not be
invertible.

Every small $`T`$-automorphism $`d`$ lifts to a simultaneous product
automorphism $`\widetilde d=(d,d_F)`$, where

```math
d_F i=i d                                             \tag{8}
```

These lifted automorphisms are admitted by §3. If $`r=(b,c)\ne0`$ and
$`b\ne0`$, equations (2) and (8), together with completeness of $`i`$, give

```math
\bigvee_d\widetilde d E_T(r)
 =\left(\bigvee_d d b,\ i\bigvee_d d b\right)=(1,1)      \tag{9}
```

If instead $`c\ne0`$, injectivity of $`h`$ gives $`h c\ne0`$, and

```math
\bigvee_d\widetilde d E_T E_F(r)
 =\left(\bigvee_d d h c,\ i\bigvee_d d h c\right)=(1,1)  \tag{10}
```

Thus admitted qualified observers cover every nonzero Boolean difference.
In the crisp-identity Boolean semantics, this is precisely the separation
assertion with Boolean value one, hence its necessary form. The argument
uses homogeneity only on $`T`$, not on $`F`$. It proves the OS obligation
conditional on §1 and the supported complete embeddings (4); it does not
establish that the two symmetric components have different CH verdicts.

## 6. Typed interpretation using supported values

The completions $`B_T,B_F,B`$ above are the ambient Boolean algebras used
to prove (2), (9), and (10). The proposition domain of the eventual typed
model is

```math
D_t=B_{\mathrm{sym}}
   =\{b\in B:b\text{ has a support in the chosen filter}\},
 \qquad D_e=R
```

with the trivial group action on $`R`$. Every permitted arrow domain
consists of all supported $`W`$-functions between the preceding domains.
One must not replace $`D_t`$ by all of $`B`$.

Quantifier joins and meets are computed in $`B`$. They belong to
$`B_{\mathrm{sym}}`$: an element fixing the parameters of the indexed
relation permutes its input domain and therefore fixes the resulting
join or meet. Lambda abstraction similarly preserves support. Singleton
predicates are supported by their singled-out objects, so the defined
Leibniz equality is crisp at every type, giving the C5 identity behavior.

An admitted Boolean map $`E`$ supported by $`H_E`$ sends a supported
Boolean value $`b`$ into $`B_{\mathrm{sym}}`$, since $`E(b)`$ is fixed by
the intersection of $`H_E`$ with a support for $`b`$. The pointwise image
of a supported function is supported by the same finite-intersection
argument. Consequently the complete maps used in §§3–5 restrict to the
typed domains and satisfy every finite list of required Good identities.
The joins in (9) and (10) remain legitimate calculations in the ambient
completion proving that the corresponding admitted existential
quantification has value one.

If concrete conditions are HS, $`B_{\mathrm{sym}}`$ is dense in $`B`$.
Thus atomlessness of the ambient forcing algebra also supplies a
supported nonzero proper refinement of every nonzero supported value.
Concrete-condition support and the characterization of base-type
relations as HS names remain obligations of the symmetry/localization
construction, rather than conclusions of the cover lemma alone.

For the stage bookkeeping, an operator in a countable prefix may have
countably many listed components cofinal in that prefix. The required
bound is below the full length $`\kappa`$; no smaller bound inside each
countable prefix is assumed.
