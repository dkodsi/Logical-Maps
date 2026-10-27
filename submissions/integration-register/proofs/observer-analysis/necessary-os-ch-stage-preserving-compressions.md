# Stage-preserving compressions through raw-index repair products

Date: 26 October 2026. Ordinary research argument; no native record or
formalization claim. Direct attribution: this construction and proof are
`misc`, §§1–6 below. The finite local preservation input belongs to
[the symmetric repair note](necessary-os-ch-symmetric-repair.md); the
bounded-stage localization argument is in
[the mixed-support note](necessary-os-ch-mixed-support-localization.md).

**Result and limit.** Raw Boolean rows permit a same-stage compression of a
repair iteration to lift to a complete embedding, including at its full
countable inverse limit. The proof uses an explicit projection and does not
infer limit genericity from finite-prefix genericity. This resolves an
embedding obligation. It does **not** supply the admitted observers needed
for OS: ordinary forcing automorphisms need not be supported as objects of
type `tt` in the proposed bounded-stage symmetry system (§6).

## 1. Ground and concrete conditions

Work in a ground $`W\models\mathrm{ZF}+\mathrm{DC}`$. Its reals are denoted
$`R`$, and its first uncountable ordinal by $`\kappa`$. The intended ground
is the Solovay model used in the linked repair note. At stage zero take the
countable partial-coloring product with coordinates
$`(\beta,n)\in\kappa\times\omega`$. A condition gives countably much
binary-color information on old real arguments at countably many such
coordinates.

At stage (m+1), index the repair factors by a ground set $`I_m`$ of admitted
raw Boolean rows $`a:R\to B_m`$, together with a copy index
$`\xi<\kappa`$. Do not identify rows that merely have the same current
extension. For a generic filter $`G`$, put

```math
A_a^G=\{x\in R:a(x)\in G\},\qquad
 \widehat A_a^G=
 \begin{cases}
 A_a^G,&A_a^G\text{ is uncountable},\\
 R,&A_a^G\text{ is countable}.
 \end{cases}
```

The factor at $`(a,\xi)`$ consists of countable partial bijections from
$`R`$ to $`\widehat A_a`$. Products have countable support. Concrete
conditions retain their ground raw-index and real-graph data; an earlier
prefix forces the graphs to be valid. The domains of admissible rows and
conditions must be sets in $`W`$. The argument below is conditional on the
chosen supported rows being closed under the indicated compressions.

Countable closure over ZF+DC adds no countable sequences of *any* old set.
Indeed, successively decide the entries of a name for a sequence in a fixed
old set, use DC to choose the descending conditions and decided values,
and take a lower bound. This proof uses witnesses below conditions, not a
Boolean maximum principle. Consequently every countable support and every
countable graph datum appearing in a full prefix extension is already in
$`W`$. This is stronger than the no-new-reals assertion alone.

## 2. The compression and normalization

For each $`\beta<\kappa`$, let $`j_{\beta,0}`$ shift the inner indices in
block $`\beta`$ by $`n\mapsto n+1`$, fixing the other blocks. At a
successor stage the intended coordinate action is

```math
(a,\xi)\longmapsto(j_{\beta,m}\circ a,\xi),             \tag{1}
```

with real graph entries unchanged. Injectivity of the Boolean embedding
implies injectivity of this raw-index map. Duplicate current targets cause
no collision because the indices are raw rows.

If $`G`$ is target-generic and (H=j^{-1}[G]), then

```math
(ja)^G=a^H.                                           \tag{2}
```

The normalization also agrees. Both prefix extensions have exactly the
old reals. A countable enumeration of a set of old reals is encoded by one
old real, and any such proposed enumeration has the same members in both
extensions. Thus the common set in (2) is countable in one extension iff
it is countable in the other. Equivalently, its countability Boolean value
is a join over old enumeration codes of meets of row-complements, so a
complete embedding preserves it. Hence

```math
\widehat A_{ja}^{G}=\widehat A_a^{H}.                   \tag{3}
```

Finite or empty sets are included among the coded countable cases.

## 3. Successor projection and complete embedding

Assume the earlier compression has a strong projection $`\pi_m`$ on the
dense concrete presentation: $`\pi_m j_m`$ is the identity; and whenever
$`q\leq\pi_m(p)`$, there is $`r\leq p`$ with
$`\pi_m(r)\leq q`$. The coordinate-shift map at stage zero has this
property by deleting its omitted coordinate and shifting the remaining
indices back.

Project a target successor condition by deleting coordinates outside the
image of (1), pulling the remaining raw indices back, and retaining their
real graphs. These data belong to $`W`$ by §1. The projected prefix forces
that these are valid source graphs. One can check this directly using the
previous projection: if a source strengthening forced an image-row range
constraint to fail, its lift below the target prefix would contradict the
validity of the target graph. Equation (3) gives the same conclusion for
the normalized targets.

For the lifting property, take a source strengthening $`q`$ of this
projection. Lift its prefix below the original target prefix. At image
coordinates use the graphs prescribed by (j$`q`$); at off-image coordinates
retain the original target graphs. These are disjoint coordinates. All
retained range constraints remain true because the new prefix extends the
old prefix. Their union is a target condition below the original one and
projects below $`q`$.

This is a strong projection at the successor stage. In particular, the
coordinate injection induces a complete embedding of Boolean completions:
for a source dense set, project a target condition, strengthen in the dense
set, and lift back below the target condition. No selection of a maximal
antichain is needed.

## 4. Full countable inverse limit

Let $`P_\omega`$ be the full inverse limit: a condition is a coherent
sequence all of whose finite prefixes are conditions. Define compression
and projection coordinatewise. Every finite-prefix restriction satisfies
the preceding construction. Given a source condition below the projection
of a target condition, retain its compressed graphs on image coordinates
and the target graphs elsewhere. The finite-prefix verification of §3
shows that the resulting sequence belongs to $`P_\omega`$. Thus the same
strong projection and complete embedding exist at the limit.

For precision about the concrete presentation, the countable graph
forcings have canonical lower bounds for descending sequences: coordinate
unions. The corresponding names for unions supply countable closure of
the inverse limit without choosing unrelated lower-bound names. Starting
with any condition, choose a descending sequence whose $`k`$-th member
has concrete data through the first $`k`$ stages. At coordinate $`m`$, take
the union of the concrete graphs in members (k>m). The resulting sequence
extends every member, and each finite prefix is valid. This proves density
of the concrete presentation used above.

## 5. Support calculation for the compression family

The proposed symmetry at stage zero permutes blocks and keeps inner
indices fixed. It normalizes the family $`\{j_\beta:\beta<\kappa\}`$.
At later stages synchronize copy permutations along the equivalence
relation on raw rows generated by all $`j_\beta`$ and their partial
inverses.

For a row with countable dependency-block set $`C`$, assume the established
support action gives $`j_\beta a=a`$ whenever $`\beta\notin C`$, and that
forward moves with $`\beta\in C`$ preserve this support. Partial inverses
introduce no additional blocks: if $`j_\beta a=b`$ and $`b`$ has support
$`C`$ with $`\beta\notin C`$, then $`j_\beta b=b`$, and injectivity gives
(a=b). For $`\beta\in C`$, equivariance and injectivity transfer the
same stabilizer from $`b`$ to $`a`$. Thus the generated orbit is countable.
Synchronizing a copy coordinate along an orbit still involves only
countably many raw coordinates at the same stage.

The compressions commute. They commute at stage zero; at successors (1)
reduces this to the earlier commutation identity, while copy indices and
real graph entries are unchanged. They therefore commute at the inverse
limit too. This permits the compressions, unlike arbitrary prefix
permutations, to commute with arbitrarily late synchronized copy actions.

For $`F=T\times\mathrm{Color}_{\mathrm{extra}}`$, the natural inclusion
$`T\to F`$ and the map $`F\to T`$ sending the extra coordinate to
$`(\beta,0)`$ and the $`T`$-part through $`j_\beta`$ have the indicated
forcing embeddings. The expected support of the latter fixes block
$`\beta`$ and the extra coordinate. This support claim requires the
direct raw-index group action just specified; it does not follow merely
from the existence of an abstract forcing embedding.

## 6. Scope of the stage-preserving compression lemma

At the full inverse limit with the filter generated by bounded-stage
stabilizers, a forcing automorphism is admitted as a `tt` map only if its
conjugation stabilizer contains such a filter member. A prefix block swap
can move a later raw-row orbit to a different orbit. An arbitrarily late
copy permutation can act differently on those two orbits, and then fails
to commute with that prefix swap. Such late actions lie in every proposed
bounded-stage support for the swap. Consequently the swap need not be an
admitted observer, even though it helps establish forcing weak homogeneity.

The compressions avoid that particular problem by the synchronization in
§5, but the finite-word argument alone does not supply observer
separation. In fact, countable conditions can prescribe conflicting values
at every inner coordinate of a block; shifting that block finitely often
does not remove the conflict. Therefore the existing construction does not
establish either OS or its necessity. The complete-embedding and support
lemmas above should be reused separately from any future covering argument.

The full covering argument is in [small observer covers](necessary-os-ch-small-observer-cover.md); the [finite-support limit](necessary-os-ch-inaccessible-countermodel.md) applies it with a strongly inaccessible cardinal.
