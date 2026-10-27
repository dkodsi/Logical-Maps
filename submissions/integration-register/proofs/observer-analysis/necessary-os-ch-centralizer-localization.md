# Countable localization with restricted centralizer supports

The purpose is to obtain actual generic projections onto countable repair diagrams. Merely assigning countable stabilizers to names would not suffice for the preservation theorem.

## 1. The concrete systems and the permitted operators

Work in W satisfying ZF + DC, with fixed real line R and κ=ω₁. The intended application is the symmetric Solovay model from a Mahlo cardinal. Build stages α≤κ using concrete countable graph conditions. At the initial level use κ many blocks, each containing countably many free countable-partial colorings of R. At a repair level α, the raw target indices are the Fα-supported Boolean rows

```math
a:R\longrightarrow B_\alpha,
```

where Bα is the complete Boolean algebra of the preceding concrete forcing. Distinct raw rows remain distinct coordinate labels even if their current evaluations coincide. There are κ copies (a,ξ) of every raw target. The evaluated target is a's subset of R when that subset is uncountable, and R otherwise. Thus every factor is a countable-partial-bijection forcing J(Â).

A condition has countably many listed stages, countably many coordinates at each listed stage, and an actual countable real graph at each coordinate. Its earlier prefix forces every required range-membership assertion. The total coordinate and graph data are countable. At limits the condition is determined by its prefixes. This is the primary raw-graph presentation; the proof does not use arbitrary generic-dependent names for coordinate permutations.

An automorphism has a coherent stage-preserving action. At a repair stage its listed component is a uniform ground permutation of the copy indices, the same at every raw row, followed by fiberwise copy permutations moving only countably many coordinate **pairs** (a,ξ). A listed exception never changes the raw row; the raw row changes only through the action already induced on Bα. At the base stage, arbitrary permutations of the κ blocks are allowed. Denote this group by Γ. Listed components may occur at countably many stages; at the final κ-stage they therefore have a common bound below κ. At a countable prefix α, the listed stages may be cofinal in α. No finite-height or strictly bounded-in-α condition is imposed there.

Let D contain the following designated complete Boolean operators:

1. all automorphisms whose base permutation moves countably many blocks and whose repair components move only countably many coordinate pairs in total, with no uniform copy component;
2. the injective within-block compressions and their coherent extensions through raw target indices;
3. finite compositions and conjugates of these operators by Γ.

Every designated operator is injective. Above its listed-stage bound it changes only raw indices and leaves copy indices unchanged. At the listed repair stages it differs from that canonical raw-index action on only countably many coordinate pairs. Uniform global copy permutations belong to Γ but are **not** designated simply on account of being bounded in stage.

The designated coordinate embeddings are required to extend to actual complete Boolean embeddings. For the compressions used here this is the stage-preserving strong-projection construction in [stage-preserving compressions](necessary-os-ch-stage-preserving-compressions.md). It sends (a,ξ) to (j∘a,ξ), and its projection drops off-image coordinates. Countability normalization commutes with j: countability of a real subset is witnessed by an old real enumeration code, so its Boolean value is an old-real-indexed join of meets, preserved by j. No quotient map on currently coextensive raw rows is assumed.

These definitions are recursive. Only rows already admitted at a preceding prefix may appear as indices or in a later listed exceptional component. The designated families are coherent under prefix restriction and canonical tail extension. Extending an operator from a prefix β introduces no new listed exceptions at stages ≥β: later effects are only its canonical raw-index transport. At limits use the coherent concrete graphs and coherent operator actions. The stage-preserving projection/lift argument proves completeness at those limits as well.

## 2. Why the restriction on designated operators is necessary

The larger class of all bounded-stage automorphisms is unsuitable. For example, take ground rows a_x constantly naming the singleton {x}, x∈R; their normalized targets are all R. At one stage let d transpose copies 0 and 1 at every a_x. Then CΓ(d) preserves that pair of copies at every x. The name saying that both corresponding generic bijections send a fixed input into a fixed proper interval is CΓ(d)-invariant and depends on uncountably many independent coordinate pairs. It cannot be reduced to countably many repair coordinates.

This d has only one listed stage but uncountably many moved pairs. It is excluded by §1. Countably many exceptional rows with arbitrary permutations of all their copies would also be a different, stronger allowance; the present argument requires countably many moved pairs.

## 3. The normal, countably complete filter

For a countable set S of protected base blocks and repair coordinates and a countable set D₀⊆D, put

```math
H(S,D_0)=\mathrm{Fix}(S)
          \cap\bigcap_{d\in D_0}C_\Gamma(d),
 \qquad
 C_\Gamma(d)=\{g:gd=dg\}
 \tag{1}
```

Use these subgroups as filter generators. The centralizer of an injective endomorphism is a subgroup of Γ; surjectivity of d is unnecessary. The coordinate action is an actual ground action, so Fix(S) is also a subgroup.

The class D is closed under conjugation by Γ. Uniform copy permutations commute with canonical raw-index transport, so their uniform parts cancel when conjugating a designated operator. The remaining exceptional pairs are images or preimages of countable sets under injective coordinate maps, and remain countable. At the base, conjugation preserves countable moved-block support. Finite composition preserves these properties.

Consequently

```math
gH(S,D_0)g^{-1}=H(gS,gD_0g^{-1})
 \tag{2}
```

This proves normality. Countable intersections are handled by countable unions of the displayed data. DC supplies the countable support witnesses when generators have first been chosen from filter elements. Their stage bounds have a countable supremum below κ. Thus the final filter is countably complete. Its generators can constrain arbitrarily late canonical actions; they are not preimages of finite-stage filters.

Every designated d is supported as an operator by CΓ(d). If a raw row a is supported by H, then d∘a is supported by H∩CΓ(d). Partial inverse rows are supported too: if d∘a=b, then any g commuting with d and fixing b fixes a, by injectivity of d. These observations justify all forward and partial-inverse row closures below.

## 4. Closure of the concrete forcing

For a descending countable sequence of concrete conditions, take the union at each coordinate and then the union of their countable stage supports. Every graph remains countable. Its earlier prefix extends the earlier prefixes which forced the individual range assertions. It therefore forces every retained assertion, and the resulting union is a condition.

This proves countable closure directly, without selecting lower-bound names by a maximum principle. DC gives the usual successive-decision argument: the forcing adds no reals and, more generally, no countable sequences of elements of a fixed ground set. In particular it preserves κ.

The normal-filter hereditary symmetric-name construction gives a ZF model at every prefix. Countable completeness of the filter, together with this closure, gives the usual direct DC preservation argument: build a countable sequence of witnessing HS names below descending conditions and take both the condition lower bound and the intersection of their countably many supports. No separate same-ideal iteration theorem is invoked.

## 5. A fixed countable dependency subsystem

The main induction statement is stronger than pointwise membership in some small extension:

> For every prefix α≤κ and every HS name x⊆check U, U∈W, there is a fixed countable dependent coordinate system Q and a strong projection Pα→Q such that x is forcing-equivalent to a Q-name. Every retained target row is measurable in the earlier retained coordinates.

The induction is on α. For a given x choose a generator (1) fixing it. Starting from S,D₀, perform the following closure in W.

First add all base blocks moved by the designated operators and all their listed exceptional repair pairs, including their images and preimages. These form a countable set. At a repair stage β, close the relevant raw rows under the prefix maps of the countably many designated operators and their partial inverses. Each resulting row orbit O is countable: its elements are obtained by finite words in a countable alphabet of partial functions.

For each touched orbit O let F_O contain the protected and exceptional copy indices occurring there, and retain the rectangle

```math
O\times F_O
 \tag{3}
```

Both factors are countable. Include all endpoint indices of listed exceptions, so (3) is preserved by those exceptions. Off these rectangles the designated operators act on raw indices and keep copy indices fixed.

There is an essential backward dependency step. Include the earlier local systems for every raw row occurring in (3), and for every later exceptional raw row in every designated operator. These are available by the induction hypothesis because a row at stage β belongs to Bβ, strictly before that repair stage. Retain their support witnesses and designated operators as well. A support for such a row is chosen in the prefix system Dβ and imported by canonical tail extension; it introduces no new listed exceptions at stages ≥β. The already proved earlier localization supplies global Boolean measurability, not just equality at the chosen generic.

Repeat these operations countably often. If an added designated operator creates more row orbits or exceptions, process them in a subsequent round. If it adds a later exceptional row, include that row's earlier local system. Each operation has countably many outputs from countably many inputs. DC permits the countable selections. The union has countably many coordinates and designated operators, and its stage heights have one countable supremum below κ. Each finite dependency or operator word appears in some finite closure round, so the union is closed under all the stated requirements.

Call this fixed system Q. It depends on the original name and its support, not on the two forcing conditions later used in the homogeneity argument. Every retained target row is, by construction, a row over its earlier Q-prefix. Its normalized target is measurable there too: no new reals are added, and countability is expressed by the same old real enumeration codes in the local and the full forcing.

Including later exceptional rows is indispensable. The restriction of CΓ(d) to an earlier prefix need not equal the centralizer of d restricted to that prefix. We never use that equality. An earlier action fixing the gathered local data fixes those later exceptional rows, which is what makes its canonical continuation commute with their later components.

## 6. The actual strong projection

Once the target measurability in §5 is available, define π_Q(p) by dropping all unselected graph coordinates. This is a condition, by induction along the selected stages. At a retained coordinate, the original prefix forces its range assertions in a target measured by the earlier Q-prefix. The earlier strong projection therefore forces the same assertions.

More explicitly, if q≤π_Q(p), construct a lift r≤p by using q on the selected coordinates and retaining p on the others. At each stage its prefix extends p's prefix, so all of p's off-system range assertions remain valid; the selected assertions are those of q. Thus

```math
q\leq\pi_Q(p)
 \quad\Longrightarrow\quad
 \exists r\leq p\ [\pi_Q(r)\leq q]
 \tag{4}
```

At a countable limit this is the coordinatewise construction; every finite or shorter ordinal prefix is already valid. There is no requirement that unselected targets ignore the selected coordinates. Strengthening the full prefix preserves their old range assertions, which is sufficient.

Consequently π_Q is a complete generic projection. For a full generic G, its projection G_Q is genuinely Q-generic over W. The retained coordinates, ordered by their original stage positions, form a W-specified countable-height repair diagram. Its target names use only earlier selected coordinates. This is exactly the kind of local forcing to which the countable repair theorem applies.

## 7. Relative homogeneity and the localization induction

Take p,q whose Q-projections are compatible. Using (4), first strengthen them over a common Q-condition. We construct a small automorphism g fixing Q pointwise, commuting with the designated operators retained in the closure, and making gp compatible with q.

At the base stage, the closure contains every block moved by those designated operators. Outside those countably many protected blocks, a countably supported block permutation moves the active blocks of p away from those of q. It fixes the protected blocks and commutes with the designated base actions.

At a repair stage, g's earlier prefix fixes the retained target rows and every later exceptional row whose dependencies have already been gathered. On each raw-row orbit O, choose one countably supported copy permutation fixing F_O and moving the remaining active copies of the transformed p away from those of q. Apply it uniformly to all rows in O. Only countably many orbits are active, and each O is countable, so the total moved-pair set is countable. This is an allowed small component, not a forbidden global uniform operation.

The component commutes with every retained designated operator. In the notation

```math
d(a,\xi)=(da,\pi_{d,a}\xi),\qquad
 g(a,\xi)=(ga,\sigma_a\xi),
```

the needed equation is

```math
\sigma_{da}\pi_{d,a}=\pi_{d,ga}\sigma_a
 \tag{5}
```

Away from exceptions, π is the identity and σ is constant on d-orbits, so (5) holds. At an exceptional row, the prefix of g fixes that row, while σ fixes all exceptional input and output indices included in F_O. Equation (5) holds there too. The same argument at later listed stages uses the backward dependency saturation from §5. At stages where only canonical raw-index renaming remains, commutation follows inductively from commutation of the earlier Boolean actions.

The complete g has countably many exceptional pairs over countably many stages, and is a designated small automorphism. It lies in the original support subgroup H(S,D₀). The transformed conditions agree with the common Q-part and have disjoint outside supports at every repair level. Coordinatewise union gives a common extension.

Thus conditions with compatible Q-projections cannot force contradictory membership statements about x. Project the membership name for x by

```math
x_Q=\{(\pi_Q(p),\check u):
        p\Vdash\check u\in x\}
 \tag{6}
```

Relative homogeneity proves that (6) is forcing-equivalent to x. This completes the induction statement of §5. For raw rows, apply it once to their whole subset name, obtaining one local system for all arguments. Their Boolean values then lie in the local complete subalgebra; uniqueness of preimages gives the local row by Replacement, with no choice of representatives.

At a limit prefix, the closure still has countably many coordinates and stage heights. The same projection and commutation proof works along that countable ordered set. In particular, no false assertion that a countable support must be bounded below a countable limit is used.

## 8. Consequences and limits of the argument

Every symmetric subset of R and every symmetric graph contained in θ×R, θ an ordinal, is evaluated in an actual generic extension by one countable-height repair diagram. Under the Mahlo hypothesis, the local theorem in [countable repair diagrams](necessary-os-ch-countable-repair.md) can therefore be applied. It gives the required absence of an injection κ→R in the symmetric target.

Every symmetric real subset appears below some countable stage bound, and all raw rows receive repairs later. An uncountable subset consequently receives a retained bijection with R. A retained initial generic coloring remains Bernstein because the construction adds no reals. These are the intended WCH and failure-of-perfect-set-property conclusions. The independent unused-color comparison needs the corresponding product localization with all repair targets independent of that extra coloring; the present argument does not waive that requirement.

There is also an admitted-cover candidate, separate from the typed check. With no protected coordinates or designated operators to commute with, the preceding compatibility construction uses only small automorphisms. Thus forcing homogeneity can be witnessed by members of D, each of which is supported by its own centralizer. This avoids the previous failure where only unsupported large forcing automorphisms supplied homogeneity. Turning it into logical observer separation still requires the typed hierarchy, complete-map preservation identities, and component comparison maps to be checked.

In such a typed interpretation the propositional carrier must be the supported part B_sym of the completion, not the whole completion when unsupported Boolean values exist. The present localization statement concerns precisely these supported rows and their associated symmetric names. No conclusion about a full unsupported predicate hierarchy is being drawn.
