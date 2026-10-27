# Symmetric repair: finite local preservation

## 1. Metatheory and the localization requirement

Let V satisfy ZFC with inaccessible κ, and let W be its symmetric Solovay model. A *small universe* means N=V[K], where K is generic for forcing of size less than κ. The reals of N are countable in W. The following source facts provide the framework: Larson and Zapletal, *Geometric set theory*, [author's draft](https://people.clas.ufl.edu/zapletal/files/balanced14.pdf), Proposition 1.7.10 and Facts 1.7.12–1.7.14, printed pp. 31–33. Small forcing can capture parameters and conditions, and W can be reconstructed as a symmetric Solovay model over any such N.

Every use of an old subset name below has this convention: its membership is decided by the forcing relation in the reconstructed W, using the retained ground and real parameters. It is **not** evaluated by substituting N's real line into an arbitrary defining formula. This distinction is necessary for arbitrary subset names.

At a successor stage, index repair coordinates by the old uncountable subsets A, with ω₁ copies of each if copy permutations will be used for the iteration's homogeneity. Countably many copies do not suffice to move an arbitrary countable condition support to fresh copies. Use a countable-support product of J(A). Independent domain and range permutations act on each coordinate. A support fixes a countable set of coordinates completely and leaves the others free. On an unsupported coordinate, any two countable partial bijections can be made compatible by domain and range permutations: move their countable domains and ranges off those of the other condition. DC suffices for the countably many choices required by two product conditions.

Consequently, for a fixed old support S, a name for a subset of an old set which is invariant under all automorphisms outside S is determined by the forcing restricted to S. To verify this directly, if two conditions have compatible S-parts, move the unsupported part of one by a support-fixing automorphism until the two full conditions are compatible. They cannot force contradictory membership statements for an invariant name. The usual restriction of its membership name therefore gives an equivalent S-name.

In an iteration, the names indexing S themselves depend on earlier coordinates. Taking those supports recursively gives a countable dependency set at each of finitely many earlier stages, provided the supports and their witnesses are available together. This is the precise local system studied below. The full limit and its support localization are supplied by the [finite-support limit construction](necessary-os-ch-inaccessible-countermodel.md).

There is no corresponding full-product argument. For any fixed small N, the old W-set ℝ\ℝ^N is co-countable in W but has no members in N. It is one of the proposed repair targets. Hence a diagram on N-reals cannot simultaneously contain bijections onto the old parts of every uncountable W-subset. Locality is essential.

## 2. Full free diagrams and old values

First consider a countable product of forcings J(ℝ), possibly together with countably many countable-partial binary-coloring coordinates. A *full N-diagram* b assigns a permutation of ℝ^N to each bijection coordinate and a total binary coloring of ℝ^N to each coloring coordinate. Its entire collection of graphs has size less than κ in N. After a further small collapse it is a countable condition in the W forcing.

Suppose N[H₀] and N[H₁] are mutually generic small extensions of N and q₀,q₁ are conditions in the respective extensions extending b. Their union is a condition. For permutations, a new edge cannot have an old domain or an old range: those have already been exhausted by b. If graph pieces from the two extensions shared a new domain or range, that real would belong to their intersection, hence to N, a contradiction. Coloring disagreements likewise require a shared real, and b has already fixed all old colors. Coordinatewise union therefore supplies a common extension.

This is the balance argument needed here. It also has the following old-value consequence. Let a name τ and its definition parameters be captured over N. If b forces that τ(x) is a real for an old input x, then b forces one specific old real value. Otherwise small capture gives either a possible new value or two incompatible old values. In the first case take mutually generic copies of a deciding condition; their values differ by the intersection property. In the second case realize the two decisions in mutually generic extensions. The preceding union argument makes the deciding conditions compatible in both cases, contradicting functionality. The same argument, with values 0 and 1, says that b decides membership of each old real in every captured subset name.

The resulting old value or old membership set belongs to N: it is defined there using the retained parameters and the reconstructed-W forcing relation. This is the direct form of the argument used in Larson–Zapletal, Theorem 9.1.1, printed pp. 201–202; that published theorem assumes a Suslin forcing. For the non-Suslin dependent systems below, the graph and forcing-interpretation checks must be supplied directly, not inferred from that theorem's name.

## 3. Enlarging a free diagram to contain many witnesses

Here is a useful strengthened conclusion. Suppose b is a full N-diagram for the preceding free product, and a countable family of captured names A_m is forced uncountable below b. There is a larger small ZFC universe N′ and a full N′-diagram b′ extending b such that, for every m, the set

```math
A_m[b'] = \{x\in\mathbb R^{N'}: b'\Vdash_W x\in A_m\}
 \tag{1}
```

has size continuum in N′. This is a statement about a well-chosen extension of the virtual diagram; no assertion is made that every full diagram has this property.

For each m, the N-reals form a countable set in W. Uncountability therefore supplies a condition q_m≤b and a real x_m outside N with q_m forcing x_m∈A_m. Small capture presents these as names for a small forcing over N, with the real forced new. Include a small collapse making b countable. After another small collapse, build perfect families of such generic extensions which are mutually generic in every finite collection. One can use a common countable product of the required small posets, and partition a perfect family into countably many disjoint perfect pieces, one for each requested witness family and one additional reserved piece. All constructions take place in a single small ZFC N′.

For every branch in the mth piece retain its deciding condition and witness. Witnesses are distinct: equality between two branch values would put that new real in the intersection of the corresponding mutually generic extensions. Thus there are continuum many m-witnesses in N′. Their deciding conditions are pairwise compatible by §2, and, more strongly, their union at each coordinate is still a partial injection or partial coloring.

The unused reserved piece prevents a partial injection from exhausting only one side. In each reserved generic extension choose a real new over N. These reals are pairwise distinct and none occurs in a graph from any retained branch. At every permutation coordinate they provide continuum many unused domain elements and continuum many unused range elements. Both complements therefore have exactly continuum size in N′. Choice in N′ completes each partial injection to a permutation; countably many such completions can be chosen together. Complete coloring coordinates arbitrarily.

The resulting b′ is a full N′-diagram extending every retained condition. Hence it forces each retained witness into its designated A_m. Equation (1) has continuum many members, as required. This proves a potential-uncountability property for the free product even though particular full diagrams can make the old part of a forced-uncountable set countable.

## 4. Dependent repair coordinates: finite local preservation

**Local preservation theorem.** Let W be the symmetric Solovay model over a ZFC ground V with inaccessible κ, so κ=ω₁^W. Fix a finite h. Let P₀ be a countable product of the countable-partial binary-coloring forcing on ℝ^W and/or J(ℝ^W). For each n<h, fix in W a countably enumerated family of Pₙ-names ⟨Ȧₙ,ₘ:m∈ω⟩ such that

```math
P_n\Vdash A_{n,m}\subseteq\check{\mathbb R}^{,W}
       \text{ is uncountable},\qquad
 P_{n+1}=P_n*\prod_{m\in\omega}J(\dot A_{n,m})
 \tag{2}
```

The product uses countable supports. The coordinates and their target names are a preselected W-sequence; they are not all targets of an ambient symmetric product. Interpret this sequence and all auxiliary names in small universes by the reconstructed-W forcing convention of §1. Then Pₕ has a dense σ-closed concrete-graph presentation and forces

```math
\mathrm{ZF+DC},\qquad
 \mathbb R=\check{\mathbb R}^{,W},\qquad
 \omega_1=\check\kappa,\qquad
 \text{there is no injection }\check\kappa\longrightarrow\mathbb R
 \tag{3}
```

In particular, it adds no reals and preserves the absence of an uncountable well-ordered sequence of distinct reals. The conclusion also holds below a condition which forces the stated target hypotheses. It is not a preservation assertion for arbitrary σ-closed forcing or for an unlocalized all-target product.

At each level of (2) there are countably many repair coordinates. The target A_j of a coordinate j uses only strictly earlier levels. The induction maintains two properties:

1. Below every condition there is a full diagram over some small universe. At coordinate j this is a bijection from the old real line onto the old part of A_j decided by its full earlier prefix.
2. Any full diagram can be enlarged so that a prescribed countable family of names forced uncountable has continuum many old members; during this enlargement it is possible to reserve continuum-sized unused domains and ranges at each incomplete repair coordinate.

The important point is how to obtain the reserved **range**, because a repair target need not be the full real line. Fix a full N-diagram b and all the conditions one wants to amalgamate. For each coordinate j, use the forced uncountability of A_j to obtain a small-generic new real y and a condition forcing y∈A_j. Take that deciding condition **only in the earlier-level forcing**. Retain a perfect family of mutually generic copies, disjoint from all other witness families. At coordinate j these branches add no graph edges. Other branches cannot use their y-values because the small generic universes intersect only in N; and b uses only N-reals. Thus the y-values remain unused ranges at coordinate j.

Amalgamate all retained graph pieces and complete the diagram level by level in N′. At coordinate j, the completed earlier prefix extends all of its range-witness decisions, so it still forces every reserved y into A_j. It also decides old-real membership in A_j by the earlier-level balance argument. The range complement therefore has continuum many members. A separate reserved family supplies continuum many unused domain reals. Both complements have size continuum in N′, so a bijective completion exists. Complete all coordinates at the level, then continue to the next level.

Why the completed diagram is balanced is also explicit. In mutually generic extensions of N′, a new graph edge at coordinate j cannot have an old input, since the full diagram already assigns every old input. It cannot have an old output either: the earlier prefix decides whether that old real belongs to A_j, and every old member of A_j is already exhausted by the full bijection. Hence potential new conflicts involve reals from the intersection of the two extensions, which are old, and are impossible. The earlier-level union forces every range-membership assertion needed for the united graph. Induction on the finitely many levels gives a common extension.

For the dense-diagram part of the induction, begin with the given condition and capture its real-coded graphs and the definitions of all the countably many local target names. Complete the earlier levels first. Apply their potential-uncountability property to the next level's countably many target names, enlarging the small universe if necessary. Their old parts now have continuum size. The already prescribed countable graph can be extended to a bijection, reserving complements as in §3. Repeat through the finitely many levels.

For the representation argument, inductively use a dense σ-closed presentation of the earlier levels. A successor condition consists of an earlier condition p and a countable sequence of names for countable graphs. DC in the earlier extension supplies simultaneous enumerations, hence one real code for the sequence. Because earlier forcing adds no reals, strengthen p to decide that code. The result is an actual W-sequence of graphs g_j, with p forcing that each g_j has its required range. This gives a dense concrete presentation. For a descending chain in that presentation, take a lower bound of the prefixes and the coordinatewise unions of the graphs. The lower bound forces their range-membership assertions and injectivity, and the union remains countable. This proves σ-closure of the presentation by induction. At each finite step DC remains available: σ-closed forcing over ZF+DC preserves DC; see Karagila–Schilhan, [*Sequential and distributive forcings without choice*](https://eprints.whiterose.ac.uk/id/eprint/194697/1/distributivity.pdf), §4, accepted manuscript p. 7, discussion preceding Theorem 4.4. Countable closure with DC also preserves ω₁ and adds no reals, giving the corresponding parts of (3).

For uniform interpretation, capture the entire countable local system, including its sequence of target names, as one W-parameter definable from a real and a ground parameter. Enlarge N to include that real. Over N, and subsequently over each small N′, use the remaining Levy-collapse forcing relation for assertions about the uniquely defined local system in the reconstructed symmetric Solovay model. Homogeneity of the remaining collapse makes assertions with parameters in N′ unambiguous. In particular, (1) is defined by this forcing relation and Separation in N′; it does not assert that the arbitrary target-name definition is absolute when its quantifiers are restricted to N′. Small capture supplies the real-coded deciding conditions needed for the perfect-family construction. Each such decision remains valid in the common reconstruction over a larger small universe. Arbitrary target names are not being treated as Suslin codes.

These two paragraphs address a fixed countable finite-height system. They do not show that a name in the complete symmetric iteration reduces to such a system: in particular, a coordinate support forced countable need not already come with a uniform countable ground set of names. The [finite-support limit construction](necessary-os-ch-inaccessible-countermodel.md) verifies that reduction for the required application.

Finally, suppose a condition forces an injection ω₁^W→ℝ. Capture that condition, the injection name, and the local system's parameters in a small universe. The dense-diagram construction yields a full diagram b over a possibly larger small N. It forces each value at an ordinal α<κ to be one specific N-real by §2. Replacement, using the reconstructed-W forcing relation, produces in N an injection κ→ℝ^N. This is impossible because κ remains inaccessible in N and |ℝ^N|<κ. This proves the final assertion of (3), completing the theorem.

## 6. An independent unused coloring forces failure of weak CH

Let Col be the forcing of countable partial maps ℝ^W→2. If c is its generic union, write C_ε={x:c(x)=ε}. The word *unused* means that no target name or condition relation in the repair system depends on this additional coloring. It does not prohibit dependence on other colorings already included in P₀.

**Independent-color theorem.** For every finite local repair system Pₕ satisfying §4's hypotheses,

```math
P_h\times\mathrm{Col}\Vdash
 C_0,C_1\text{ are uncountable},\quad
 C_0\not\hookrightarrow C_1,\quad
 C_1\not\hookrightarrow C_0
 \tag{4}
```

Hence Pₕ×Col forces ¬WCH. This is a product with an independent additional color coordinate; it is not the iteration which subsequently repairs the subsets defined from that coordinate.

The product has a dense σ-closed presentation and adds no reals. Each cell is uncountable: for every old countable D⊆ℝ and every product condition, a fresh real outside D and the countable color domain can be assigned the chosen color. Therefore neither cell is contained in any old countable set. Any countable set of reals in the extension has an enumeration coded by a real and so is old. This proves the first assertion of (4).

Suppose (p,r) forces that a name f is an injection C₀→C₁. Capture the local repair system, p, r, an enumeration of dom(r), and the definition of f in a small universe. By §4, enlarge it to a small N over which a full repair diagram b≤p exists. This construction concerns only Pₕ and is independent of the extra coloring. In N let D=dom(r), which is countable there, and define the full coloring d of ℝ^N by extending r and assigning color 0 everywhere outside D.

The pair (b,d) is a balanced full diagram for the product. The repair-coordinate union argument is unchanged. At the extra color coordinate, two mutually generic extensions can disagree only at a common real; such a real belongs to N and its color is already fixed by d. Thus coordinatewise unions remain compatible. Section 2's old-value argument applies to f with this combined diagram.

For each x∈ℝ^N\D, the combined diagram forces x∈C₀ and hence forces f(x) to be a unique N-real. It forces that output into C₁, whose old part is contained in D. Using the reconstructed-W forcing relation, Replacement in N therefore gives an injection

```math
\mathbb R^N\setminus D\longrightarrow D
 \tag{5}
```

This contradicts Choice in N, since D is countable and ℝ^N is uncountable. Consequently no condition forces such an f. Assign color 1 outside D instead to prove the reverse non-injection. Each cell fails to be equinumerous with ℝ: for example, a bijection ℝ→C₀ would restrict to an injection C₁→C₀. This completes (4).

Here is the exact conditional application to the proposed infinite symmetric target. Suppose T and F are intermediate ZF models in a common extension of W, with F obtained by retaining an additional independent generic coloring and with the following verified properties:

1. Their real line is ℝ^W; the coloring is generic enough to meet the old countable-set avoidance dense sets above.
2. Every graph in F of a function C₀→C₁ or C₁→C₀ is realized in some local generic extension W[Gₕ,H], where Gₕ is generic for a system from §4, H is the same extra color generic, and the pair is generic for Pₕ×Col.
3. None of that local system's repair target names uses the extra coloring.

Then F satisfies ¬WCH. A purported injection in F would be an injection in its corresponding local model: its graph, its two cells, and the real line are the same, and the function and injectivity assertions quantify only over these sets. This contradicts (4). The criterion requires completeness of the local generic reduction, not just a syntactic support assignment.
