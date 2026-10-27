# Countable repair diagrams by Mahlo reflection

The countable-height difficulty can be avoided by choosing one small universe which already contains witnesses for every relevant dense extension requirement. Such a universe is obtained from a club of witness bounds and an inaccessible point supplied by Mahloness. The proof does not replace κ by λ in an arbitrary definition, and it does not identify the reals of a limit extension with the union of its earlier real sets.

## 1. Exact local statement

Let V satisfy ZFC with a Mahlo cardinal κ, and let W be the symmetric Solovay model derived from κ. Fix a countable ordinal δ in W, a countably enumerated set of coordinates at every level below δ, and a W-sequence of target names. A repair coordinate at level α has target Ȧ which uses only levels below α and is forced to be an uncountable subset of the fixed real line ℝ^W. The forcing at that coordinate is J(Ȧ), the countable partial bijections ℝ^W→Ȧ. Free countable-partial binary-coloring and J(ℝ^W) coordinates are also allowed. Form the countable-support iteration P of these countably enumerated levels.

All these data are one fixed W-set. The statement concerns this selected local iteration, not the product of all possible targets. As before, interpretation in small universes means interpretation by the remaining Levy-collapse forcing relation for the reconstructed W.

**Countable local preservation theorem.** P has a dense presentation by countable sequences of actual real-coded graphs, is σ-closed in that presentation, and forces

```math
\mathrm{ZF+DC},\qquad
 \mathbb R=\check{\mathbb R}^{,W},\qquad
 \omega_1=\check\kappa,
 \qquad \check\kappa\not\hookrightarrow\mathbb R.
 \tag{1}
```

The same conclusion holds below a condition forcing the stated target hypotheses. In particular, the theorem preserves non-well-orderability of the real line. It makes no assertion that the weaker assumption of an inaccessible cardinal suffices for this countable-height proof.

The concrete presentation and closure can be checked independently of the Mahlo argument. At successor levels, previous forcing adds no reals, so densely it decides a real coding the countable collection of graph conditions. At a countable limit, choose a sequence of earlier levels cofinal in that limit. Successively normalize those prefixes, preserving the earlier graph conditions by extension. Take coordinatewise unions of the resulting descending sequence. Every coordinate is eventually covered, each union is countable, and its earlier prefix forces all of its range-membership assertions. This is a concrete lower bound and an extension of the original condition. The same coordinatewise union argument gives σ-closure for descending sequences. DC permits these countable constructions and is preserved by σ-closed forcing; hence no reals or countable ordinal sequences are added. These observations prove the first three forcing assertions in (1). The last assertion needs the full diagram constructed below.

## 2. A ground club of witness bounds

Capture the local system, an initial condition, and any auxiliary name being tested in a small ZFC universe M=V[K], where K comes from forcing of size less than κ. In particular, capture a real code showing that δ and the total coordinate set are countable. The fixed high-rank ground parameters used to define the local system are retained. The Solovay parameter-reduction and reconstruction facts are Larson–Zapletal, *Geometric set theory*, [author's draft](https://people.clas.ufl.edu/zapletal/files/balanced14.pdf), Facts 1.7.12–1.7.14, printed pp. 32–33. Small forcing preserves the Mahloness of κ: it preserves the stationary set of ground inaccessibles sufficiently above its size, and preserves their inaccessibility.

Work in M, and write L_α=Coll(ω,<α), for α≤κ. The actual W can be reconstructed over M. Its fixed local-system definitions and captured parameters are interpreted in the symmetric model associated with L_κ. Homogeneity permits us to use the largest condition for the local-system hypotheses which hold in the actual W.

There are countably many kinds of extension requirements. The input consists of a real code for a valid concrete P-condition p, a coordinate j, and, where relevant, an old real x. The needed requirements are:

- extend p so that x is in the domain at j;
- extend its earlier prefix to decide whether x belongs to A_j;
- if that decision is positive, extend p so that x is in the range at j.

For a free coloring coordinate, require its value at x to be assigned. An earlier-prefix decision can be amalgamated with the rest of p by strengthening the prefix; previously required range assertions remain forced. The repair targets' uncountability makes domain extension dense. Range extension is dense after a positive membership decision. All witnesses are again real-coded concrete conditions. The canonical graph unions used for closure need no additional witness selection.

For each α<κ, the collection of nice L_α-names for real input codes has cardinality less than κ in M: |L_α|<κ and κ is strong limit. For each such input name and each requirement kind, the ZFC maximum principle for the **outer** forcing L_κ chooses a name for a real-coded witness whenever the requirement's antecedent is satisfied. On invalid inputs choose an arbitrary default real. This use of Choice is in M, not in W and not in a symmetric extension.

Every L_κ-name for a real is equivalent to one supported below some β<κ. Indeed, L_κ is κ-cc, so the union of the antichains deciding its countably many bits has size less than κ; the union of the finite coordinate supports is bounded below κ. There are fewer than κ many selected witness names for a fixed α. Their bounds therefore have a common bound f(α)<κ. Choose f in M, increasing it if needed so f(α)>α. The club

```math
C=\{\lambda<\kappa:
       \lambda\text{ is a limit ordinal and }
       f``\lambda\subseteq\lambda\}
 \tag{2}
```

meets the stationary set of M-inaccessibles. Choose an inaccessible λ in this intersection, above the bounds needed for the captured real parameters and δ. The arbitrarily high rank of a fixed ground parameter does not affect the counting: only the nice real input names vary in this argument. No rank-initial-segment elementarity claim is being made.

Let N=M[H_λ], for the corresponding initial segment of the actual Levy generic. Then N satisfies ZFC and

```math
\lambda=\omega_1^N=|\mathbb R^N|,
 \qquad \lambda<\kappa.
 \tag{3}
```

Every real in N has a name supported below some α<λ, since λ is inaccessible in M and L_λ is λ-cc. Thus any tuple of old real input codes for a requirement comes from some L_α, α<λ. Its selected witness name is bounded below f(α)<λ and consequently has its value in N.

It follows that the old part of each required dense set is dense among old valid conditions. Here *valid* is defined in N by the remaining-collapse forcing relation for the reconstructed W. The actual validity of an N-code is equivalent to the corresponding forcing assertion: the remaining collapse is homogeneous with that code and the captured parameters fixed. The same applies to the extension requirements. Therefore the witnessed density is available inside N, not merely as an external assertion about one generic extension.

## 3. Constructing a full diagram in that one universe

In N let P_N be the set of old real codes which are valid P-conditions under the preceding interpretation. It has size at most λ. It is σ-closed in N. For a countable descending sequence in N, its coordinatewise graph union is coded by an N-real. The sequence belongs to W, where the closure argument in §1 verifies that union's validity; the remaining-collapse interpretation gives the same verdict in N.

There are λ many requirements from §2: the total coordinate set is countable in N and the old real line has size λ. Use Choice in N to enumerate them in order type λ. Construct a descending sequence ⟨p_ξ:ξ<λ⟩, beginning below the captured initial condition and meeting the next requirement at each successor step. At each limit η<λ, the ordinal η is countable in N by (3), so σ-closure supplies a lower bound. All selections can be made using a fixed N-well-order of P_N.

Let b be the coordinatewise union of this λ-sequence. It belongs to N, although it is generally not a countable condition there. In W, λ and the N-reals are countable, so b is a countable concrete P-condition extending every p_ξ. Each graph edge is valid because it appeared in some p_ξ and b's earlier prefix extends that condition's earlier prefix. For every coordinate j and every x∈ℝ^N, the construction has met the domain, earlier-prefix decision, and range requirements. Thus b_j is a bijection

```math
\mathbb R^N\longrightarrow
 A_j[b_{<j}]
   :=\{x\in\mathbb R^N:
           b_{<j}\Vdash_W x\in A_j\}.
 \tag{4}
```

Free colorings are total on ℝ^N. No separate requirement that the old part of A_j be uncountable was needed: (4) itself establishes that it has continuum size in N.

This is a full diagram at every one of the countably many levels, over the **single** universe N. There is no chain of small universes whose real sets are later identified with a union. Additional reals from later small extensions have not been omitted from N: every real of N was explicitly included in its λ-long requirement list.

## 4. Balance and preservation

The full diagram is balanced by induction along the countable well-ordered levels. Consider mutually generic small extensions N[H₀], N[H₁] and conditions q₀,q₁ extending b in them. At a coordinate j, a new edge cannot use an old domain element, since b_j already assigns every old input. It cannot use an old range element either: b_{<j} decides whether that element belongs to A_j, and b_j already exhausts its old members. Any common new domain or range between the two graph pieces would be a real in the intersection of the two mutually generic extensions, hence an old real. This is impossible. The earlier union forces every range-membership assertion required for the united graph. Free-color disagreements are excluded in the same way. At a limit level the concrete condition definition is determined by its prefixes, so coordinatewise union remains a condition. This proves compatibility of q₀ and q₁.

The old-value argument from [the finite note](necessary-os-ch-symmetric-repair.md), §2, now applies without any finite-height restriction. A captured name forced to be a real-valued function at an old argument must have one specific N-real value below b: otherwise mutually generic copies produce compatible conditions forcing different values. The forced old value is definable in N by the reconstructed-W forcing relation.

If an initial condition forced an injection κ→ℝ, capture that name before choosing λ. The resulting full b yields in N, by Replacement, an injection κ→ℝ^N. But κ remains inaccessible in N and |ℝ^N|=λ<κ. This contradiction proves the last assertion in (1).

The independent-unused-color theorem also extends to these countable local systems. Build the full repair diagram over N first, then color every N-real outside the initial countable extra-color domain 0. Old-value reflection excludes an injection from the 0-cell into the 1-cell; reverse the extra color for the opposite direction. Both cells remain uncountable because the combined forcing adds no reals. This is exactly [the finite note's §6](necessary-os-ch-symmetric-repair.md#6-an-independent-unused-coloring-forces-failure-of-weak-ch), with the present full diagram replacing its finite-height construction.

What has been proved is a local countable-height theorem under a Mahlo cardinal. Applying it to an ω₁-stage symmetric repair construction still requires an actual countable dependency reduction, the appropriate preservation of ZF and support bounds, and complete maps yielding admitted logical observers. These are not consequences of the local theorem alone.
