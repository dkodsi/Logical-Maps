# Independent audit of centralizer localization

## 1. Exact recursive conventions

At a repair stage β the raw target indices are the already supported rows a:R→Bβ. Copy permutations act within a fixed raw-row fiber; the row itself is transported only by the preceding Boolean action. Thus a listed exception is a permutation of copy indices at specified raw rows, with only countably many moved coordinate pairs in total. Arbitrary exchanges between different target rows would not in general preserve the forcing and are not part of the construction.

The operator systems must be coherent under prefix restriction and canonical tail extension. In particular, a support witness for a row at β uses the filter and designated operators of that prefix. When that witness is imported into a later support calculation, use the canonical extensions of those prefix operators: their later action transports raw rows and fixes copy indices, introducing no new exceptional stages at or above β. This convention makes the backward dependency induction genuinely descend to earlier forcing stages. Importing an arbitrary global extension of the same prefix operator would not justify that descent.

This coherence has a recursive implementation. Given the forcing, group, designated operators and filter at β, first form the supported raw-row set. The next forcing stage and its group then use precisely those rows. Extend old designated operators canonically, add the permitted small copy actions, and close under the next group’s conjugations and finite compositions. Finally form the next centralizer filter. Supportedness of an image row follows from intersecting its old support with the relevant centralizer. Supportedness of a partial preimage follows from injectivity. Consequently no later raw-row admission is used to define an earlier filter.

At a countable limit prefix, countably many listed stages may be cofinal in that prefix. At the final κ=ω₁ stage a countable stage set is bounded below κ. Requiring a strict bound below every countable prefix would break restriction coherence; the saved construction correctly avoids this requirement.

This audit uses the complete Boolean extensions of the designated compressions proved in [the separate compression note](necessary-os-ch-stage-preserving-compressions.md). An action on raw coordinate labels alone would not supply those extensions.

## 2. The countable dependency closure

Fix a supported name x⊆check U, with a support H(S,D₀). Close the countable support data under designated row maps and their partial inverses. At each repair stage, each resulting row orbit O is countable, because its members are reached by finite words in countably many partial functions. Protect O×F_O, where F_O includes every protected or exceptional copy index encountered in that orbit, including both endpoints of an exception.

For every retained row, import a whole local forcing system for that row from the earlier-stage induction hypothesis. Import its prefix support operators by the canonical extension convention of §1. Do this also for every later exceptional row of each operator already under consideration. Repeat countably often. Every operation has countable output from countable input; DC supplies the countable choices of witnesses. The closure remains countable and contains every finite dependency chain.

The induction hypothesis needed here is whole-row localization: there is one earlier local complete subalgebra containing all Boolean values a(r), r∈R. Separate local witnesses for individual r would not suffice. Once the whole row belongs to the local subalgebra, its local preimage is unique; Replacement, rather than a choice of representatives, assembles the local row.

Call the resulting coordinate system Q. Its selection is made from x and its support before choosing any pair of forcing conditions. Every retained target is measurable over the earlier retained coordinates. The normalization which replaces a countable target by R is measurable there as well: countability is expressed using the same old-real enumeration codes, and the complete embedding preserves the corresponding joins and meets.

## 3. Strong projection and genericity

The projection π:P→Q drops unretained graph coordinates. Prove its validity stage by stage. At a retained coordinate, a full prefix which forces a range assertion in an earlier Q-measurable target has a Q-projection forcing that assertion. This follows from the previously established projection property: a contrary extension of the projected prefix would lift to a contrary extension of the full prefix.

For the lift itself, let q≤π(p). Use q on retained coordinates and retain p’s graphs elsewhere. At each stage the combined prefix strengthens p’s prefix, so all of p’s off-system range assertions remain true. The retained assertions follow from q and the earlier projection property. Coordinatewise unions handle countable limits. Therefore

```math
q\leq\pi(p)\quad\Longrightarrow\quad
\exists r\leq p\;[\pi(r)\leq q]
```

An unretained target may depend on retained coordinates. This causes no problem: strengthening a prefix preserves each already forced range assertion. No independence assumption between selected and unselected targets is needed for this lift.

It follows that projection of an actual P-generic is genuinely Q-generic over W. Ordering the retained stages by their original positions gives a countable-height dependent diagram with targets using only earlier coordinates. This is the precise input required by [the Mahlo local preservation theorem](necessary-os-ch-countable-repair.md), §1.

## 4. Commuting relative homogeneity

Let p and q have compatible Q-projections and strengthen them over a common Q-condition. At the base, protect every block moved by a retained designated operator. A small permutation of the other blocks moves p’s active blocks away from q’s.

At a repair stage, the preceding action fixes every protected raw row and every exceptional row whose earlier local system was imported. On each active row orbit O choose one small copy permutation σ_O fixing F_O. It moves p’s unprotected active copies away from q’s active copies in the image orbit. Apply that same permutation to all rows of O. The orbit and the copy support are countable, so this changes only countably many literal coordinate pairs. Only countably many orbits and stages are active.

Here is the exact commutation check. Write

```math
d(a,\xi)=(da,\pi_{d,a}\xi),\qquad
g(a,\xi)=(ga,\sigma_a\xi)
```

Assuming the prefix actions commute, the remaining equation is

```math
\sigma_{da}\pi_{d,a}=\pi_{d,ga}\sigma_a
```

Away from listed exceptions, both π terms are identities and σ is constant on the d-orbit. At an exceptional row, the prefix fixes the row and σ fixes every exceptional input and output index. The equality follows again. Backward support closure is precisely what permits this calculation at later exceptional stages; no surjectivity statement about restricting centralizers is used.

Protected orbits are fixed pointwise on raw rows. Since the preceding action is bijective, an unprotected orbit cannot be carried into a protected orbit. Thus the chosen copy moves do not disturb the common Q-part. The transformed conditions have disjoint unprotected coordinate supports, and their union is a valid extension by the same range-assertion argument as in §3.

The resulting g is a small designated automorphism lying in the original support of x. Hence conditions with compatible Q-projections cannot force opposite membership verdicts about x. The projected membership name is forcing-equivalent to x. This proves whole-name localization and closes the earlier-stage induction used in §2.

## 5. What this audit establishes

Under the explicitly recursive system above, every symmetric subset of a fixed ground set has one actual countable generic dependency diagram. For subsets of R and graphs in θ×R, the Mahlo theorem therefore gives the advertised local preservation consequence, including exclusion of an injection κ→R. Every such local diagram is bounded below the final κ, even when its own height is a countable limit.

The independent unused-color comparison still requires its own product localization with repair targets independent of that color. The supported typed hierarchy, native real-label representation, whole-operation preservation, and comparison observers also remain separate obligations. None of them follows merely from this projection audit.

## 6. The target and unused-color comparison

Assume the recursively specified symmetric model T of the construction above exists, with the asserted ZF and localization properties. Let F be the hereditary symmetric model for Pκ×Col, using the same group and filter on Pκ and the trivial action on the extra countable-partial coloring factor Col. Repair targets in Pκ are its original prefix-supported rows; they do not depend on this extra factor. This section proves T satisfies weak CH and F does not, rather than identifying either symmetric model with its full forcing extension.

First, countability of a subset A of the old real line is absolute between these symmetric models and the corresponding full forcing extensions. The full forcings are countably closed over W and add no reals. A countable enumeration of A can be coded by a real, so any such enumeration belongs to W and hence to the symmetric model. The converse is immediate. This also makes the target normalization in the construction agree with countability in the symmetric models. It is not enough merely to know that the symmetric model itself adds no reals; the full-forcing fact is used here.

For A⊆R in T, localization puts A in a fixed countable coordinate diagram below some α<κ. The equivalent prefix name is symmetric there: protecting the retained coordinates fixes its membership name, whose arguments are ground reals. Its Boolean membership row is consequently an admitted raw target at that prefix. At a later repair coordinate, the generic graph is a bijection R→A when A is uncountable. The graph is hereditary symmetric, supported by that coordinate and the support of its target row. The usual domain and range dense sets give totality and surjectivity; they concern only old reals, which remain all the reals. Thus every uncountable real subset in T is equinumerous with R, proving weak CH.

For F, take any HS name x⊆check U, for example the graph of a purported injection between its extra color cells. This name may depend on the extra coloring and need not be a T-name. Its symmetry support nevertheless has the same form H(S,D₀) on the Pκ coordinates. Construct the countable diagram Q from that support exactly as in §2, and retain the entire extra factor. There is a strong projection

```math
P_\kappa\times\mathrm{Col}\longrightarrow Q\times\mathrm{Col},
\qquad (p,r)\longmapsto(\pi_Q(p),r)
```

If two product conditions have compatible projections, strengthen to a common Q-condition and a common extra-color condition. The relative automorphism from §4 acts on their Pκ parts and fixes the extra condition. Hence it makes the full product conditions compatible. The projected-membership argument therefore localizes the whole F-name to an actual Q×Col generic extension. Q’s targets remain the original Pκ-prefix targets and are independent of the extra color.

Apply the countable-height independent-unused-color theorem from [the Mahlo note](necessary-os-ch-countable-repair.md), §4, using the finite argument in [the repair note](necessary-os-ch-symmetric-repair.md), §6. It excludes both C₀↪C₁ and C₁↪C₀ in this actual local product extension. This exclusion transfers to F without changing the forcing interpretation: an injection property of a specified graph between the specified cells is bounded and absolute between the transitive local extension and the full extension. If F contained such a graph, its local evaluation would already have that property, contradicting the local theorem.

Both cells are uncountable. For every old countable S⊆R and each i<2, the conditions assigning color i to some real outside S are dense. If Cᵢ had a countable enumeration in the full extension, that enumeration would have an old real code, contrary to this density. In particular, neither cell is countable in F. If C₀ were equinumerous with R, composing C₁⊆R with a bijection R→C₀ would give the excluded injection C₁→C₀. Thus C₀ witnesses failure of weak CH in F.

Finally suppose the typed interpretation at e has fixed carrier R^W and exactly the HS Boolean rows as its admitted unary, binary and ternary relations. Their current extensions are exactly the subsets and relations of the respective symmetric ZF model: a symmetric relation name yields its supported Boolean membership row, and conversely a supported row yields a hereditary symmetric relation name. Both models have the same real line as W. Its ground field operations and natural-number subset are admitted, and ZF proves that this real field is complete for every **nonempty** bounded subset. Consequently native real-structure existence is nonvacuous in both components. Internal categoricity of complete ordered fields, proved by rational Dedekind cuts without Choice, makes native CH on every admitted real structure at e equivalent to weak CH of that model. Hence T has U_{e,CH}, and F has ¬U_{e,CH}, under this exact typed interpretation.

This last paragraph audits the e-type verdict and its nonvacuity. It does not establish closure of the entire typed hierarchy under comparison observers or verify their whole-operation identities; those remain part of the assembled modal-model audit.
