# A concrete choice fragment without a transversal

22 October 2026. Construction and typed verification by OpenAI Codex, direct source `misc`, this note. This is an ordinary paired-atoms permutation construction, not a claim of a new construction in the literature. The particular choice-fragment verification below is self-audited only.

## Exact result

There is a Henkin model of the original C in which:

* Relational Choice holds from every finite tuple of individuals to **every admitted output type**, including individuals.
* Relational Choice holds from any input type to any output type built from t alone.
* Transversal Choice at e fails, witnessed by an equivalence relation with two-member cells.
* Relational Choice at (et,e) fails explicitly.

Thus this is **not a model of all-type RC** and does not settle RC⇒TC. It is an actual model of C and a substantial specified fragment, rather than a hypothetical finite-fragment factor. It identifies the next missing choice instance exactly. It does not alter or instantiate the earlier unconstructed ultraproduct proposal.

## 1. The full finitely supported Henkin tower

Work in ZFC. Let I be infinite and let E=I×{0,1}. Let G be the group of all permutations of E preserving the partition into the pairs P_i={i}×{0,1}: pairs may be permuted arbitrarily and flipped independently. For finite A⊆E let G_A fix A pointwise. Fixing one point fixes its whole pair pointwise.

Set D_e=E and D_t={0,1}, with the trivial action on D_t. Recursively, D_(στ) is the set of functions D_σ→D_τ having finite support under the conjugation action, for each admitted type στ (τ≠e). Every value already lies in D_τ. This is the usual exponential of finitely supported G-sets. Equivalently, at every flattened relational type use all finitely supported Boolean predicates on the corresponding tuple domain.

Interpret application and lambda abstraction ordinarily. An abstraction with finitely many parameters is supported by the union of their finite supports. Quantifiers range over the whole appropriate domain, which is invariant under G; their interpretation is therefore invariant under any permutation fixing the parameters. Equality is literal equality. Boolean connectives, quantifiers and identity predicates are admitted at their required types.

Consequently the structure validates classical H, beta and eta, and actual extensionality. In particular it validates C's Logical Equivalence. Every admitted function type still ends in t. No e-output function type is added: external functions with individual outputs below are used only to define admitted graphs.

## 2. Choice from finite individual tuples

Fix n≥1 and an admitted serial relation U⊆E^n×E, supported by a finite A. Choose n+1 points B from distinct pairs disjoint from every pair meeting A. Let K=G_(A∪B).

For an input tuple x̄, the fiber U_x̄ is nonempty and invariant under G_(A∪{x_1,...,x_n}). The orbits of this latter subgroup on E are:

* singleton points in pairs meeting A or the input tuple; and
* one orbit consisting of all points in every remaining pair.

If U_x̄ meets the first part, it contains a point fixed by the subgroup, hence by K_x̄. Otherwise it contains the entire second orbit. At most n of the n+1 pairs anchored by B meet the input tuple, so one of B's points lies in that orbit. It belongs to U_x̄ and is fixed by K_x̄.

Thus every input tuple has an allowed output fixed by its stabilizer in K. Externally choose one input representative and one such output for each K-orbit of input tuples. Transport those choices equivariantly. Stabilizer-fixity makes this well defined, and the resulting total functional graph is K-invariant. It has finite support A∪B, hence belongs to the required relational domain.

This proves every finite polyadic RC_(e^n,e) instance, with the polyadic notation meaning a tuple of individual arguments. The empty tuple case is simply existence of a point in a nonempty admitted property. This does not assert RC for an unrestricted property-type input; coding tuples by their haecceities only gives choice on that particular represented subdomain of codes.

### Strengthening: arbitrary output types

The same model in fact supports choice from finite individual tuples to **any** D_τ. Here is a proof which does not assume a uniform bound on the supports of all possible outputs.

Fix a finite A supporting U⊆E^n×D_τ. There are finitely many G_A-orbits of input tuples: an orbit is specified by the coordinates in the finitely many anchored pairs and by the equality, pairing, and relative two-point pattern of the remaining coordinates. For an orbit O let r be the number of distinct input pairs not meeting A. We prove by induction on r that a serial U restricted to O has a finitely supported selector.

If r=0, O is a singleton tuple. Choose one output and add its finite support; this supports the single-row graph.

For r>0 choose a tuple x̄₀∈O, an allowed output y₀, and a finite support L of y₀. Let J be the union of x̄₀'s r unanchored pairs, and put B=A∪(L\J). The subgroup G_(B∪{x̄₀'s coordinates}) fixes y₀: each pair meeting the tuple is fixed pointwise, so its support L is fixed. Let O_gen consist of tuples in O whose r previously unanchored pairs avoid B. This is precisely the G_B-orbit of x̄₀. The rule

    g·x̄₀ ↦ g·y₀,               g∈G_B,

is well defined by that stabilizer-fixity and gives a B-supported selector on O_gen.

The exceptional tuples O\O_gen split into finitely many G_B-orbits, each having fewer than r unanchored pairs relative to B: at least one formerly free input pair now meets B. Apply the induction hypothesis on each such orbit, with B as the base support. Their finitely many finite supports, together with B, form a finite support for the combined selector on O. Finally combine the selectors on the finitely many original G_A-orbits.

Every output entity has some finite support by construction of the Henkin tower, including outputs at higher relational types, so this induction applies at every admitted τ. The empty input tuple is handled by choosing one witness and its support. All selectors remain **graphs**; no individual-output type is introduced.

## 3. Arbitrary inputs with purely propositional outputs

Every type τ built from t alone has a finite domain and trivial G-action, by induction on its formation. Fix an external ordering of D_τ. For any admitted serial U from an arbitrary D_σ to D_τ, choose the least allowed output at each input. If A supports U, then G_A fixes every output entity and preserves the fibers, so this selector graph is also G_A-invariant. It is admitted.

This proves the claimed additional RC instances. In particular RC_(t,t) and RC_(tt,t) hold. Since this model is extensional, BC and Actuality hold as well; that is consistent with the proposed local Actuality theorem and does not supply the missing individual-output choice.

## 4. Failure of a transversal and of the next choice instance

Let R be the equivalence relation whose cells are the pairs P_i. It is G-invariant and hence admitted with empty support. If an admitted transversal T existed, let A support it and choose a pair disjoint from A. Flipping that pair fixes A and therefore T, so T either contains both points of the pair or neither. It cannot contain exactly one. Thus TC_e fails.

Consider the ordinary membership-selection relation

    V(F,y) := Fy ∨ ¬∃z Fz,                 F:et, y:e.

It is admitted and serial. Suppose S were an admitted total functional subrelation, with finite support A. Choose a pair P_i disjoint from A and regard its characteristic property as an entity F_i∈D_et. Flipping P_i fixes F_i as an entity and fixes S, but swaps the only permitted outputs in V(F_i,−). Functionality is impossible. Hence RC_(et,e) fails.

## 5. Relevance and limitation

The individual-tuple fragment can choose using the points already supplied in an input, with a finite reservoir covering fibers outside those points' pairs. A property code for an entire pair has more symmetry than either of its individual presentations, which is why the next input type breaks that argument.

This makes the distinction between choice with individual inputs and a uniform higher-type membership chooser concrete inside a complete Henkin tower of C. Even allowing every finite individual input arity and every output type does not close the main problem. An intensional continuation intended to satisfy RC_(et,e) would have to change this fixed-code obstruction while also abandoning Actuality; adding that choice instance to the present extensional setting would already produce TC_e. No such continuation is claimed here.
