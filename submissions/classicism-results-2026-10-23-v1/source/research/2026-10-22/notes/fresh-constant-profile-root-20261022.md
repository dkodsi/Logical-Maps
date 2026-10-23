# Fresh-constant profile roots: finite atom counts and exact countability spectrum

Original mathematical construction, 22 October 2026, by the world-cardinality research lane. No database edits, Lean work, literature-novelty claim or human-checking claim. This is a variation of the pure-term-profile root construction in `/tmp/classicism-research/profile-root-construction-20261022.md`, whose all-type semantic embedding is audited in `/tmp/classicism-research/audit-profile-20261022.md`. The new ingredient is a countable stock of auxiliary propositional symbols, interpreted only as top or bottom in copies of the component models. The proof below spells out its effect and checks that it introduces no signature-Maximalism assumption.

Work in ordinary ZFC metatheory. The object theory is the fixed relational-type C. The auxiliary symbols are semantic bookkeeping resources and are forgotten in the final pure-language reduct. **Only ordinary Pure Maximalism for the original C language is asserted. No Strong Possibility or signature Maximalism is asserted.**

## 1. Component category and auxiliary symbols

Choose a set of pure C action models that witnesses every C-consistent closed pure sentence. Include all objects and arrows of each chosen component, and explicitly include the full finite Henkin models with arbitrarily many individuals and the full finite S5 models with one individual and arbitrarily many worlds. These additions are harmless. The use of a complete component family is the same metatheoretic assumption used in the existing coalesced/profile-root construction.

Let c_0,c_1,... be countably many auxiliary symbols of type t. For every component M and every bit sequence α∈2^ω, make a disjoint copy M_α. Interpret c_i as ⊤ at every object of M_α when α(i)=1, and as ⊥ at every object when α(i)=0. These interpretations commute with every component arrow because transport preserves the logical constants ⊤ and ⊥. No arbitrary global interpretation of a proposition under category loops is needed.

Add a new object o with one individual *. For every object V of every M_α and every a∈D_e(V), add an arrow h_(V,a,α):o→V sending * to a. Put

    k h_(V,a,α) = h_(V',ka,α)

for a component arrow k:V→V'. There are no nonidentity arrows back to o. Functoriality in the component makes this composition associative. The assignment α remains unchanged along component arrows.

## 2. Profiles and root domains

For each relational type τ, let B_τ consist of the families

    b_T(V,a,α) := [[T(z)]]_(V,α)[a/z],

where T is a well-typed term in the auxiliary expanded language with no free variable except the individual variable z. Quotient terms by equality of their entire families of component entities. Equality only of their current truth values is not the quotient. Each B_τ is nonempty and countable, because there are countably many finite terms. In fact it is countably infinite: the constant relations with value c_i have pairwise different profiles, as assignments α distinguish them. For individuals the only needed profile is z.

If τ=σ_1...σ_k t, recursively define

    D_τ(o) := P(D_σ1(o)×...×D_σk(o)) × B_τ.

For k=0 this is 2×B_t. The recursion is on syntactic type complexity, so the domains of the argument types are already defined. A pair (S,b_T) has actual extension S at 1_o and, at h_(V,a,α), the actual extension of the component entity b_T(V,a,α). Its truncation along that arrow is stipulated to be exactly that component entity.

This really is an embedding as relational intensions. The identity coordinate recovers S. If b_T and b_U differ as entity families, they differ at some (V,a,α); distinct component relations are distinct intensions, so a further component arrow and argument tuple distinguish their actual extensions. The corresponding composite root arrow, which is present by construction, distinguishes the root intensions. Thus different pairs have different intensions.

Transport lands in the component domain and is compatible with composition: component term interpretation commutes with transport, and every c_i interpretation is transport-compatible. The truncation of (S,b_T) along h_(V,a,α), followed by k, is therefore b_T(V',ka,α), just as the composite arrow requires.

## 3. Application, abstraction, quantifiers, H and Logical Equivalence

For f=(S,b_T) of type ρτ and a root argument u, take the appropriate fiber of S as the actual extension of f(u). If ρ=e, the profile of u is z; otherwise u has a profile U(z). The output profile is T(U(z)). Equal representative profiles give equal component entities under application, so this definition does not depend on the chosen terms. It also satisfies

    h(f(u)) = (hf)(hu)

at every root arrow. Application to component arguments that do not come from o remains the component's original application.

An assigned root parameter at a relational type has a term profile T(z); the sole individual parameter has profile z. Given a term R with finitely many assigned root parameters, substitute their profiles capture-avoidably into its free parameters. This produces a single auxiliary term R*(z). By structural induction, at every outgoing arrow the value of R with the transported assignment is the component value of R*(a). The auxiliary symbols cause no new case beyond their stipulated transport-compatible interpretations.

For λ-abstraction, its root actual extension is the set of tuples satisfying the abstraction body under the root assignment, and this is admitted without any restriction on the subset. Its outgoing profile is the auxiliary abstraction after substitution of only the free parameters. Bound variables remain bound. Thus at a component it denotes the whole component abstraction, including its behavior on arguments absent from the root transport image.

For a quantifier ∀_ρ, its actual extension at o is the family of root predicates true of every member of D_ρ(o), and its profile is the pure logical quantifier ∀_ρ. At an outgoing arrow its value is the component quantifier over the entire component domain D_ρ(V). This verifies the quantifier step above. It does **not** replace target-domain quantification by quantification over root images, and it does not require root transports to be surjective.

Equality at o is literal equality of domain entities, with the ordinary equality term as its profile. Unequal root entities may become equal after transport; that is allowed in C. Boolean constants have their ordinary truth-functional actual extensions and their logical term profiles.

The ordinary truth-functional and quantifier clauses, literal equality and substitution validate H at o. β holds as an identity because root extension substitution and component profile substitution agree. η holds because the actual fibers reconstruct the original actual extension and component η identifies the profiles. Components already validate H. The inference rules preserve validity under all assignments.

For Logical Equivalence, take an H-theorem P↔Q with its original theoremhood restriction. At o the two relevant abstractions have the same actual extension by H-soundness. At each component, C identifies those abstractions as entities under the transported parameter assignment. Their profile families are therefore identical, so the root pairs are identical. This checks the required intensional equality, not merely equality of actual truth values. No equivalence proved from an optional hypothesis has been promoted to an equality.

Thus the construction is a C model. It can be regarded as an auxiliary-language expansion by interpreting c_i at o as, for example, (0,b_ci); forgetting those constants gives the promised original-language C model. Their use in defining domain elements does not change the reference theory of Maximalism.

## 4. Pure Maximalism and exactly one atom

For every C-consistent closed pure sentence P, some chosen component object V satisfies P. Pick a∈D_e(V) and any α. Its pure interpretation is unaffected by the auxiliary assignments, so the arrow h_(V,a,α) makes the root proposition P true. Hence P is nonbottom at o. This proves the pure Possibility form of Maximalism, and therefore the recorded equivalent Pure Maximalism schema.

Let r=(1,b_⊥) be the root-only proposition. It is a nonzero atom: every subproposition has bottom profile and actual bit either 0 or 1. If p=(1,b_T) differs from r, then r is a proper nonzero subproposition of p, so p is not an atom.

Suppose p=(0,b_T) is nonzero. The profile b_T is nonbottom somewhere. By the relational-intension interpretation of component propositions and closure under descendants, T is true at some pointed component object (V,a,α). Choose j such that c_j does not occur in the finite term T. Changing only α(j) preserves T's value, because the underlying pure component and every auxiliary symbol occurring in T are unchanged. In the copy with α(j)=1, p∧c_j is true; in the copy with α(j)=0, p∧¬c_j is true. Both are admitted propositions (their profiles are auxiliary terms), both are nonzero, and they split p. Therefore p is not an atom.

Consequently r is the only propositional atom at o. Every nonzero proposition off the root is atomless. The atom r is a strong world: it settles all current propositions and transports to bottom along every nonidentity root arrow, where the settlement disjunction is trivial. Thus Strong Actuality and “every current atom is strong” hold, while Atomicity and Strong Leibniz fail.

## 5. Natural-number supports are actually standard

Fix any admitted counting type σ and let ν_σ=(σt)t. Write n_σ for the standard n-fold successor of zero as an entity at o. These denotations are pairwise distinct. At σ=e, finite individual components with sufficiently many individuals distinguish any two. At any relational σ, the constant-relation embedding t→σ is injective, so finite S5 components with sufficiently many worlds have arbitrarily many σ-entities; their full actual predicate extensions distinguish the finite cardinalities. Difference of the corresponding pure profile families entails difference of the root entities.

The set S_σ={n_σ:n∈ω} is an admitted actual extension of a root property W of type ν_σ t: choose precisely that subset as the actual coordinate and choose the bottom profile. At o, W contains zero and is closed under successor. The impredicative definition of N_σ therefore makes every current N_σ-member belong to S_σ. Conversely every standard numeral satisfies N_σ by ordinary finite induction, a C theorem. Hence

    N_σ(o) = {n_σ:n∈ω},

with no repetitions. This is true even for σ=e, although the current individual domain has just one member: distinct cardinality entities may have empty actual extensions while differing at components. No equation between coextensive cardinalities is inferred.

The property W need not remain successor-closed or contain zero after transport; only its current induction premises are used. The construction's unrestricted actual-extension coordinate is what admits this witness. External countability alone would not establish the internal countability assertions below.

## 6. Exact internally countable type spectrum

For each finite k≥0, the root domain of τ=e^k t is countable. The product of its k individual argument domains is a singleton, so its actual-extension coordinate has two values, and its profile coordinate B_τ is countably infinite. The same statement covers τ=t when k=0.

Fix a counting type σ. There is a concrete external injection of D_τ(o) into the standard naturals: encode the actual bit and the least syntax index of a term representing its profile. Composing this code with n↦n_σ gives an injection into N_σ(o). Its graph is an admitted actual extension of a relation R:τ ν_σ t; assign the bottom profile to this relation. At o, every τ-entity receives a numerical code, and two entities share a code exactly when identical. Thus the exact Background definition holds:

    Ctbl_{σ,e^k t}(⊤), for every admitted σ and every finite k≥0.

These are actual assertions. No boxed countability is claimed. The coding relation is explicitly an admitted entity, not an unrepresented metatheoretic function.

For contrast, let τ=σ_1...σ_k t have a relational argument σ_i. That argument domain contains an injection of D_t(o), via constant relations, and D_t(o) is countably infinite. Fixing the other coordinates gives an injection of ω into the argument product. Varying the actual extension on this copy of ω, while fixing the profile to bottom, embeds P(ω) into D_τ(o). Thus D_τ(o) is externally uncountable in the ZFC metatheory.

This also verifies failure of every Ctbl_{σ,τ}(⊤) internally in this model. By §5 its numerical support N_σ(o) is the standard countable set. Any admitted relation satisfying Ctbl would assign each τ-entity a nonempty set of numerical codes, with disjoint sets for different entities. Taking the least standard code would give an external injection into ω, contrary to the displayed P(ω) injection. This least-code argument uses no arbitrary choice. Independently, the Frege-infinity report §22 proves the corresponding uncountability for every Pure Max model at these types.

Therefore the model has exactly the following internal countability spectrum among relational types: all types with only individual arguments are countable at every Frege index, and every type with a relational argument is uncountable at every Frege index.

One may also calculate the external cardinalities exactly in ZFC. Assign r(e)=-1 and, for a relational type τ, set r(τ)=0 if all its arguments are e; otherwise set r(τ)=1+max r(σ_i) over its relational arguments. Then |D_τ(o)|=beth_{r(τ)}(aleph_0). The profile factor is countably infinite at every relational type, and the actual-extension factor takes a powerset of the finite argument product. This external beth calculation is separate from the internal countability proof and is not asserted for arbitrary Henkin models.

## 7. Adding full isolated roots: any positive finite atom count

Now add one standard full isolated coalesced root o' above this entire model, with one individual. For every relational τ its domain is

    D_τ(o') = P(product of its current argument domains) × D_τ(o),

with the second coordinate transported to o. The standard coalesced construction supplies closure and C-validity; alternatively the proof in §3 applies with the full old domain as the permitted tail coordinate. Pure Maximalism is inherited, since o already makes every C-consistent pure sentence possible and o' sees o.

At t the Boolean algebra is 2×D_t(o), so o' has exactly two atoms: its root-only atom and the lift of r. The original nonzero atomless remainder persists. Both atoms are strong worlds, by their behavior under transport along the two isolated root stages.

Let V=λx.r', where r' is the new root-only atom. Since the current individual domain is singleton, every current individual profile has one of two extensions, and exactly one of the two atoms represents it. Thus raw UWR_e holds, as does its version at every finite tuple of individuals. Its empty-profile agreement proposition is ¬r', which has the atomless remainder and is not an atom; the original AUCP_e fails, as the direct Pure Max obstruction independently requires.

The exact countability spectrum of §6 persists. For τ=e^k t, the new actual-extension factor has two elements and the old tail domain is countable. For a type with a relational argument, the new actual-extension factor again contains P(ω). The standard-number proof and admitted coding-graph proof are unchanged, using the new arbitrary actual extensions. The displayed external beth cardinalities are also preserved by structural induction.

Repeating this isolated-root operation finitely many times gives every prescribed positive finite current atom count, always with Pure Maximalism, current individual monism and the same internal countability spectrum. The two-atom stage gives raw UWR; the one-atom stage refutes raw WR; stages with at least three atoms satisfy raw WR but refute raw UWR under monism. None of these models is claimed to satisfy Strong Possibility: each has the isolated-root distinctness-preserving collapse, and the auxiliary fresh symbols split the canonical pure finite-theory propositions that the separate SP lemma makes atomic.

## 8. Audit boundaries

The proof does not assume an arbitrary submodel of term denotations preserves quantification. Actual extensions at the new root remain unrestricted, while only outgoing profiles are term-generated. Every target quantifier uses its component's whole domain. The all-pointed-object construction is essential when converting disagreement of component entities into root-intension disagreement. The auxiliary symbols have completely explicit coherent interpretations, and are forgotten before stating Pure Maximalism. Countability is established by admitted root relations and a proved description of N_σ, not inferred merely from external cardinalities.

This is a relative semantic construction in ordinary ZFC using the same action-model completeness/coalescence background as the audited profile-root model. It is not a Strong-Possibility consistency proof and makes no claim about signature Maximalism.

## 9. Explicit failure of Countable Boolean Completeness at t

This section strengthens the negative side of the exact countability spectrum: the one-atom model fails every counting-index instance of Countable Boolean Completeness at t. The same conclusion persists after finitely many isolated full roots.

Let r=(1,b_bottom) be the root-only atom, and choose the admitted auxiliary propositions c_i with actual bit zero. Define

    q_n := ¬r ∧ (∧_{i<n} c_i) ∧ ¬c_n       (n∈ω).

The initial conjunction is top when n=0. The factor ¬r ensures that even q_0 has actual root bit zero. Each q_n is nonbottom: any component copy with its first n auxiliary bits true and its nth bit false realizes it. Distinct q_n are algebraically disjoint, since their finite Boolean cylinders are disjoint at every component copy and all have actual root bit zero.

Take the property A of propositions whose actual extension is exactly {q_2n:n∈ω}, with bottom profile. It is admitted because root actual extensions are unrestricted. At every Frege index σ, A is internally countable: its coding relation assigns q_2n the actual numeral n_σ, with bottom profile. Section 5 proves that these numeral entities are distinct and exhaust the current N_σ.

Suppose B is any upper bound of this actual family. Its outgoing profile is represented by a finite auxiliary term T(z), and only finitely many c_j occur in T. Choose an odd k larger than all those indices, and then choose an even l>k. Fix any underlying pointed component object (V,a) and an assignment α whose first l bits are true and whose lth bit is false. At this copy q_l is true. Since B≥q_l, B is true there too. Change only α(k) from true to false. The underlying component, a, and every auxiliary interpretation occurring in T are unchanged, so B remains true; q_k is now true. Thus B∧q_k is nonbottom.

But every member q_2n of A is disjoint from q_k. Therefore B∧¬q_k is still an upper bound of A and is strictly below B. No upper bound is least. The actual bit of B causes no difficulty: q_k has root bit zero, so removing q_k changes only the tail profile, and the exhibited component copy proves strictness.

Consequently A has no LUB, or dually its pointwise-negated family has no GLB. This explicitly refutes Countable Boolean Completeness at t, at every numerical base σ. It does not infer failure merely from external countability.

After any finite sequence of isolated full roots, lift all q_n with actual bit zero at every new stage. A candidate upper bound has an arbitrary finite initial string of truth bits followed by one old term profile T. The same fresh-index argument lowers that tail while leaving all initial bits unchanged. The exact actual family and its numerical coding graph remain admitted at the new root, so the same CBC failure holds.

Externally, the original propositional Boolean algebra is the product of the two-element algebra with a countable atomless Boolean algebra: the first factor is the root truth bit, and the second is B_t. The fresh-symbol splitting argument proves that B_t is atomless. The explicit no-LUB proof above uses no classification theorem for countable Boolean algebras.

## 10. Protected finite cells and arbitrary finite individual domains

Two variants sharpen the finite-cardinality calibration.

### 10.1 Prescribing which finite Fregean cells are atoms

Let S be a finite set of positive external integers, A_n:=Fregean∧Exactly_n(e), and J:=¬(∨_{n∈S} A_n). In the component expansions replace the choices top/bottom for each fresh c_j by J/bottom. Both choices are pure term denotations and so remain coherent along every component arrow. Keep the same finite-term profile construction and unrestricted root actual extensions.

At an A_n-world for n∈S, every c_j is the bottom ENTITY: the world is Fregean and J is false there. Consequently each auxiliary term profile has the same actual truth value at every pointed A_n-world, by the finite extensional homogeneity argument in the audited original profile construction. Inclusion of all descendants converts this truth agreement into equality of profile entities. As A_n is actually false at the new root, every p∧A_n is literally bottom or A_n. Thus each protected A_n is an atom.

Conversely a nonzero profile part below J can be split with a fresh c_j. At a component realizing that part, J is true; interpreting c_j first as J and then as bottom preserves the older profile term but makes the fresh selector true and false. Thus the profile part below J is atomless. A possible atom crossing the finite partition by the A_n's and J must lie under one partition member. It follows that the only current atoms are the protected A_n's together with the root-only atom r. There are exactly |S|+1 of them. Pure Max, standard actual arithmetic, and the exact countability spectrum are unchanged. This argument uses the Fregean nature of the protected cells; merely disjoint arbitrary formulas are not silently substituted.

### 10.2 Pure Max and raw UWR with any positive finite number of individuals

Fix an external d≥1. In §1 replace the singleton root individual domain by a fixed d-element set D. Every arrow h_(V,a,α) sends ALL members of D to a. This is an allowed individual action; it deliberately need not preserve distinctness. A root individual parameter still has profile z, irrespective of which member of D it denotes. The substitution proof of §3 therefore works unchanged. Actual root extensions are unrestricted subsets of the relevant products of D and the relational domains, and actual equality remains literal equality. Different actual individuals may become identical after transport, as C permits.

The proposition algebra is unchanged: it has the root-only atom and an atomless remainder. Every type e^k t still has a finite actual-extension factor and a countably infinite profile factor, so the same countability spectrum and standard numerical supports hold.

Now attach 2^d−1 successive full isolated roots, each retaining the same individual set D, with the identity map to the preceding root. At each stage a relational entity has an arbitrary actual extension and an old tail entity. Each stage adds one propositional atom. The final root therefore has exactly 2^d atoms, one for each root stage, together with a nonzero atomless remainder.

Enumerate the 2^d subsets of D. Build V^{et} through the successive actual-extension coordinates so that, at the stage corresponding to a subset S⊆D, its actual extension is exactly S. At that stage's root-only atom w_S, and hence at its lift to the final root,

    w_S ≤ V(a)  iff  a∈S.

The individual transports between these stages are identities; below the original root that atom has become bottom. Every current individual profile X has one actual extension S⊆D, and exactly w_S represents it. Hence raw UWR_e holds. It also gives raw UFWR_e, since every actual individual property is finite.

This proves relative consistency of Pure Max + Exactly_d(e) + raw UWR_e for EVERY fixed positive finite d. These models additionally have Strong Actuality, every current atom strong, internally countable propositions at every Frege base, and failure of CBC_t. They fail Atomicity because of the surviving atomless remainder. The result therefore shows why the local-Atomicity prerequisite in the separate Max+UFWR infinity theorem cannot simply be discarded.

The original nonunique UCP_e also holds in this model. For a rigid current property X, finite individual-domain listing and C's uniqueness of rigid coextensive properties identify X with the finite union of the relevant individual haecceities. At every isolated stage its transported extension is the same S⊆D. At the stage assigned S, the agreement proposition ∀x(Vx↔Xx) is true, hence possible at the final root. The stronger atomic-agreement principle AUCP_e still fails by the independent Pure Max obstruction. No BF, ND, Atomicity, or signature Max is asserted.

## 11. Pure Max + UCP_e + raw UWR_e with an arbitrary individual set

This is a further relative model construction in ZFC. It shows that compatibility of the nonunique original UCP and the raw unique representation principle with Pure Max does not depend on an actually finite individual domain. No Atomicity, BF, ND or Strong Possibility is asserted.

Let M be the one-atom fresh-constant profile model of §§1–6, with original root m, individual domain {*}, and sole propositional atom r. Choose any nonempty external set D and put I:=P(D)\{∅,D}. For each S∈I add an isolated object v_S over M. Its individual domain is D; its arrow to m sends every individual to *. Its relational domains are the full isolated-root domains

    D_τ(v_S)=P(product of D_argument(v_S)) × D_τ(m).

Each v_S retains the whole old M as its future. Now add a root o with individual domain D, an identity-on-individuals arrow to every v_S, and a direct collapse arrow to m. Identify every composite o→v_S→m with this direct arrow, and identify further composites in the evident way. For an original component arrow k:m→V, its root composite sends every d∈D to k(*). This defines a category and individual action. If I is empty, only the direct arrow o→m is required.

### 11.1 All-type coherent root domains

For τ=σ_1...σ_k t, recursively put

    D_τ(o) = P(∏_j D_σj(o))
             × (∏_{S∈I} P(∏_j D_σj(v_S)))
             × D_τ(m).

A root entity (A_0,(A_S),b) has actual extension A_0, image (A_S,b) at v_S, and image b at m. This satisfies the identified-composite constraint exactly: every path to m gives the same b. Arbitrary actual extensions at the root and at every v_S are allowed; only their old tail entity is shared.

The representation as relational intensions is injective. The identity coordinate distinguishes A_0; the arrow to v_S distinguishes A_S; a difference in b is distinguished at some descendant of m, which is also reachable from o. All truncations lie in the stipulated target domains.

For application, take the current fiber at o, the fiber of A_S at the transported argument in v_S, and the old application at m. These coordinates have the required form. For abstraction with assigned parameters, take its actual extension separately in o and each v_S, and its abstraction with old transported parameters in m. All the v_S abstractions have exactly that same old tail, by term-transport compatibility in their already valid full isolated-root models. Thus the coherent tuple is admitted. Quantifiers at each point range over that point's entire domain; the old tail is the old quantifier, not a restricted-image quantifier. Equality uses literal identity at each current domain with the corresponding old equality tail. H, contextual βη and Logical Equivalence follow by the same actual-extension/component-entity argument as §3. This verifies the whole type hierarchy; arbitrary Boolean gluing at t alone would not suffice.

Pure Max is inherited from M: each C-consistent pure sentence is true at an old component accessible through m. This is still a pure-language claim, with the same original C reference theory.

### 11.2 Exactly one atom for each current individual profile

At t the Boolean algebra is exactly

    2 × 2^I × D_t(m).

Since D_t(m) has precisely the sole atom r, its atoms are: the root-only atom w_∅; one coordinate atom w_S for every S∈I; and the lift w_D of r. The old atomless remainder remains nonzero. Thus the displayed atoms are naturally indexed by ALL subsets S⊆D.

Choose V^{et} with actual root extension ∅, extension S at v_S, and old tail λx.r at m. The common-tail constraint is satisfied, and the entity is admitted. For each a∈D,

    w_S ≤ V(a)  iff  a∈S.

For S=∅ this is its false current root value. For a proper nonempty S this is the v_S coordinate, with identity transport of individuals. For S=D it follows because all a collapse to * and r lies below (λx.r)(*)=r.

Every current predicate X^{et} has exactly one actual extension S⊆D, and precisely w_S represents it. Therefore raw UWR_e holds. This is true for finite or infinite D. When D is infinite, actual Axiom of Infinity_e holds because the root actual relation domains contain all finite-cardinality and Dedekind witnesses; equivalently, no finite cardinality counts the full infinite current D in this full actual-extension structure.

### 11.3 Original UCP_e: the rigidity argument

For every S⊆D define Y_S^{et} by actual extension S at o, extension S at EVERY v_T (not only v_S), and old tail H_*(x):=(x=*) if S is nonempty, or bottom if S is empty. This is an admitted coherent entity. The use of H_* is essential: the old model's futures can acquire individuals beyond the image of *; the universal old predicate would be wrong.

At every point reached from o, the actual extension of Y_S is exactly the transported image of S. At o and v_T this is S; at m it is {*} for S nonempty; further on it is the singleton image of *, as prescribed by H_*. Every point reached from a v_T has the analogous image property. Consequently membership persists. For inextensibility at any such point, suppose all current Y_S-members necessarily satisfy Z. Any Y_S-member at a successor is the transport of a current Y_S-member, so it satisfies Z there. Hence Y_S≤Z. The old H_* is rigid already in C, covering the remaining descendant cases. Thus Y_S is rigid throughout, in precisely the source definition.

If X is any rigid root predicate with actual extension S, C's uniqueness of coextensive rigid predicates yields X=Y_S. For S=∅, V and Y_S agree at o. For proper nonempty S, they agree at v_S. For S=D, their tails agree actually at m, whose sole individual satisfies both r and H_*. Thus ∀x(Vx↔Xx) is true at an accessible point in every case. Original UCP_e follows.

This explicit representative proof is stronger than saying that an identity individual map preserves a rigid property's nonmembers; that unsupported inference was not used. The other root arrows do collapse individuals, and H_* controls the later expansions.

### 11.4 Remaining properties and limits

The root-only atom is true and strong. Every other listed atom is strong: its isolated coordinate either survives as a root-only atom at its own stage, is bottom on the other branches, or is the lift of the old strong atom r. Thus Strong Actuality and 'every current atom is strong' hold. Atomicity fails because the old nonzero atomless remainder survives. AUCP_e fails by the independent general Pure Max obstruction.

The arbitrary current extension coordinate again admits a predicate whose extension is exactly the standard numeral denotations, and old finite components still distinguish all standard numerals. Therefore N_σ(o) is standard at every fixed counting type σ. When D is finite, the exact countability spectrum from §6 is preserved. When D is infinite of external cardinal κ, the propositional domain has cardinal 2^(2^κ), and the atom set has cardinal 2^κ. The external calculations are not claims of fullness for arbitrary Henkin models.

The CBC_t counterexample of §9 lifts from M with zero actual coordinate at o and at every v_S. A bound's old tail would bound the old even-q_n family; lowering that tail strictly while keeping every new actual coordinate fixed gives a strictly smaller root bound. The lifted family has an admitted numerical coding relation at o. Hence CBC_t still fails at every Frege index.

For infinite D this yields a concrete relative model of Pure Max + UCP_e + raw UWR_e + Axiom of Infinity_e, with Strong Actuality and strong atoms, while retaining a nonzero atomless remainder. It does not threaten the AUCP obstruction, the SP obstruction, or the Max+local-Atomicity+UFWR infinity theorem: each distinguishes assumptions that this model lacks or explicitly satisfies in the required way.

## 12. Exploratory boundary: why an atomic Boolean cover does not yet settle Max + Atomicity

**Status: obstruction analysis only. No consistency or inconsistency theorem for Pure Max + Atomicity_t is claimed here.** The product/coherent-tail constructions above inherit an atomless remainder, but this is a feature of those constructions, not a proof that every Max model must have one.

At the level of ordinary Boolean algebras, every Boolean algebra B is a quotient of an atomic Boolean algebra. In ZFC let U=Ult(B)×ω and embed b∈B as its Stone set C_b×ω. Every nonzero such set is infinite. Let A be the subalgebra of P(U) consisting of sets of the form (C_b×ω) Δ F, where F is finite. This representation determines b uniquely: a nonzero symmetric difference between two Stone sets, multiplied by ω, cannot be finite. The map to b is therefore a well-defined surjective Boolean homomorphism A→B. The algebra A contains every singleton of U and is atomic; its kernel consists of finite subsets. Hence atomicity is not preserved by surjective Boolean transport. This construction is not generally complete, and completeness is not being asserted.

However, replacing only a root's propositional algebra by A is not a model construction for C. There are at least three exact further obligations:

1. Every relational type must be lifted together with application, lambda abstraction, logical quantifiers and identity. The quotient maps must preserve all term denotations, and the resulting domains must embed as relational intensions over a category of worlds. An arbitrary Boolean homomorphism does not supply these data.
2. Each new Boolean atom must have a genuine truth location. A root plus one old future cannot distinguish arbitrarily many new atoms all killed by the quotient: only its one current truth bit remains. New worlds and compatible individual/entity transports are required.
3. Identity and quantifiers constrain those new worlds. If two root entities merge in an old future, their equality proposition is nonzero. Atomicity requires some atom below that equality; its truth world must actually identify those entities. Conversely, an atom deciding every current quantified proposition may require witnesses that were absent from the root. It cannot simply be interpreted as a two-valued quotient on the old current domains.

One useful way to state the typed obligation is this. For a candidate atom w, define x∼_w y iff w≤(x=y), at every admitted type. The C equality laws make these equivalence relations compatible with application, and w decides the truth of every current proposition. But the quotient of the current domains need not witness all existential propositions that w makes true. The missing witness property is precisely a quantified lifting issue; it is not supplied by ordinary Boolean atomicity or by the finite-perturbation cover.

Thus a possible route to Max+Atomicity would have to extend these typed quotient diagrams with witnesses while preserving one coherent root model, its all-type closure, and all Pure Max instances. The present note identifies that obligation and stops there. Neither product failure nor the Boolean quotient observation resolves it.

## 13. Cardinality and agreement audit for the arbitrary-D model

The statement Atoms≅P(D) in §11 is an external bijection with CURRENT individual extensions. It is not a bijection with the entire intensional domain D_et(o), which contains many properties having the same current extension. No collapse of those intensional entities is assumed.

There is also a precise internal relational formulation in this model. Its explicit Y_S construction gives a rigid coextension of every current individual property. C makes rigid coextensions unique. Hence the definable relation

    G(w,X) := Atom(w) ∧ Rigid(X) ∧ ∀a(Xa↔w≤V(a))

is an actual bijection between the atom property and the rigid individual-property domain. This is a graph bijection, which does not automatically yield an operation. For |D|≥2, take a nonempty proper singleton {a}. Both w_∅ and w_{a} transport to bottom at the old root m. But their graph-corresponding rigid profiles Y_∅ and Y_{a} transport to bottom and H_* respectively, which are distinct old entities. Any operation realizing the graph would preserve application under transport and would therefore assign two different outputs to the same old input bottom. No such operation exists. Extending the graph off atoms by the default bottom profile makes an explicit total functional relation witnessing failure of the relevant Plenitude instance. This is an example-specific illustration of why the graph/operation distinction matters, not an additional general theorem beyond established Plenitude consequences.

The original agreement propositions can also be computed exactly. Let R be the lift of the old atomless complement ¬r, and write q_S:=∀a(Va↔Y_Sa). Then

    q_∅ = w_∅ ∨ R,
    q_S = w_S ∨ w_D       when ∅≠S⊊D,
    q_D = w_D.

The first formula follows because V is empty at o and in every old proper component, while it is nonempty at each v_S and at m. For a nonempty S, the Y_S tail is H_*: it agrees with V at m, but not in any proper old component, where V is empty and H_* has its distinguished instance. At an isolated v_T it agrees exactly when T=S. These coordinates give the displayed literal Boolean identities.

Thus all rigid profiles have possible agreement, establishing UCP, but raw UWR does not make those agreement propositions atomic. The empty agreement contains the atomless remainder. Every proper nonempty agreement has an additional atom w_D because distinct current individuals merge at m. In the nominal UWR models of main report §35, identity transports and Atomicity remove both obstructions; there the corresponding agreement is exactly one atom. This explains the difference without importing B into a Max model.

## 14. A necessary atom-splitting feature of any Max + Atomicity model

This is a proved conditional obstruction to certain proposed lifts, not a solution of the Max+Atomicity consistency question.

Ordinary Pure Max makes ¬Actuality possible, because C has a model with no true atom. Suppose a Max root also satisfies Atomicity_t. Choose a current atom w below the nonzero proposition ¬Actuality. At any reachable object where w is true, its transported value is true and that object satisfies ¬Actuality. Hence the transported value of w cannot be an atom there. It has a nonzero proper subproposition. A weak root atom has necessarily become split by propositions available at its truth location.

No such proper part can be the image of a root proposition p: otherwise preservation of Boolean meet would send w∧p, which at the root is either bottom or w, to that proper part. Therefore transport to this location is not surjective on the Boolean interval below the image of w. New local propositional distinctions are essential.

In particular, the atomic-cover idea of §12 cannot be completed merely by killing every new atom in the old Max model and making the atoms true only at fresh full isolated roots. Every such isolated root has Actuality, whereas the chosen atom w must have a truth location satisfying ¬Actuality. A successful lift would need genuinely new truth locations with new local propositional distinctions, compatible at every type and with logical quantification.

This is the semantic form of the recorded implications Strong Leibniz_t⇒□Actuality and Atomicity_t+BF_t⇒Strong Leibniz_t, together with Max's incompatibility with □Actuality. It identifies a required failure of local lifting/surjectivity, without treating it as an inconsistency proof for Atomicity alone.

## 15. Pure atom names cannot reach a region with Frege arithmetic

**Status: proved metatheorem, independently checked by the Frege-infinity research lane.** Fix an admitted counting type σ and a closed pure proposition term A. Let Iσ:=◇I*σ, with the fixed definitions in `topics/classicism/background.md`. Then ordinary Pure Maximalism proves the particular sentence

    Atom(A) → A≤¬Iσ.

No Atomicity, ND, BF, Plenitude, Choice, or actual individual infinity is assumed. This is a schema over externally chosen closed pure terms and types; it does not quantify internally over syntax.

First recall two source facts. C is effectively axiomatized. Under Iσ its fixed Frege arithmetic interpretation proves PA (Robinson arithmetic Q would suffice for the incompleteness step). The latter is Goodsell's arithmetic lemma used in `topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`, Lemmas 5–7 and the reference there to source Lemma 1. That write-up also proves C: Iσ→I*σ, and T gives the converse. The present use of arithmetic is exactly the same effective interpreted-theory argument already used to refute Necessity of Arithmetic under Pure Max; it is not an assumption that every Max model has standard natural numbers.

Here is the proof, with the metatheoretic case distinction explicit.

* If C+(A∧Iσ) is inconsistent, the deduction theorem gives C⊢¬(A∧Iσ). Necessitating this discharged C theorem gives C⊢A≤¬Iσ. The required conditional is immediate.
* Suppose C+(A∧Iσ) is consistent. For an ordinary first-order arithmetic sentence H write H^σ for its fixed translation. The theory

      T_A := {H : C⊢(A∧Iσ)→H^σ}

  is a consistent recursively enumerable deductively closed extension of PA. Recursive enumerability follows by enumerating C-proofs; consistency follows because a translated arithmetic contradiction would contradict the assumed C-consistency. The arithmetic interpretation respects the propositional connectives, so deductive closure is inherited. By essential undecidability/incompleteness of consistent r.e. extensions of Q (equivalently one may use Rosser for this PA extension), choose H such that neither H nor ¬H belongs to T_A. Consequently both closed pure propositions

      P := A∧Iσ∧H^σ,       Q := A∧Iσ∧¬H^σ

  are C-consistent: inconsistency of the first would put ¬H in T_A, and inconsistency of the second would put H in T_A. Two ordinary Pure Max instances give ◇P and ◇Q. Thus P and Q are nonzero propositions. Both lie below A by necessitated propositional logic, and P∧Q=bottom. They cannot both lie nontrivially below an atom. Therefore Max⊢¬Atom(A), which in particular gives the displayed conditional.

This proves the claim in either metatheoretic case. It is not a claim that an algorithm can decide which case applies to an arbitrary A, or uniformly output the corresponding independent arithmetic sentence. It is an instance-by-instance mathematical derivability theorem. The Pure Max reference theory remains C, not C+Iσ or C+A.

There is a useful general underlying fact. For fixed closed pure A and P, if C⊢A→P then C⊢A≤P by necessitation. If C does not prove A→P, Pure Max gives ◇(A∧¬P), so Max refutes A≤P. Accordingly, if Max+Atom(A) is consistent, the pure theory C+A is consistent and complete: two C-consistent complementary extensions A∧P and A∧¬P would split A exactly as above. Its completeness is only a necessary condition for a pure atom name; no converse about arbitrary parameter-containing propositions is asserted. Applying essential undecidability to the arithmetic-bearing extension gives the sharper displayed conclusion.

### 15.1 Actuality and Atomicity consequences

Pure Max proves Iσ at every fixed σ. For example, a full S5 C-model with infinitely many individuals and infinitely many worlds satisfies I*σ for every type: each type is infinite and its Frege arithmetic is standard. Pure Max gives ◇I*σ=Iσ. A one-world infinite-individual model would not suffice uniformly, since its proposition type is finite.

Hence, for every fixed closed pure A,

    Max ⊢ ¬(A∧Atom(A)).

Indeed, Atom(A) implies A≤¬Iσ; T turns an actual A into actual ¬Iσ, contradicting Max's Iσ. The source Actuality witness condition is

    A ∧ ∀q(q→A≤q).

It implies Atom(A) in C: any p≤A is true, in which case the witness condition gives A≤p, or false, in which case A≤¬p and p≤A make p bottom. Since A is true it is nonzero. Therefore no closed pure term can witness Actuality under Max. This does **not** refute Actuality: the roots constructed above have a true strong atom not denoted by any closed pure term.

If a Max root satisfies Atomicity_t, its nonzero proposition Iσ contains an atom w. No closed pure A can denote w: the theorem would give w≤¬Iσ as well as w≤Iσ, forcing w=bottom. Thus Max+Atomicity requires atoms outside the closed pure propositional term denotations, even though it need not require any extra primitive symbols in the language. In particular, a propositional term-generated Max model cannot satisfy Atomicity_t. This is an obstruction to a proposed model presentation, not an inconsistency theorem for Max+Atomicity.

### 15.2 Numerical-finiteness reading

The Frege lane's independently checked bare-C equivalence (scratch report §27) is

    ¬Iσ ↔ Nσ(bottom) ↔ Fin_νσ(Nσ),

and ¬Iσ also entails Fin_σ(top), indeed its necessity. Necessitating these C theorems and using the main result shows that any closed pure atom name lies below the region where the σ-domain and its numerical domain are internally Frege-finite. This is asserted separately for each fixed σ. It does not give a single externally standard finite bound, does not identify all atoms with pure names, and does not collapse the general Max+Atomicity problem.

## 16. Max supplies an infinite region of failures of Actuality

This strengthens §14 by an internal infinity theorem. It uses the generic localization argument from the Frege lane's report §21, with a new family of consistent components. No Atomicity, Choice, BF, ND, or Strong Possibility is assumed until §16.3.

Put P:=¬Actuality, and for n∈N_e define

    h(n):=P∧(Suc_e n)(top_e),
    Π:=∀n∈N_e ◇h(n).

Then Pure Max proves Π. Consequently h is a total injective operation from N_e to a pairwise disjoint family of nonzero propositions below P, and the interval ↓P is relationally Dedekind-infinite and hence Frege-infinite.

### 16.1 The consistency construction, including designated-truth care

For every external positive integer j, C is consistent with E_j∧P, where E_j says exactly j individuals exist. To check this, specialize the recorded full Boolean-valued construction `topics/classicism/writeups/full-boolean-valued-atom-and-atomless.md` to a j-element individual domain. Its verification of H and LE uses completeness of B=2×A, crisp identity and full function domains, and is unchanged by replacing the singleton individual set with any nonempty finite set. Here A is a nontrivial complete atomless Boolean algebra, a=(1,0_A), and designated truth is first-coordinate projection.

E_j has Boolean value 1_B. The only Boolean atom is a. The C equivalence Actuality↔∃p(p∧Atom(p)) therefore gives Actuality value a: Atom(p) is crisp in this algebra and true only for p=a. Hence P has value b=(0,1_A)≠0, and ◇(E_j∧P) has value 1_B. Thus E_j∧P is C-consistent; if C refuted it, necessitation would refute its possibility in this C model.

This does not designate an ultrafilter on the atomless part as a truth projection. Such an ultrafilter need not preserve arbitrary quantifiers. The only designated projection used is the complete first-coordinate projection. Ordinary Henkin completeness then supplies a C model M_j actually satisfying E_j∧P.

Coalesce the countable family (M_j) under a free root with one individual, arbitrary current truth extensions at relational types, and the component entity coordinates. The construction can be made directly with Henkin algebras as in §38 of the main report: application takes fibers and component application, quantifiers use each full component domain, and lambda abstraction takes the current root extension and the component denotations. These clauses validate H and the original LE rule.

At the root N_e consists exactly of the standard numeral denotations: their range is an available current predicate, inductive by construction. The numerals are distinct, since a component with sufficiently many individuals distinguishes any given two. Component M_(k+1) makes h(n_k) true. Thus the root satisfies Π, establishing its C-consistency. This standardness assertion concerns this constructed root only.

### 16.2 The internal Max argument

Pure Max gives ◇Π. For an arbitrary current n∈N_e, persistence of numberhood gives □N_en. At a Π-world its image therefore satisfies ◇h(n), so ◇◇h(n); axiom 4 yields ◇h(n). Generalizing over current n proves Π itself. This is the same modal pullback as the recorded Max→Infinity_t argument.

For distinct current numbers m,n, the recorded boxed Exclusivity and Swap lemmas give

    □¬[(Suc_e m)(top_e)∧(Suc_e n)(top_e)].

Hence h(m)∧h(n)=bottom. Π makes every h(n) nonzero, so h is injective. Max gives I_e, and thus successor is injective on N_e and misses zero. Define H(q):=∃n∈N_e(q=h(n)). On Q(q):=(q≤P), the graph

    R(q,r):=[∃n∈N_e(q=h(n)∧r=h(Suc_e n))]
             ∨[¬H(q)∧r=q]

is a total single-valued injective self-relation, missing h(0). The shifted and fixed parts have disjoint ranges; injectivity on the shifted part follows from that of h and successor. The missing-value argument uses that zero is not a successor. The C finite-cardinality Dedekind lemma therefore gives

    Max ⊢ ¬∃m∈N_t m(λq.q≤¬Actuality).

No operation with individual output, numerical choice, or Boolean completeness is used. This is an internally quantified interval-infinity theorem, not merely an external collection of arbitrarily large finite examples.

### 16.3 Atomicity would force weakly Dedekind-infinite splitting atoms

Assume only local Atomicity below P: every nonzero q≤P has an atom below it. Full Atomicity_t implies this. Put

    A(w):=Atom(w)∧w≤P.

Define a numerical coding relation on A by

    C(w,n):=A(w)∧N_en∧
       [(w≤h(n))∨(n=0_e∧∀m∈N_e ¬(w≤h(m)))].

A nonzero atom can lie below at most one of the pairwise disjoint h(n). Thus C is total and single-valued on A, with the default value zero for atoms lying below none of them. For every n, local Atomicity supplies an atom below the nonzero h(n), and that atom has code n. Hence C is a surjective relational graph A→N_e. No simultaneous selection of one atom per number is needed. In particular A is Frege-infinite; a finite domain has only a finite functional image, whereas N_e is Dedekind-infinite under Max's I_e.

Every member of A fails to be a strong world. In C a strong world w entails Actuality: its boxed settling condition ensures that, wherever w is true, it entails every true local proposition and so witnesses Actuality there. Thus SWorld(w) gives w≤Actuality, incompatible with nonzero w≤P. Equivalently, each such root atom becomes nonatomic at every truth location, as §14 showed, and the new local splitting propositions cannot all be root images.

Therefore any Max+Atomicity_t model must have a current class of non-strong atoms that surjects onto the full current N_e by an admitted relational graph. This is stronger than merely requiring one non-strong atom or an externally infinite set of them. It does not give an injection N_e→A without a further selection principle, does not make the graph into an operation without a representation premise, and does not resolve consistency of Max+Atomicity.

### 16.4 General localization lemma behind the construction

The same proof gives a reusable metatheorem. Fix a closed pure proposition P and a closed pure property F^{ρt}. Suppose, for every externally standard positive j,

    C + P + (the j-th ρ-numeral)(F)

is consistent. Then Max proves that ↓P is relationally Dedekind-infinite. Use h(n)=P∧(Suc_ρ n)(F) and the same Π, countable coalescence, numerical persistence, boxed Exclusivity/Swap, and shift argument. In the consistency construction the components with sufficiently many F-instances distinguish the standard ρ-numerals; the arbitrary current root predicate again makes the root N_ρ exactly their range. F need not be rigid, and no fixed actual size of the root ρ-domain is required.

Under local Atomicity below P, the same labeling relation gives atoms-below-P↠N_ρ. The proof uses each finite consistency premise only to build one metatheoretic component family establishing a single C-consistent Π sentence. It does not conflate an external finite-size schema with internal Infinity: the quantified Π and Max pullback are precisely what supply the internal conclusion.

The Frege report §21 is the case P=Exactly_r(e), F=Atom_t, ρ=t. The present §16 is P=¬Actuality, F=top_e, ρ=e. This common formulation makes the exact compatibility premise visible and avoids treating either example as an unexplained modal strengthening of an external infinity schema.

### 16.5 Finite propositions would supply Actuality

Already in C,

    Fin_t(top_t) → Actuality.

The currently true propositions form the admitted property T(p):=p. Finite-subset closure makes T finite if the whole t-domain is finite. By induction on a finite cardinality, every finite property X of true propositions has a true common Boolean lower bound. The empty case uses top. In a successor case remove one instance a; a true lower bound b for the remainder gives the true lower bound b∧a for X. This uses only the finite-cardinality deletion clause and conjunction. Applying it to T produces a true proposition below every current true proposition, exactly an Actuality witness.

Consequently ¬Actuality entails actual Frege Infinity_t, and hence I_t. This gives another useful consequence of §15: in any Max+local-Atomicity-below-¬Actuality model, none of the atoms in §16.3 can be denoted by a closed pure term. Each lies below I_t, whereas every such pure atom name would lie below ¬I_t. Thus the required weakly Dedekind-infinite class consists of non-strong, non-pure-denotable atoms.

Audit note, 22 October 2026, 20:27 UTC: the finite-D Boolean-valued calculation, the countable algebraic coalescer, the standard-numeral range argument, the modal Π pullback, the interval shift and the atom-to-number labeling were independently rechecked in this research lane. This remains an agent mathematical audit, not human checking or Lean verification.
