# Independent adversarial audit: pure term profiles at an isolated root

22 October 2026. Audit by an OpenAI Codex research agent. Ordinary mathematics; no named human checking, proof-assistant verification, or literature novelty claim. No main database record was edited.

**Verdict.** The core model in `profile-root-construction-20261022.md` §§1–5 passes. Its finite Fregean atoms, internal countability, and the ensuing obstruction arguments in `research/2026-10-22/strong-possibility-obstructions.md` §§2–6 pass. One necessary intermediate argument was compressed in the source note: agreement of truth at all pointed component objects must be converted into equality of component proposition entities using their action-model intensions and inclusion of all descendants. Section 4 below supplies it explicitly. No counterexample or substantive repair of the construction was found.

## 1. Scope and exact assumptions

The language is the original finitary relational language of C: types arise from e and t by σ→τ only for τ≠e. No optional preset, Extensionality, Barcan Formula, Choice principle, or full function space is assumed of the components. Work in ordinary ZFC metatheory. Fix a set of pure C action models witnessing every C-consistent pure sentence, and include all their objects and arrows. It is enough to choose one witness for each consistent sentence and add the finite full extensional models explicitly. The latter addition is harmless.

I checked `topics/classicism/topic.yaml`, the Framework and Notation sections of `background.md`, the exact Strong Possibility, Fregean Axiom, Atomicity, Extensionality, and Functionality records, and the coalesced/pinned-root writeups. I also checked the action-model interpretation clauses directly in Bacon–Dorr's [author-hosted Classicism draft](https://andrew-bacon.github.io/papers/Classicism.pdf), dated 1 July 2022: Definitions 3.18–3.20, pp. 55–56. Its quantifiers use the domain at the target object. Its completeness/coalescence background is not a proof of this particular restricted-profile construction. The bundle cites a different, 16 May 2023 draft and pagination.

## 2. A fully specified premodel embedding

Write J for the set of pointed component objects (V,a), with a∈D_e(V). Add o, with D_e(o)={*}, and arrows h_(V,a):o→V. Put k h_(V,a)=h_(V',ka). Component transport is functorial, so this is associative and the individual action is well defined.

For a relational type σ, let B_σ consist of families

    b_T(V,a) = [[T(z)]]_V[a/z]

where T is a pure σ-term with no free variable other than the individual z. Quotient by equality of these families, not merely by equality of their actual truth values. This distinction matters at non-Fregean component objects. Pure syntax is countable, so B_σ is countable and nonempty. The only e-profile needed at o is z.

If σ=τ₁…τₖt, recursively set

    D_σ(o) = P(D_τ₁(o)×…×D_τₖ(o)) × B_σ.

The recursion is well founded: every input type τ_i has smaller syntactic size than σ. In the empty-argument case the powerset is 2.

Represent (S,b_T) as the following relational intension. At 1_o its extension is S. At h_(V,a), its extension is the actual extension in V of b_T(V,a). This representation is injective. The identity coordinate recovers S. If b_T≠b_U, their values differ at some (V,a). Distinct component relations have distinct intensions; hence some component arrow k:V→V' and some tuple at V' distinguish their extensions. The root arrow k h_(V,a)=h_(V',ka) distinguishes the two root intensions. Notice that the availability of *all* pointed component objects is used here.

The truncation of (S,b_T) along h_(V,a) is exactly b_T(V,a). At a subsequent k:V→V', its extension is that of

    b_T(V',ka) = k b_T(V,a),

by transport compatibility of term interpretation in the component. Consequently every truncation lands in the component domain, with its existing action. Thus the pairs really are a subaction of the corresponding relational-intension/exponential action; this is not merely an abstract algebra on pairs.

For application, if f=(S,b_T) and u has profile U, define f(u) to have actual extension S_u (the relevant fiber) and profile T(U). Its profile is independent of representatives, since equal component parameter entities remain equal in every term context. The transport equation

    h(f(u)) = (hf)(hu)

holds componentwise. At an outgoing arrow and an arbitrary argument that did not come from o, application is simply the pre-existing application in that component. This is the part of the exponential action that is easy to omit if one writes only the root application formula.

## 3. Closure, H, and Logical Equivalence

Fix any term R with finitely many assigned root parameters. Choose a pure z-profile T_i for each relational parameter and z for each individual parameter; make bound variables fresh. Simultaneous capture-avoiding substitution gives a pure term R*(z). At any h_(V,a), the interpretation of R with transported parameters is [[R*]]_V[a/z]. This statement follows by structural induction. In the quantifier case the quantifier in V ranges over D_σ(V), exactly as it already did in the component. It does not range only over images of D_σ(o).

For abstraction λx.R, its root actual extension is the set of root tuples satisfying R under the root assignment. It is admitted without restriction. Its outgoing profile is the pure abstraction obtained after substituting only its free parameters, leaving x bound. At every component it has the entire component abstraction, including its behavior on component arguments outside the root transport image. Hence the pair lies in the prescribed domain. This proves closure under all terms, including the quantifier and identity constants.

For precision, the logical ∀_σ at o is the pair whose actual extension consists of the predicates true of every root σ-entity and whose profile is the pure quantifier constant ∀_σ. Its transport is the component quantifier. Equality has the actual literal equality relation on root entities and its usual pure profile. Equality can therefore become true after transporting unequal root entities; that is permitted in C and does not violate NI.

β and η hold as identities of denotations: their actual extensions agree by substitution/fibers, and their component profile entities agree by component βη. This validates the strong contextual βη schemata of H, not just material equivalence of the final actual truth values. Propositional and quantifier axioms use their usual actual clauses. Literal equality gives reflexivity and Leibniz substitution. The ordinary inference rules preserve validity under all assignments.

For Logical Equivalence, assume H proves P↔Q with its original theoremhood restriction. Under any root parameters, the abstractions λx̄.P and λx̄.Q have the same actual extension by H soundness. In every component, the same H-equivalence instance is validated by C as equality of the two abstractions under the transported parameters; so their profile families are equal. Their root pairs are equal. Components already satisfy the schema. Hence the constructed model validates C. No inference from equivalence under optional hypotheses to identity has entered this argument.

**Status: pass, with the embedding and full component-abstraction details supplied.** In particular, lack of surjectivity of root transports is not a gap. Replacing this construction by a constant-domain global quantifier interpretation would be a different, generally invalid argument.

## 4. Maximalism and the finite Fregean atoms

Every C-consistent closed pure sentence P holds at some selected component object V. Pick a∈D_e(V). Its root denotation has a true point at h_(V,a), and so is nonbottom. This is the pure Possibility form of Maximalism. Equivalence with the recorded Distinctness form is a theorem of C.

Let A_n=F∧E_n, n≥1. At any component object satisfying A_n, F gives Extensionality at every relational type. D_t has exactly two elements. Induction on types now proves that the local structure is the full finite extensional hierarchy over its n-element individual domain. At an inductive function type the input and output domains are finite; any desired extension is represented using a finite disjunction of equality tests with those finitely many entities as parameters. Extensionality rules out duplicate entities having that extension. This proves both fullness and uniqueness, even if the surrounding component was originally nonfull and nonextensional elsewhere.

Every bijection between two n-element individual domains extends recursively to an isomorphism of their full finite hierarchies. The permutation action on individuals is transitive. Therefore, for each fixed pure proposition term T(z), its actual truth has one fixed value ε_(T,n) at *every* pointed component object (V,a) satisfying A_n.

Here is the important profile-entity step. If ε_(T,n)=0, then T(a)∧A_n is false at every pointed component object: at A_n-objects this follows from ε=0, and elsewhere from ¬A_n. Fix any (V,a) and any descendant k:V→V'. The transported conjunction is T(ka)∧A_n at (V',ka), also false. Its component proposition intension is empty. Thus T(a)∧A_n equals bottom as an entity in D_t(V), for every (V,a). If ε_(T,n)=1, the same argument applied to the symmetric difference of T(a)∧A_n and A_n shows equality of their component entities. Therefore the *family profile*, not merely its actual truth pattern, is either bottom or the A_n profile.

At o, F is false: for example (1,bottom-profile) and (1,top-profile) are two distinct true propositions. Thus A_n has actual bit 0. For an arbitrary p=(b,b_T), the actual bit of p∧A_n is also 0. Combining this with the profile conclusion gives literally

    p∧A_n = bottom  or  p∧A_n = A_n.

A full finite n-individual component witnesses A_n≠bottom. Hence Atom_t(A_n) holds at o, simultaneously for every n. This argument needs no claim that all C-models satisfying A_n have trivial future categories: only their local full extensional isomorphism type and truth separation of component propositions were used.

**Status: pass.** The arbitrary actual coordinate also gives the true root-only atom (1,bottom-profile), so this root has Actuality and distinctness-preserving modal collapse. It is not a Strong Possibility model.

## 5. The internal-countability assertion

D_t(o)=2×B_t is externally countable and infinite. The profiles E_n are pairwise separated by finite extensional components.

Let ν_e=(et)t. The numeral values n_e are pairwise distinct because finite extensional components distinguish any two: in a component with m individuals, the m-th cardinality holds of top_e and any distinct numeral does not. The root subset of D_ν_e consisting precisely of the standard numeral values is an admitted actual extension of an entity of type ν_e t, regardless of its chosen profile. It contains zero and is successor-closed. Therefore the impredicative finite-cardinality predicate contains no extra root values. Conversely finite induction puts every standard numeral in it.

Choose an external injection D_t(o)→{n_e:n∈N}. An actual graph relation of type t ν_e t is admitted, with any profile. At o it satisfies exactly the background definition of Ctbl_(e,t)(top_t): two propositions share a natural-number index if and only if they are the same root entity. No surjectivity, choice operation with individual output, or Countable Boolean Completeness is being asserted.

**Status: pass.** An external countability claim alone would not have sufficed; the freely admitted graph and the standardness proof are what establish the internal claim.

## 6. Audit of the Strong Possibility obstruction chain

### 6.1 Universal identity reflection

If a universally quantified finite Boolean combination U of typed identities fails, choose an actual countertuple and one true DNF clause witnessing ¬U. Let q be the conjunction of its disequality literals, or top if none. q is true. NI makes its equality literals ordinarily necessary. For each disequality a≠b, NI's contraposition proves □(◇(a≠b)→a≠b). Consequently □(◇q→¬U), and q witnesses □ne¬U. This proves ◇ne U→U without a Barcan principle. Terms occurring inside identities may themselves contain quantifiers; NI still applies to their denotations.

Atom(A_n) is in this fragment, after expanding algebraic order as a Boolean identity. Its Max-consistency is established above. Therefore pure Strong Possibility entails Atom(A_n), for every n≥1. **Pass.**

### 6.2 Signature obstruction

For a relational constant c:τ, both A_n∧(c=top_τ) and A_n∧(c≠top_τ) have full finite extensional models, by choosing c=top_τ and c=bottom_τ. Signature Max makes both nonzero. They are disjoint parts of A_n, refuting its atomicity. Thus pure Strong Possibility and signature Max are incompatible for every admitted signature. This uses only two signature-Max instances. It does not infer inconsistency of either Strong Possibility theory by itself. **Pass.**

### 6.3 Barcan and Functionality

From Atom(a), every actual p satisfies a≤p∨a≤¬p. Each disjunct is an identity, hence ordinary NI gives necessity of their disjunction. BF_t then gives the necessary universal clause in the atom definition. The nonzero clause is □ne-persistent by the disequality argument, so BF_t∧Atom(a) entails □ne Atom(a). An ordinary full coalesced Max root, with two separately selectable copies of a finite A_1-component, witnesses Max+¬Atom(A_1). Strong Possibility consequently gives ◇ne¬Atom(A_1), contradicting BF_t and its forced Atom(A_1).

Every relational σ has t as a split retract using constant functions and evaluation at any actual argument tuple. The identity r(c(p))=p is β-provable, so BF_σ transfers to BF_t. No globally fixed choice of those arguments is required. At e, the already recorded SP→E_1 together with BF_e would imply necessary E_1, contrary to pure Max's ◇E_2. Hence SP refutes BF at each type.

At any input σ and relational output τ, suppose Functionality_(σ,τ). Given ∀x□Px, the functions f(x)=top_τ and g(x)=λȳ.Px agree on every actual x, by the definition of □ and β. Functionality gives f=g. NI plus the ordinary necessary coextension of equal relations yields □∀x∀ȳ Px, and nonemptiness of the output argument types gives □∀xPx. Thus this Functionality instance implies BF_σ. Strong Possibility refutes every such instance. **Pass.**

## 7. Additional profile-note claims checked

The later pointed-completeness criterion has the correct extra individual-marker condition. If C+A does not decide some unary P(x), unary Possibility+ under Max makes A∧P(b) and A∧¬P(b) nonzero for each actual b, so A cannot be an atom. If it does decide every such P, the profile argument above applies. Its additional argument that A cannot be actually true at a Max root correctly uses the nonexistence of a consistent r.e. theory containing Max. This latter obstruction is an extension of a published non-r.e. argument, not a novelty claim. For infinite signatures its reduction to the finite sublanguage occurring in A is needed; merely calling an infinite-signature theory r.e. would not suffice.

The finite-signature singleton diagrams pass: higher-type values in the singleton extensional hierarchy have finite pure term representatives, and those diagrams determine every profile truth even with the marker. Ordinary unpointed completeness is insufficient in a relational-only signature with more than one individual orbit, as the note correctly warns.

The arbitrary atomic/atomless pattern construction passes. Auxiliary symbols are semantic devices, not a change in the final reference language. At an A_m-point, every d_(n,j) with n≠m is literally bottom because that point is Fregean. For n outside the requested atomic set, a fresh d_(n,j) can be toggled between A_n and bottom while keeping the finitely many symbols in a chosen nonzero p≤A_n fixed. Both resulting profiles are realized by included component expansions, so p has two disjoint nonzero parts. Its actual bit is already zero. This proves the atomless assertion, not only failure of atomhood. The construction still has countably many finite-syntax proposition profiles and the same internal graph witness.

## 8. Remaining limits

The profile root supplies consistency witnesses for selected unboxed strengthenings of Max; it does not construct Strong Possibility. Deleting the freely chosen root truth bit destroys the present closure argument unless actual truth, equality, and all Henkin conditions are rebuilt together. The pointed-term-generation and named-neighborhood criteria are sufficient conditions only; their realizability remains a separate problem. The extension obstructions show that changing the reference signature is mathematically consequential. They do not justify transferring Strong Possibility between signatures or treating a missing database arrow as a nonimplication theorem.
