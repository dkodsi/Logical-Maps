# Structural algebraic research: boxed Plenitude and stronger world principles

Research notes, 22 October 2026. Prepared by OpenAI Codex research subagent. These are ordinary mathematical arguments, not Lean formalizations and not literature-novelty claims. No published or human-authored records have been changed. New arguments below would have direct source `misc`; the existing map results cited here retain their own attribution.

## 0. Fixed framework and verified starting point

Work in the fixed relational type theory C. Put T = C + □Plenitude, equivalently C + □ND + Atomicity. The box on ND is essential. All optional principles were queried as premises, not engine background.

Using `scripts.pmap.load_topic` and an `Engine` containing only proved results/models, the premise `necessary-plenitude-r` entails:

- □BF, via □ND;
- □Rigid Comprehension;
- Boolean Completeness;
- □Actuality;
- □Strong Leibniz;
- No Pure Contingency.

The last already has a substantial atom-transposition/conjugation proof in `topics/classicism/writeups/c5-and-atomicity-imply-no-pure-contingency.md`. Finite world swaps and pure world homogeneity are therefore NOT new discoveries here. Background definitions are in `topics/classicism/background.md`; the recorded equivalence is `results/c5-and-atomicity-imply-necessary-plenitude.yaml` and the converse records. Full S5 is the special case described by `models/full-infinite-s5.yaml`, referring to Classicism §3.5, pp. 58–61. The new nominal models below differ from the recorded one-object finite-support action model, whose worlds are permutations and whose proposition algebra is atomless.

Write W(a) for Atom_t(a), and write a ≤ p for algebraic entailment. In the concrete S5 models below, W(a) means that a is a singleton subset of the external world set. A rigid relation has a world-independent extension. This latter semantic description agrees with the map's Persistent + Inextensible definition in these constant-domain S5 models: persistence gives constant membership; conversely a constant extension meets the inextensibility condition. For object-language arguments over T, use the corresponding rigidity characterization proved from □ND, BF and rigid comprehension; do not silently substitute Gallin's different definition outside T.

## 1. Internal complete subalgebras are exactly world partitions

This is a classical algebraic idea adapted to the admitted higher-order families of T. It is an internal theorem, not a claim of external powerset fullness.

A **complete subalgebra predicate** is a rigid A^{tt} whose actual extension contains complements and the meet of every admitted family lying in A. More explicitly:

1. A is rigid;
2. ∀p(Ap → A¬p);
3. ∀X^{tt}[(∀p(Xp → Ap)) → ∃q(GLB(q,X) ∧ Aq)].

The empty family supplies top, complement supplies bottom, and two-element families supply binary meets. Thus separate top/bottom/binary-operation clauses are redundant. Completeness here quantifies only over properties X present in the type hierarchy.

An equivalent, more perspicuous definition over T restricts X to rigid families and replaces GLB by the explicit conjunction

    m_X := ∀p (Xp → p).

For rigid X, m_X is its meet: Xq gives □Xq, so m_X ≤ q; conversely a lower bound z gives □(z → (Xq → q)) for each q, and BF gives z ≤ m_X. Rigid comprehension replaces an arbitrary actual family by a rigid coextensive one, proving equivalence with clause 3. This simplification is valid over T, not automatically over bare C.

For a rigid equivalence relation E^{ttt} restricted to world atoms, define

    A_E(p) := ∀a b [(W(a) ∧ W(b) ∧ Eab) → (a≤p ↔ b≤p)].

For a rigid complete subalgebra A, define

    E_A(a,b) := ∀p [Ap → (a≤p ↔ b≤p)]

on world atoms. Then:

**Theorem 1.** These constructions are mutually inverse between admitted rigid equivalence relations on worlds and admitted rigid internally complete Boolean subalgebras of propositions.

**Proof.** A_E is rigid because all displayed tests are rigid. Complements preserve the equivalence of membership at a and b. If every member p of an admitted family X is E-invariant, and m is its meet, then

    a≤m iff ∀p(Xp → a≤p),

and the same holds for b. Thus m is E-invariant. This verifies internal completeness without external intersections.

For A, fix a world a and form the admitted rigid family

    L_a(p) := Ap ∧ a≤p.

Its meet c_a lies in A. It is nonzero because a≤c_a. A world b lies below c_a iff it lies below every A-proposition containing a. Because A contains complements, this is equivalent to E_A(a,b): disagreement in either direction is detected either by p or by ¬p. Consequently c_a is precisely the proposition comprising the E_A-class of a.

If p is E_A-invariant, it is the join of the c_a with a≤p. This is an admitted family: c_a is uniquely specified by GLB, and Plenitude represents the unique assignment a↦c_a, or one can use the explicit rigid-family conjunction above. Each such c_a belongs to A. Internal join closure therefore gives Ap. Conversely every member of A is E_A-invariant by definition. Hence A_{E_A}=A, with equality of the rigid properties justified by necessary coextension.

For E, the class proposition

    d_a := ∃b (W(b) ∧ Eab ∧ b)

is admitted and lies in A_E. Actuality and atomhood show that a world b lies below d_a exactly when Eab. If a and b are not E-equivalent, d_a distinguishes them. Thus E_{A_E}=E on worlds. ∎

Every internal complete subalgebra is itself atomic: its relative atoms are exactly the distinct class propositions c_a. No representative-selection axiom is needed; quotient classes have canonical proposition codes. Refining a world partition enlarges the corresponding complete subalgebra. This gives the usual order reversal between partitions and complete subalgebras, with all objects internally represented.

### Generator criterion and improved definition

For R^{et}, its world profile partition is

    E_R(a,b) := ∀x^e (a≤Rx ↔ b≤Rx).

The internally complete subalgebra generated by {Rx:x∈e} is exactly A_{E_R}. In particular,

    ∀a b [W(a) ∧ W(b) ∧ a≠b → ∃x ((a≤Rx) xor (b≤Rx))]

is equivalent over T to saying that {Rx} completely generates the proposition algebra.

For a direct proof, the meet of the admitted literal family

    L_a(p) := ∃x [(a≤Rx ∧ p=Rx) ∨ (¬(a≤Rx) ∧ p=¬Rx)]

has exactly the worlds with a's R-profile below it. When R separates worlds this meet is a itself, by Atomicity. The admitted join of the worlds below any p is p, again by Atomicity. Conversely, if a≠b have the same profile, the proper complete subalgebra {p:a≤p iff b≤p} contains every Rx. This is a useful alternate definition, not a strengthening and not new language.

## 2. A general nominal S5 Henkin construction

Let W be an infinite set and G a permutation group on W. For a finite S⊆W, G_(S) denotes its pointwise stabilizer. An object is finitely supported if fixed by G_(S) for some finite S.

Take D_e={*}, with trivial G-action. Take D_t to be all finitely supported subsets of W, with the usual direct-image action. For every admitted function type στ (τ≠e), put

    D_{στ} = {f:D_σ→D_τ : f has finite support},

with conjugation action (g·f)(x)=g·f(g^{-1}·x). This is a set-sized typed hierarchy. Evaluate p∈D_t at w by w∈p. Equality at every type is literal equality, represented by W when true and ∅ when false. Application is ordinary function application.

**Closure details.** A term with finitely many parameters has support contained in the union of their supports. Application is equivariant. If a body is supported by S together with the support of its bound argument, its lambda abstraction is supported by S. Negation and conjunction are the equivariant Boolean operations on subsets of W. The universal-quantifier constant sends f∈D_{σt} to ⋂_{x∈D_σ}f(x); this intersection has any support of f because G permutes D_σ. The quantifier operation itself is equivariant and therefore belongs to the required type. Equality is likewise equivariant. Thus all lambda terms, quantifiers and logical constants are admitted.

All H axioms are valid. H-equivalent formula bodies have identical subsets of W for every assignment, hence identical lambda denotations; Logical Equivalence is valid. Thus this is a model of C, not merely a low-type Boolean example. Necessity defined by p=top is exactly truth at every w∈W. Identity is rigid, domains are constant, and □ND and □BF hold.

By iterated currying, D_{σ_1…σ_n t} is exactly the set of finitely supported subsets of W×D_{σ_1}×…×D_{σ_n}. Both directions matter: the section of a supported relation at a supported argument has support contained in their union, while conjugation of the curried function is precisely the diagonal action on the relation.

**Atomicity.** If R is nonempty, choose a point (w,x_1,…,x_n) in it. The singleton relation at that point is supported by {w} together with finite supports of the x_i, so is in the hierarchy. It is an atom below R. Thus Atomicity holds at every relational type, including t; Actuality is witnessed by {w} at w. Hence the recorded equivalence already yields □Plenitude.

There is also a direct check of Plenitude. If U is functional at w_0, let f(x) be its unique actual output. If U has support S, the graph of f is invariant under G_(S∪{w_0}), by functionality and equivariance. Hence f is an admitted operation whenever its output type is relational. The same argument works at every world. This verifies □Plenitude independently of the recorded equivalence.

**Rigid comprehension and internal completeness.** Freeze a relation's extension at w_0; the resulting constant extension has support S∪{w_0}. For an admitted family at w_0, its actual collection of members is invariant under such a stabilizer, so the intersection/union of those members is supported. Thus these models validate the internal completeness/rigidity consequences directly while potentially omitting many external subsets.

## 3. Exact internal natural numbers in these models

Use the map's prescribed index type ν=(tt)t and Frege zero/successor. Write c_n for its n-th numeral. Each c_n is a pure term, hence fixed by G. Because W is infinite, D_t contains arbitrarily many distinct singleton propositions. Induction on n shows that c_n applies to a property F exactly at worlds where F has n instances. The c_n are therefore pairwise distinct.

The rigid predicate whose extension is {c_n:n∈N_external} is G-invariant, so it belongs to D_{νt}. It contains zero and is successor closed. The impredicative definition FiniteCardinality_t therefore contains no other objects. Conversely each c_n belongs to every inductive property by ordinary finite induction. Thus internal natural numberhood is EXACTLY the standard sequence c_n in these models.

For any proposition p define

    W_p(a) := W(a) ∧ a≤p,
    FinW(p) := ∃n^ν (FiniteCardinality_t(n) ∧ n W_p),
    InfW(p) := ¬FinW(p).

In these models FinW(p) means that the external subset p⊆W is finite. This exactness has been proved here; it must NOT be assumed in an arbitrary Henkin model. An external infinite domain may be internally finite in a nonstandard model. Likewise the Infinity schema and the single Frege Axiom of Infinity are distinct hypotheses in the database. In the present models D_t is standardly infinite, the standard-number predicate is admitted, and the type-t Axiom of Infinity holds; D_e is singleton, so no type-e infinity is claimed.

## 4. Unordered nominal worlds: all external symmetries, but no infinite splitting

Take G=Sym(W). Its finite stabilizer orbits are the points of S and W\S. Consequently

    D_t = FinCof(W).

All external permutations of W act on, and lift through, the entire hierarchy. Nevertheless no proposition splits W into two infinite parts. Thus T does not imply the natural principle

    ISplit: ∀p [InfW(p) → ∃q(q≤p ∧ InfW(q) ∧ InfW(p∧¬q))].

The failure is at p=top. This is a fully explicit S5/Henkin countermodel in ordinary ZFC, not a full powerset S5 model and not a model relying on choiceless metatheory.

### Intensional Choice holds at every type

Let F⊆W×D_σ be supported by finite S and inhabited over every world. Choose u∉S and x with (u,x)∈F. Choose a finite support T_x for x, and put T=(S∪T_x)\{u}. For w∉T choose a permutation g fixing T with gu=w and define f(w)=gx. This is independent of g: two such choices differ by a permutation fixing T∪{u}, which contains a support of x. Since S⊆T, equivariance of F gives (w,f(w))∈F. This generic part of f is G_(T)-equivariant.

For each of the finitely many w∈T, choose any witness x_w∈F_w. Enlarge T to a finite B containing supports of all these witnesses. The completed f is G_(B)-equivariant: the generic part remains equivariant, and every exceptional point/witness is fixed. Its graph is a finitely supported subset of W×D_σ, hence an admitted property G≤F with one instance at every world. This proves Intensional Choice for every σ, and therefore its boxed form as well. Only finite witness choices and one generic witness were used.

### Relational Choice fails

At type t, let U(p,q) hold rigidly iff p has exactly two world atoms and q is one of them; for other p, let the unique allowed q be bottom. This relation is equivariant, admitted and serial. A functional subrelation at an evaluation world w_0 would give a selector whose actual graph is invariant under G_(S∪{w_0}) for some finite S. Choose distinct a,b outside that support. The transposition of a,b fixes the input p={a,b} and fixes the support, but swaps its two allowed outputs. Uniqueness is impossible.

Thus this model satisfies T + □Intensional Choice and refutes Relational Choice (and hence Functional Choice). The distinction is substantive: Intensional Choice indexes its selection by worlds; general Relational Choice can require selecting from all unordered pairs of worlds.

## 5. Ordered nominal worlds: repeated splitting without a countable list

Take W=Q, G=Aut(Q,<), and the same finite-support hierarchy. A finite S cuts Q into finitely many point orbits and open-interval orbits. Consequently D_t consists exactly of finite unions of intervals and points with rational endpoints, allowing unbounded intervals and either inclusion of an endpoint.

Every infinite admitted p contains an open interval. Choose c inside that interval and put q=p∩(-∞,c). Both q and p\q are infinite and admitted, with support enlarged by c. Hence ISplit holds.

Define the global principle of **countably many disjoint possibilities** by existence of F^{νt} such that for all internal naturals n,m, Fn≠bottom, and n≠m implies Fn∧Fm=bottom. In this model it fails. If F has finite support S, every numeral c_n is fixed by G, so every F(c_n) is invariant under G_(S). It is therefore a union of the finitely many G_(S)-orbits. At most 2|S|+1 pairwise disjoint nonempty such sets exist. The same argument rules out an internal injective enumeration of infinitely many distinct world atoms, and a fortiori any enumeration of all worlds.

This is a genuine distinction between arbitrarily repeated existential splitting and a single operation collecting infinitely many choices. It does not arise from nonstandard natural numbers; §3 proves the indices standard.

**Intensional Choice fails here.** Define the equivariant F∈D_{tt} by

    F({r}) = {q:q<r},
    F(p)=∅ when p is not an atom.

Every world q has an F-instance {r} with r>q. A uniquely selecting G≤F with finite support S would induce a G_(S)-equivariant f:Q→Q satisfying f(q)>q. Choose q above every point of S. The stabilizer of S∪{q} must fix f(q), by uniqueness; its only fixed rational points are S∪{q}, all ≤q. Contradiction.

Accordingly ISplit and Intensional Choice are incomparable over T, using §4 in one direction and this model in the other.

### Global countable disjointness is not the same as local splitting

Take W=A⊔N with A an infinite set, and let G=Sym(A) fix every point of N. Then

    D_t = FinCof(A) × P(N).

The sequence of singleton N-worlds is an admitted equivariant countable sequence of disjoint possibilities. But the proposition A is infinite and unsplittable. Thus global countable disjointness does not imply ISplit; the ordered model gives the converse nonimplication. These statements should not be called a linear hierarchy without distinguishing global existence from the local principle requiring countably many disjoint subpossibilities below EVERY infinite p.

In full S5 models in ZFC, ISplit and countable disjointness hold whenever the world set is infinite. Full S5 with uncountably many worlds has countable disjointness but no enumeration of all world atoms. Under □Functional Choice, the standard internal choice/well-order arguments are expected to absorb the splitting fragments; they are useful intermediate separations, not proposed additions beyond full Choice. A complete object-language reduction of each fragment to the map's Frege arithmetic and choice records should be supplied before recording those implication arrows.

## 6. Universal profiles and reversible rearrangements

Let EU_e be the root lane's principle that there is R^{et} whose possible extensions include every rigid property of individuals:

    ∃R ∀X (Rigid(X) → ◇∀x(Rx↔Xx)).

Define Inv(K) for K^{eet} to mean that K is total, single-valued and symmetric. Thus it is the graph of an involutive permutation of individuals; no forbidden type ee is introduced.

Define **Universal Involution**:

    ∃H^{eet}[□Inv(H) ∧ ∀K^{eet}((Rigid(K)∧Inv(K)) → ◇∀x y(Hxy↔Kxy))].

**Theorem 2 (precise coding hypotheses).** Over T, suppose there are rigid graphs coding an injection e×e→e and two disjoint injections e→e. Then EU_e is equivalent to Universal Involution.

**EU implies Universal Involution.** Let c code pairs injectively. For every rigid K, its coded graph is the rigid unary property Y_K(z) holding just when z=c(x,y) and Kxy. Decode the universal unary R into Bxy:=R(c(x,y)), expressed by relational graph quantification. At a world where R has extension Y_K, B has extension K. Define

    Hxy := (Inv(B)∧Bxy) ∨ (¬Inv(B)∧x=y).

At every world H is an involution: it uses B when B is an involution and otherwise the identity. Every rigid involution is still realized. All constructions are lambda terms of admitted relational types.

**Universal Involution implies EU.** Let i_0,i_1 be the disjoint injections. For any rigid X, form the rigid involution K_X swapping i_0(x),i_1(x) when Xx, and fixing every other point (including the two points when ¬Xx). Injectivity/disjointness make this a total single-valued symmetric relation. Put Qx:=H(i_0(x),i_1(x)), again interpreted through the coding graphs. Whenever H realizes K_X, Q realizes X. Thus Q is universal. ∎

The same coding shows that EU_e supplies joint arbitrary variation of any fixed finite list of finite-arity relations on individuals: inject the finitely tagged tuples into e, combine target relations into one rigid unary target, and decode R. This gives an informative alternate formulation of universal profiles.

In ordinary full S5 with an infinite individual set E, the required coding graphs exist by standard infinite-cardinal arithmetic under Choice. The analogous internal theorem from □Functional Choice plus the single Axiom of Infinity at e is now supplied by §10 of `/tmp/classicism-research/structural-world-representation.md`: the least-bad-initial-segment / lexicographic-square proof uses only admitted well-orders, graphs, Frege induction and internal Schroeder–Bernstein. This lane audited that proof. An injection e²→e gives the two disjoint injections by fixing two distinct second coordinates. Thus Theorem 2 yields EU_e iff Universal Involution over □Functional Choice plus the quantified Axiom of Infinity_e. The Infinity schema is not substituted for that axiom. Under those codings, “all rigid unary configurations can occur” and “all reversible rearrangements can occur” are equivalent formulations, not rival strengths.

The infinity/coding condition is essential. Full S5 with |E|=2, |W|=2 realizes both involutions but cannot realize the four unary profiles. Conversely |E|=6, |W|=64 realizes all unary profiles but cannot realize all 76 involutions. The involution counts obey a_n=a_{n-1}+(n-1)a_{n-2}, with a_0=a_1=1, giving 1,1,2,4,10,26,76. These finite models all satisfy □Functional Choice.

### A direct all-type obstruction

The analogous EU_t is inconsistent with T. Given R^{tt}, define the rigid property

    D(p) := W(p) ∧ ¬(p≤Rp).

At any evaluation world, take its true atom a. Atomhood gives a≤Ra iff Ra is true there; hence Da iff ¬Ra. Therefore R cannot be coextensive with D at that world. Actuality holds everywhere, so it cannot be coextensive anywhere. No external cardinality argument is needed.

More generally the same diagonal works at a type σ whenever there is an admitted rigid injective coding of world atoms into σ: diagonalize at the code of the actual world. Consequently a universal-profile schema over all types is not a consistent strengthening; the base-type restriction is substantive.

## 7. External completeness: an exact symmetry boundary

These are semantic/external statements, not proposed object-language definitions.

Suppose an atomic S5 Henkin model has internal Choice and internally infinitely many world atoms, and every external permutation of its world set W lifts to an automorphism of the typed structure. Internal infinite-cardinal arithmetic gives an admitted balanced proposition p with admitted bijections between W and each of p and its complement. Therefore externally |p|=|W\p|=|W|. All external permutations then give every balanced subset of W as an admitted proposition.

Every subset A⊆W is a Boolean combination of balanced subsets (in external ZFC). If both A and its complement have size |W|, A is already balanced. If |A|<|W|, partition W\A into three sets B,C,D each of size |W|; then A=(A∪B)∩(A∪C), an intersection of balanced sets. The remaining case follows by complementation. Hence D_t=P(W) externally.

Both qualifications matter: §4 has all external symmetries but no Choice/balanced split; an externally infinite but internally finite nonstandard world set must not be substituted for internal infinity.

Even full external world symmetry plus □Functional Choice does NOT force external fullness at higher types. Here is a standard elementary-Henkin construction. Start from full S5 with W=N and E singleton, encoded as a countable many-sorted first-order structure with a world sort, all typed sorts, application, logical operations, quantifier operations and world/proposition membership. Let c=2^{aleph_0}; its group of world permutations has size c. Build an elementary substructure of size c containing all W and all P(W), alternately taking elementary hulls of size c and closing under the entire group. The union of the omega-chain is elementary, group-invariant, and still of size c.

It retains W=N and D_t=P(N), and all external world permutations lift. It satisfies every first-order instance of the C, Plenitude and Functional Choice schemata true in the full model. Quantifiers retain their intended semantics: for each retained predicate and each w∈W, elementarity equates universal truth over the full and retained argument domain; since all worlds remain, the returned proposition is exactly the retained-domain intersection. Lambda witnesses similarly remain by elementarity. Function extensionality ensures restriction to retained arguments does not identify distinct retained functions.

But D_{tt} has at most c elements, whereas the set of all maps P(N)→P(N) has cardinality 2^c. Thus the higher hierarchy is externally incomplete. This demonstrates why neither internal completeness nor even maximal symmetry of the external world set should be described as full higher-order powerset semantics.

## 8. Definition audit and status

Recommended alternate definitions, with assumptions explicit:

- Over T, a rigid internally complete Boolean subalgebra can be defined by complement closure and closure under the explicit conjunction of every admitted rigid family. Top, bottom and binary meets are redundant clauses.
- Over T, complete generation by a family R is equivalent to separation of world atoms by its members. The partition E_R gives its exact generated algebra.
- Over the rigid injection hypotheses of §6, universal unary profiles are equivalently universal involutions or universal finite relational configurations. Without those hypotheses these are genuinely different principles.
- The nominal models give a clean semantic interpretation of FinW and countable indexing, but those interpretations depend on the proved standardness lemma and are not blanket identifications in all Henkin models.
- External symmetry/fullness statements are metatheoretic properties of models. They should not be presented as new formulas of C without a separate language/semantics proposal.

All construction and theorem arguments in §§1–7 are supplied here for audit. Their adaptation to this map has not been independently checked by a named human. No Lean status is claimed. The implication “□Functional Choice + Axiom of Infinity_e yields the precise coding graphs” has now been supplied in the companion world-representation report §10 and audited here; see the update in §6. The formal consequences from Choice to splitting and local countable extraction are developed further in §15. None of these updates alters the stated model separations.

## 9. Complete Boolean evaluators, worlds, and contravariant maps

This develops a suggestion from the parent research lane and is compatible with the world-representation lane's ultrafilter formulation. Again “complete” means preservation of every admitted internal family, not every external subset.

For an admitted rigid X^{tt}, let m_X be its Boolean meet. An operation H^{tt} is **internally complete** when H(m_X) is the meet of the admitted image family

    H[X](q) := ∃p(Xp ∧ q=Hp)

for every rigid X. The image family is rigid because X is rigid and identities are rigid under T. Equivalently quantify over all admitted families using rigidification of their actual extensions. Unital Boolean homomorphism means preservation of top, complements and binary meets. Empty-family preservation can replace the separate unital clause if desired.

**Theorem 3 (complete evaluators are worlds).** Over T, the internally complete unital Boolean homomorphisms E:t→t whose ranges lie in {bottom,top} are exactly

    E_a(p) := (a≤p)

for world atoms a. The witnessing atom is unique.

**Proof.** Given E, the property U(p):=(Ep=top) is admitted and rigid. Let a be its meet. Completeness gives Ea=top, since the image family consists solely of top (and includes top). Hence a≠bottom. Bivalence and complement preservation imply that for every p, either Ep=top or E¬p=top. Therefore a≤p or a≤¬p. Since a is nonzero, this is precisely the Boolean-algebra characterization of atomhood.

If Ep=top then a≤p by the definition of a. Conversely if a≤p, monotonicity gives Ea≤Ep, hence Ep=top. Thus E agrees with E_a at every argument, and the equality is justified by BF/NI and modalized functionality in T. If E_a=E_b, evaluation at p=a and p=b gives b≤a and a≤b, so a=b.

Conversely an atom a decides every proposition, so E_a is a bivalent unital Boolean homomorphism. For every admitted family X,

    a≤m_X iff ∀p(Xp → a≤p),

which is exactly meet preservation by E_a. ∎

Thus “complete bivalent logical evaluator” is an equivalent definition of a world over T. Dropping completeness is a genuine weakening, not another equivalent definition.

**Theorem 4 (internal contravariant representation).** Internally complete unital Boolean homomorphisms H:t→t correspond bijectively to internally represented maps f from world atoms to world atoms, by

    a≤Hp iff f(a)≤p,
    Hp = ⋁{a : W(a) ∧ f(a)≤p}.

Represent f as an operation t→t taking nonatoms to bottom; only its values on atoms are substantive.

**Proof.** For each atom a, E_a∘H is a complete bivalent evaluator, so Theorem 3 gives a unique atom f(a). The graph

    W(a)∧W(b)∧∀p(a≤Hp ↔ b≤p)

is admitted and rigid. Add the unique default b=bottom off atoms. Plenitude represents this functional graph by an admitted operation f; no choice among multiple values occurs. The displayed join formula follows because its atom profile is exactly that of Hp, and Atomicity identifies propositions with equal profiles.

Conversely, from an admitted world map f define

    H_f(p) := ∃a (W(a) ∧ a ∧ f(a)≤p).

Actuality and uniqueness of the true world atom imply a≤H_f(p) iff f(a)≤p. Pointwise Boolean identities and the meet universal property then prove that H_f is a complete unital Boolean homomorphism. Equality of profiles gives both inverse laws. ∎

The following strengthen the correspondence and require no Choice:

- H_f is injective iff f is surjective on worlds. Surjectivity makes equality of pulled-back profiles reflect equality; if an atom b is omitted, H_f(b)=H_f(bottom)=bottom.
- H_f is surjective iff f is injective on worlds. Surjectivity separates any distinct a,b by a preimage of proposition a, forcing f(a)≠f(b). Conversely, if f is injective and q is any proposition, let p be the admitted join of {f(a):W(a)∧a≤q}. Then H_f(p)=q. Here atoms are completely prime for admitted joins: E_a preserves those joins by Theorem 3 and complementation.
- H_f∘H_g=H_{g∘f}. Thus the correspondence reverses composition, as inverse-image maps should.
- Complete Boolean automorphisms correspond exactly to internally represented world permutations.

An internal world permutation consequently lifts through the entire type hierarchy by the same conjugation mechanism as the recorded atom-swap proof: use the Boolean automorphism at t, identity substitution at e, and F_τ∘X∘F_σ^{-1} at σ→τ. Complete preservation of admitted meets supplies commutation with the quantifier constants; bijectivity supplies equality preservation. Keep the identity at e as a metalinguistic substitution action, not as a claimed term of the forbidden type ee. The generalization is an algebraic extension of the recorded conjugation proof, not evidence that arbitrary EXTERNAL world permutations are internally represented.

**Why completeness matters.** In the full S5 model W=N, an external free ultrafilter U yields the admitted bivalent Boolean homomorphism E_U(p)=top iff p∈U. It is not E_a for any world atom. It fails completeness on the admitted tail family: all tails evaluate to top, their meet is bottom. This uses the ultrafilter theorem, available in the stipulated ZFC metatheory.

An even more elementary witness occurs in the unordered nominal model: on FinCof(W), map cofinite propositions to top and finite propositions to bottom. This is equivariant and therefore admitted. It is a bivalent Boolean homomorphism, but its value on the meet of all co-singletons is bottom while the meet of their values is top. The family of co-singletons is itself admitted and rigid. Hence internal completeness is already a substantive restriction in a finitely supported Henkin hierarchy.

## 10. Complete normal modal operators are world relations

Use explicit operator laws here. The background's named NKB condition should not silently be replaced by the stronger conjunction of reflexivity, transitivity and symmetry laws. For instance the constant-top operator satisfies normality, K and the usual B inequality but fails T.

Let H:t→t preserve all admitted meets, including the empty meet. No complement preservation is assumed. Define the rigid relation on worlds

    R_H(a,b) := ∀p(a≤Hp → b≤p).

**Theorem 5.** Such H correspond exactly to admitted rigid binary relations R on worlds, by

    a≤H_R(p) iff ∀b(W(b)∧Rab → b≤p).

**Proof.** For an atom a, let s_a be the meet of the admitted rigid family X_a(p):=(a≤Hp). Meet preservation implies a≤H(s_a), since a lies below each H-image of a member of X_a. Monotonicity then gives

    a≤Hp iff s_a≤p.

The forward implication is the meet definition; the reverse uses a≤H(s_a) and s_a≤p. By Atomicity, s_a≤p iff every world below s_a lies below p. Also b≤s_a iff R_H(a,b), by the meet universal property. This proves the displayed relation semantics.

Conversely define H_R by the admitted formula

    H_R(p) := ∀a[(W(a)∧a) → ∀b(W(b)∧Rab → b≤p)].

Actuality supplies the unique true world atom, and the rigidity of R and order tests gives the displayed evaluation rule. Universal quantification over successors preserves every admitted meet, including top. To check the inverse on relations explicitly, the join q of the admitted successor-atom family {b:W(b)∧Rab} is the meet of its upper bounds: it is a lower bound and is itself one of those upper bounds. Thus the reconstructed s_a equals q. Complete primality of atoms for admitted joins gives b≤q iff Rab, so no additional successors appear. Atomicity gives the inverse on operators. ∎

The familiar frame correspondences hold internally; atom complements supply all counterexample valuations:

- T, Hp≤p for every p, iff R is reflexive. For the nontrivial direction a≤Hs_a≤s_a, so Raa.
- 4, Hp≤H(Hp) for every p, iff R is transitive. If Rab and Rbc but not Rac, use p=¬c. It holds at all successors of a, yet Hp fails at b; this refutes 4 at a. Transitivity proves the converse directly.
- B, p≤H(¬H¬p) for every p, iff R is symmetric. If Rab but not Rba, take p=a; B would force a successor of b lying below a, necessarily a itself. Symmetry proves the converse.
- H(bottom)=bottom iff every world has an R-successor.

All inequalities above are algebraic/necessary inequalities, not merely material implications at one chosen evaluation world.

Combining Theorems 1 and 5 gives a three-way correspondence:

    rigid world equivalence relations
        ↔ rigid internally complete Boolean subalgebras
        ↔ internally meet-complete modal operators satisfying T,4,B.

For the partition E, H_E(p) is the greatest member of A_E below p; its fixed points are precisely A_E. Conversely a complete subalgebra A defines H_A(p) as the join of its members below p. This join is an admitted family. The partition theorem identifies H_A with H_{E_A}, proving all the operator laws. In particular □p≤H_Ap≤p and H_AH_Ap=H_Ap.

### Two independent modalities and product worlds

For equivalence relations E,F, the associated modalities commute iff the relations permute under composition. The composite operator represents the composite relation (with the usual reversed order for nested universal modalities). If E∩F is equality on worlds and E∘F is the universal relation, every E-class intersects every F-class in exactly one world. Therefore worlds are canonically the product of the two quotient sets. This is internal and choice-free: the quotient classes are proposition codes from Theorem 1, and the intersection witness is unique, so Plenitude represents reconstruction.

Equivalently the complete subalgebras A_E,A_F jointly generate all propositions, and every nonzero member of one has nonzero meet with every nonzero member of the other. This characterizes genuine independent coordinates, rather than merely two named necessity operators. The product condition is stronger than commutation alone.

## 11. Exact profile spaces have a complete-freeness characterization

For a fixed R^{et}, say that it is an **exact profile family** if every rigid individual property X has exactly one world a satisfying

    ∀x(a≤Rx ↔ Xx).

Thus the same R has both universal profiles and world separation. The existence of possibly different witnesses for the root's EU_e and S_e is not silently identified with a common exact witness: joining those existence claims uses the separate internal Choice/Cantor–Bernstein argument discussed with the parent.

**Theorem 6 (endomorphism extension criterion).** Over T, R is an exact profile family iff every assignment G^{et} extends to a unique internally complete Boolean endomorphism H^{tt} satisfying

    ∀x H(Rx)=Gx.

**Forward.** For each target world a, its G-profile X_a(x):=(a≤Gx) is an admitted rigid property of individuals. Exactness gives a unique source world f(a) with

    f(a)≤Rx iff a≤Gx.

Plenitude represents the unique world assignment. The complete Boolean endomorphism H_f from Theorem 4 then satisfies H_f(Rx)=Gx by equality of world profiles. Any other complete endomorphism K has an associated world map k; the same equality on generators makes k(a) and f(a) have the same R-profile, so exactness gives k=f and K=H_f.

**Reverse: uniqueness gives separation.** If distinct a,b have the same R-profile, their distinct complete evaluators E_a and E_b agree on every Rx. They are two extensions of the same admitted assignment Gx:=(a≤Rx), contradicting uniqueness. Hence R separates worlds.

**Reverse: existence gives all profiles.** For a rigid X, take Gx:=Xx. These are bivalent propositions. Choose any world atom a, available by Atomicity at top. An extension H exists. The composite E_a∘H is a complete bivalent evaluator, hence E_b for some world b by Theorem 3. For each x,

    b≤Rx iff E_b(Rx)=top iff E_a(Gx)=top iff Xx.

Thus b realizes X; separation gives uniqueness. ∎

This is an exact alternate definition, not a merely suggestive analogy: an individual-indexed family is a full configuration basis iff arbitrary reassignments of its basic propositions extend uniquely to complete Boolean endomorphisms.

There is also a genuine relative free-object property. For any admitted relational type τ, its Boolean algebra is internally complete and atomic under T. Given an admitted assignment G:e→τ, each target atom b determines the rigid individual profile x↦(b≤_τGx), hence a unique source world f(b). The operation

    H(p) := ⋁{b : Atom_τ(b) ∧ f(b)≤p}

is represented by Plenitude after unique internal joins, is a complete Boolean homomorphism t→τ, and uniquely extends the assignment on the R-generators. The proof is Theorem 4 with different source/target atomic algebras. This justifies the description **free internally complete atomic Boolean algebra on the individuals**. The word ATOMIC is essential for infinite generator sets: P(2^E) is then not in general a free object among arbitrary complete Boolean algebras. In an atomless target, the meets specifying all complete truth assignments can all vanish, preventing the required complete extension. For finitely many generators, finite Boolean distributivity gives the ordinary free finite Boolean algebra, so this particular objection does not arise.

### Coherent independent flips

An exact R-profile family gives more than unstructured transitivity of worlds. For each rigid individual property X, assign

    G_X(x) := (Xx∧¬Rx) ∨ (¬Xx∧Rx).

Theorem 6 gives a unique complete endomorphism H_X. Applying it twice fixes each generator, so uniqueness gives H_X²=id. Thus H_X is an automorphism. The same generator calculation gives

    H_X∘H_Y = H_{X xor Y}.

The induced world permutations form a coherent commuting group of involutions. Given worlds a,b, the rigid difference profile X_{a,b}(x):=(a≤Rx) xor (b≤Rx) induces the unique coordinate flip carrying a to b. The action of rigid subsets of individuals under symmetric difference is free and transitive on worlds.

This supplies an additional precise interpretation of exact configuration space: worlds form a torsor for the Boolean group of rigid individual subsets, with each subset flipping exactly its own coordinates. It does not follow merely from the existence of a universal profile family with arbitrary fibre sizes; unequal fibre sizes can obstruct profile-flipping automorphisms.

## 12. Modal-scope guardrail for the proposed principles

T already proves No Pure Contingency. Therefore each fully closed pure instance of ISplit, countable disjointness, EU_e, S_e, Universal Involution, or existence of an exact profile family is equivalent over T to its boxed instance. This uses the recorded No Pure Contingency schema, whose side condition is purity relative to C. It is NOT unrestricted necessitation of an optional assumption. A formula retaining a named R, H, X, a nonlogical signature constant, or another parameter does not acquire this conclusion merely from being displayed in the report; prove rigidity or close it appropriately.

## 13. Orbit criteria and a sharper countable separation

In the general nominal construction of §2, the following are exact external criteria. They are proved using the standard internal natural numbers established in §3, not assumed for arbitrary Henkin models.

1. An admitted countable sequence of disjoint nonzero propositions exists iff some finite point stabilizer G_(S) has infinitely many orbits on W.
2. An admitted sequence of infinitely many distinct world atoms exists iff some G_(S) has infinitely many fixed points on W.

For the forward direction of 1, a finitely supported sequence has all its values invariant under one G_(S), since every numeral is fixed by G. Each nonempty disjoint value contains at least one distinct orbit, so there must be infinitely many orbits. Conversely choose countably many distinct orbits O_n (external ZFC is the metatheory). Each O_n is supported by S; the operation taking c_n to O_n and nonnumerals to bottom is itself supported by S, since the numerals are individually fixed. Hence it is admitted.

For 2, each atom in a sequence supported by S must itself be fixed by G_(S); this says exactly that its unique world is fixed. Conversely a countable sequence of distinct fixed points yields an admitted atom sequence by the same numeral-indexed definition. These criteria distinguish infinitely many distinguishable blocks from selecting a point in every block.

**Pair-flip model.** Let W=N×{0,1}, and let G be the direct product of independent flips of each pair P_n={n}×{0,1}. Use finite point supports as before. A proposition is admitted iff it splits only finitely many pairs; on all other pairs it may independently include the whole pair or omit it. Arbitrary unions of whole pairs have empty support.

This model satisfies T. ISplit holds: an infinite admitted p contains infinitely many whole pairs, apart from finitely many exceptions, and the corresponding infinite subset of N splits into two infinite subsets. The unions of those pair subfamilies give an admitted split of p. There is an admitted countable disjoint sequence n↦P_n. But every finite point stabilizer fixes only the points in the finitely many pairs meeting its support. By criterion 2 there is no internal infinite sequence of distinct world atoms, even though the external world set is countable.

Intensional Choice fails: at world (n,i), let F allow the two atoms of P_{n+1}. This equivariant F is necessarily instantiated. A selector supported by finite S would, for sufficiently large n, be fixed by the flip of P_{n+1}, which fixes both S and the input world but interchanges the allowed outputs. This contradicts uniqueness.

If one wants the disjoint possibilities themselves infinite, replace each pair by a rationally ordered block and take the product of its order-automorphism groups, with the blocks labeled by N. The block propositions form an admitted disjoint sequence of infinite possibilities. ISplit holds by splitting an interval in a block (or splitting infinitely many whole blocks). Finite point stabilizers still have only finitely many fixed world points, so there is no infinite atom sequence. The same greater-point argument as §5 refutes Intensional Choice.

These are robust refinements of the hierarchy: repeated splitting, countably many disjoint possibilities, countably many disjoint INFINITE possibilities, and choosing a countable sequence of world atoms must not be conflated in the absence of full Choice.

**A useful special boundary.** In the §2 hierarchy with singleton individuals, an admitted enumeration of all worlds implies that a finite point stabilizer acts trivially on W. It then acts trivially on the recursively generated full typed universe, so every function at every type has that finite support; the nominal hierarchy is externally full. This observation is specific to this construction, not a general theorem about Henkin models. It also shows why an externally countable nominal world set need not have an internal enumeration.

### A world-separating generator family without external fullness

The construction allows any nominal base D_e all of whose members have finite support, instead of the singleton; the closure and Plenitude proofs are unchanged. In the unordered case take D_e=W with its natural permutation action. The relation R^{et} given by Rx={x} is equivariant and separates worlds. Hence the individual-indexed singleton family internally completely generates D_t, by §1. Nevertheless D_t remains FinCof(W), not P(W), and ISplit still fails. This is a concrete warning against reading “complete generation” as generation under all external joins. The proof of □Intensional Choice in §4 still works for this base, since it used only finite support of each chosen witness.

## 14. Full configuration semantics versus a proper Henkin configuration space

In full standard set-based S5 semantics (equivalently the relevant full world-indexed/Gallin-style presentation), choose an individual set E and worlds W=P(E). Set

    R(n) = {w⊆E : n∈w}.

Every rigid individual subset is a subset of E, so R has every profile at exactly one world. The proposition algebra is P(P(E)). Its complete-atomic freeness is completely explicit: an assignment G:E→P(V), for any target world set V, induces the map

    f(v) = {x∈E:v∈Gx} ∈ P(E),

and the unique complete Boolean homomorphism P(P(E))→P(V) extending the assignment is inverse image under f. This is the external full-semantics version of Theorem 6. It uses a full target powerset; the internal theorem quantifies only over admitted assignments and families.

There is a particularly sharp proper Henkin example showing that the internal freeness axiom does NOT smuggle in full powerset semantics, even in the presence of □Functional Choice and genuine Infinity.

Start with this full model at E=N and W=P(N). Regard it as a many-sorted first-order semantic structure with the world sort, all admitted typed sorts, application, logical/quantifier operations, and world/proposition membership. Take a countable elementary substructure containing R and every individual n. The language has countably many types and comprehension/lambda instances; the chosen seed is countable. If desired also include a rigid enumeration graph connecting the standard Frege numerals to the individuals, and their standard order, as additional countably many seed elements. No forbidden operation type with output e is needed: use a relational graph.

The retained individual sort is still exactly N. The retained world sort W' is a countable family of subsets of N. Retained propositions can be restricted to W': their restrictions remain distinct, because the first-order extensionality assertion that distinct propositions differ at some world is preserved by elementarity. Similarly retained function objects remain distinct on retained arguments by functional extensionality, and their values stay in retained sorts by closure.

For a retained predicate F and retained world w, the truth of ∀x F(x) in the full structure agrees, by elementarity, with its truth over the retained argument domain. Thus quantifier operations calculate the intended intersections after restriction. Comprehension/lambda witnesses and all instances of □Functional Choice remain by elementarity. The original Axiom of Infinity_e remains true, and Frege natural numberhood is standard: the source model has exactly the standard numeral objects, all retained as pure terms, and elementarity excludes any additional natural-number objects.

The exactness formula for R is first-order in this many-sorted encoding, so R remains exact. Its profiles identify W' with the retained rigid individual-subset domain. Each retained world has its unique rigid profile, and every retained rigid profile has its unique world, by elementary transfer of those existential uniqueness assertions. Both collections are countable proper subfamilies of the external P(N).

The retained proposition domain is countable as well, while P(W') is uncountable: W' is infinite since it includes the profiles of infinitely many distinct finite individual subsets. Hence the proposition algebra is externally incomplete. Nonetheless it is internally complete and atomic, satisfies □Functional Choice, and has the unique complete-endomorphism extension property of Theorem 6.

This example sharply separates three claims:

1. an internal exact configuration space, proved equivalent to complete freeness;
2. external representation of each retained proposition as a set of retained worlds;
3. external fullness, admitting every subset of those worlds and every external assignment of generators.

The example has 1 and 2 but not 3. Accordingly neither the internal universal property nor “worlds are all admitted individual profiles” should be paraphrased as W=P(E) externally. The full Gallin-style construction is a particularly transparent model witnessing consistency, not a hidden semantic restriction on the theorem.

## 15. What full Choice settles in the splitting hierarchy

The companion report `/tmp/classicism-research/structural-world-representation.md`, §10, now supplies the internal infinite-square theorem from Choice. Its proof is for any represented infinite well-ordered field, not essentially for the entire individual sort: take a least bad initial segment, rule out its greatest point, and compare it with its square ordered by (max(a,b),a,b). Every proper initial segment of the square is too small to receive the alleged least bad field. All uses of finiteness are the Frege induction lemmas proved there. This lane audited the argument.

Consequently □Functional Choice proves ISplit. Given InfW(p), the represented rigid world subset W_p is infinite and can be well-ordered. The infinite-square theorem and two distinct members give an injection W_p×{0,1} into W_p; the reverse injection and internal Schroeder–Bernstein give a bijection. Its two ranges are admitted infinite subsets partitioning W_p. Their admitted joins are propositions q and p∧¬q, each with infinitely many world atoms. No external choice of a subset missing from the hierarchy is made.

There is also local countable world extraction under □Functional Choice: every InfW(p) has an admitted operation n↦a_n from the internal Frege naturals at type t to distinct world atoms below p. Well-order W_p. Define the relation between n and a by saying that a's predecessor set in this order has cardinality n. The least world witnesses n=0. If a witnesses n, there must be a least world above a: otherwise W_p would be the finite predecessor set together with a. That next world witnesses Suc(n). Frege induction gives existence for all internal n. Uniqueness follows from the finite-cardinality fact that a proper initial segment of a finite set cannot have the same finite cardinality as the whole; the predecessor sets of distinct worlds are properly nested. Thus the graph is functional, and Plenitude supplies the operation. The finite-cardinality fact is proved by the same successor-removal induction as the companion report's hereditary-finiteness lemmas; it does not assume all internal naturals externally standard.

The resulting singleton possibilities form a countable disjoint sequence below p. This is stronger than the local/global splitting fragments separated by the nominal models. It does not enumerate all worlds of p unless that world subset is internally countable. Full S5 with uncountably many worlds remains a countermodel to universal world enumeration, even though □Functional Choice holds.

Thus the nominal separations rigorously illustrate what full Choice adds, while the universal-profile, separation, exact-configuration and complete-freeness principles supply further independent structural content beyond Choice itself.

## 16. Boolean retractions give an algebraic formulation of full Choice

This section develops the parent's retraction suggestion and separates its propositional and all-type strengths.

For a rigid internally complete Boolean subalgebra predicate A of the relational Boolean algebra B_τ, define a **complete Boolean retraction onto A** to be an admitted complete unital Boolean homomorphism H:τ→τ satisfying

    ∀p A(Hp),
    ∀q(Aq → Hq=q).

These two clauses already imply that its range is exactly A and H²=H; separate range-surjectivity and idempotence clauses are redundant. All types here are admitted because τ is relational.

The partition and complete-homomorphism correspondences generalize from propositions to every B_τ. Their proofs use only atomic Boolean algebra, admitted meets/joins, rigid graph predicates and Plenitude. A target atom b evaluates q by the bivalent proposition b≤_τq. A complete Boolean homomorphism B_τ→B_τ is therefore inverse image under an admitted map of its atoms, with joins replacing the literal existential proposition formula used at type t.

**Lemma 16.1.** A complete subalgebra A_E associated with an admitted equivalence E on the atoms of B_τ has a complete Boolean retraction iff E has an admitted transversal.

Given a transversal, let c send each atom to the unique selected atom in its E-class. Plenitude represents c. It is constant on E-classes and satisfies c(a)Ea. Its inverse-image Boolean homomorphism H_c has E-invariant values, and fixes every E-invariant element. Hence it retracts onto A_E.

Conversely let H be a retraction and f its atom map. Since every Hp lies in A_E, if aEb then a≤Hp iff b≤Hp for every p, so f(a)≤p iff f(b)≤p for every p. Evaluating at p=f(a),f(b) gives f(a)=f(b). Since H fixes A_E, a and f(a) agree on every A_E-element, hence aEf(a) by the partition correspondence. Thus f is constant on each E-class and returns a member of it. The admitted rigid predicate f(a)=a selects exactly one atom per class. ∎

**Theorem 16.2.** Over T, □Functional Choice is equivalent to the schema asserting that every rigid internally complete Boolean subalgebra of every relational-type Boolean algebra has a complete Boolean retraction.

**Choice implies retractions.** Boxed Functional Choice supplies Relational Choice and, with the rigid comprehension already in T, Transversal Choice. Apply it to the equivalence on atoms corresponding to A. Extend that equivalence to the entire type by making nonatoms singleton classes if necessary. Restrict its transversal to atoms and use Lemma 16.1.

**Retractions imply Choice.** Let S be an arbitrary equivalence relation on a type σ, including e. Rigidify its actual extension, which preserves equivalence in the constant-identity setting of T. Choose a world atom a. The map

    j(x) := λy^σ (a ∧ y=x)

injects D_σ into the atoms of B_{σt}; this is the world/tuple atom normal form proved in the companion world-representation report. Define an equivalence E on those atoms by

    E(U,V) := U=V ∨ ∃x y(U=j(x) ∧ V=j(y) ∧ Sxy).

On the j-image its classes are the S-classes, and every other atom is a singleton. This is admitted and rigid. Its associated complete subalgebra of B_{σt} retracts by hypothesis. Lemma 16.1 supplies an atom transversal C. Pull it back along j: F(x):=C(j(x)). This selects exactly one member of each S-class. Therefore Transversal Choice holds at every σ.

The recorded implications give Relational Choice; T already supplies Plenitude, so Functional Choice follows. Each fully closed Functional Choice instance is pure, and No Pure Contingency in T gives its boxed form. Thus no illicit necessitation of a hypothesis is used. ∎

This is an exact algebraic alternate definition of full Choice over boxed Plenitude: **all internally complete Boolean inclusions split**, interpreted at every relational type. It is not just a metaphor drawn from ordinary external powersets.

The converse uses only the instances Ret_{σt}, one for each type σ; arbitrary relational-algebra shapes are unnecessary for that direction. The phrase “all complete inclusions split” must range over internally represented complete subalgebra fields A⊆B_τ. Restricting it to inclusions between entire type algebras B_ρ→B_τ is not automatically the same schema, and no such restriction is claimed equivalent here.

### Why the all-type scope is essential

At type t alone, the retraction principle expresses only Transversal Choice for equivalence relations on WORLDS. It is strictly weaker than full Choice.

In the unordered nominal model of §4, let an admitted rigid equivalence E on W have finite support S. On O=W\S, invariance under every permutation of O makes E either equality or the universal relation: the diagonal and the off-diagonal are the only orbits on O².

If E is equality on O, no point of O can be equivalent to a point of S; otherwise invariance and transitivity would merge all of O. All O-points are singleton classes, and the remaining finitely many classes are inside S. Choose representatives there; together with O they form an admitted cofinite transversal.

If E is universal on O, there is one large class containing O and possibly some points of S, with all other classes inside S. Choose one point of the large class and representatives for the finitely many other classes. This finite transversal is admitted. Thus every world equivalence has a transversal, and every propositional complete subalgebra retracts. Yet Relational Choice fails by §4. This model also satisfies □Intensional Choice.

In the pair-flip model of §13, the partition into the pairs P_n has no admitted transversal. Its complete subalgebra consists of propositions that are unions of whole pairs. Hence that propositional subalgebra does not admit a complete Boolean retraction. The obstruction is not Boolean incompleteness: the subalgebra is internally complete; selecting one atom from each of its relative atoms is the missing choice.

## 17. The .2 law is confluence, with no reflexivity assumption

For a complete normal meet-preserving H as in Theorem 5, write Dp:=¬H¬p. Then

    D(Hp) ≤ H(Dp) for every p

holds iff its represented world relation R has directed successor cones:

    ∀a b c[(Rab∧Rac) → ∃d(Rbd∧Rcd)].

**Confluence implies .2.** If a has a successor b where Hp holds, and c is any successor of a, choose a common successor d of b,c. Since Hp holds at b, p holds at d; hence Dp holds at c. Since c was arbitrary, HDp holds at a.

**.2 implies confluence.** Suppose Rab and Rac but there is no common successor. Let p be the admitted join of the R-successors of b, the cone s_b from §10. Every successor of b lies below p, so b≤Hp, and therefore a≤DHp. No successor of c lies below p: if one did, complete primality for the admitted successor-atom join would make it also a successor of b. Hence c≤¬Dp, so a is not below HDp. This contradicts .2. The case b=c is included; a reachable dead end is correctly detected as a failure of confluence. No reflexivity assumption was used.

The mixing-models sibling lane independently audited the complete-operator representation and this .2 argument. That is a research cross-check, not a named-human `checked_by` claim or a Lean certification.

## 18. Retraction refinements and the direction of Choice

The mixing-models lane supplied a stronger countermodel to propositional retractions. Let W=J×{0,1} for infinite J, and let G be the full wreath product of independent pair flips with all permutations of the pairs. Use supports closed under the mate involution. D_t remains FinCof(W), because a finite stabilizer is transitive outside finitely many supported pairs. The pairing equivalence, unlike in the full Sym(W) construction, is now admitted with empty support.

Intensional Choice nevertheless holds. In the generic transport proof of §4, choose u in a pair disjoint from the support S of F; close both S and a witness support under mate, and remove the whole pair of u to form T. The point stabilizer of u automatically fixes its mate. Thus two permutations fixing T and taking u to the same fresh world act identically on the witness, making generic transport well-defined. The complement of T is one orbit, and finitely many exceptional worlds are handled by finitely many witnesses as before. This proves the all-type boxed Intensional Choice principle. But flipping a fresh pair defeats any finitely supported transversal of the pairing. The complete pair-union subalgebra therefore has no retraction. This construction was independently audited in this lane.

In the opposite direction, every propositional complete subalgebra DOES retract in the ordered nominal model of §5. For an equivalence E with finite support S, the stabilizer acts independently and order-homogeneously on the finitely many open intervals cut out by S. On each interval, symmetry of E and transitivity of the automorphism action on increasing pairs force E to be either equality or universal. If it is equality there, no point can relate to a point outside the interval: moving the former while fixing the latter would collapse the interval. Thus discrete interval points form singleton classes; all other classes are unions of members of a finite list of interval/point orbits. A transversal is the union of the discrete intervals plus finitely many representatives of the remaining classes. It is admitted. By §16 every propositional complete subalgebra retracts, while Intensional Choice fails by §5.

Hence propositional retraction and Intensional Choice are incomparable over T. The all-type retraction schema remains equivalent to full Choice.

Finally, the word “inclusion” in the algebraic Choice formulation is essential. Complete Boolean SURJECTIONS between nontrivial internally complete atomic Boolean algebras already split without Choice. Their dual atom maps are injective. An admitted injection f:V→W has an admitted left inverse g:W→V: invert it on its image, and send other points to one fixed default member of V. Unique-value comprehension/Plenitude suffices. Taking inverse images produces a complete Boolean right inverse of the original surjection.

By contrast a complete Boolean injection has a surjective dual atom map. A Boolean left inverse requires a section of that atom surjection, selecting one atom from every fiber. The all-type assertion that these inclusions split is precisely the Choice content proved in §16, not a statement about splitting Boolean surjections.


## 19. A simpler logical definition of complete Boolean maps

Over T, a represented map H:t→t is a complete unital Boolean homomorphism exactly when it satisfies just the following two clauses:

    H(¬p)=¬H(p),
    H(∀p Fp)=∀p H(Fp)              for every F^{tt}.

Thus a complete Boolean evaluator can equivalently be defined as a bivalent operation commuting with negation and propositional universal quantification. This is a simplification of a definition, not an additional axiom, and uses only existing C syntax. Quantifier commutation is equality of propositions, not merely their actual coextension.

**Proof.** Suppose the two clauses hold. Taking F to be the identity gives H⊥=∀p Hp≤H⊤=¬H⊥; hence H⊥=⊥ and H⊤=⊤. For arbitrary p,q, a λ-defined F taking value p at ⊤ and q elsewhere has meet p∧q: ⊤≠⊥ supplies both cases, and proposition identity is rigid in T. Quantifier commutation therefore gives preservation of binary meets, and negation gives the remaining finite Boolean operations.

For a rigid admitted family X, its meet is ∀p(Xp→p). Since Xp is either ⊤ or ⊥, H(Xp→p) equals Xp→Hp. Consequently quantifier commutation gives

    H(meet X)=∀p(Xp→Hp)=meet H[X].

The image family is admitted by λq∃p(Xp∧q=Hp). This is exactly admitted-family completeness. Conversely, the range family λq∃p(q=Fp) is admitted and rigid, and its meet is ∀p Fp. Complete-meet preservation gives the quantifier clause; the negation clause is part of Boolean homomorphism. The same range-family proof shows that such H commutes with every admitted indexed conjunction ∀x^σ Gx, at every type σ. ∎

For general B_τ, replace propositional conjunctions by their pointwise versions. The proof is identical. In particular the complete-retraction schema in §16 can be stated as the existence of retractions respecting negation and all represented indexed conjunctions; no separate list of Boolean operations is needed.

## 20. Finite-operation retractions select ultrafilters, not necessarily atoms

Here a **finite Boolean retraction** preserves ⊤, complement and binary meet, has range in the internally complete subalgebra A, and fixes A pointwise. “Finite” describes the preserved operations; A itself still satisfies the internally complete-subalgebra definition in §1. No assertion below concerns arbitrary incomplete subalgebras.

Let C be the rigid admitted family of relative atoms of A. For c∈C, its block is the family of ambient atoms below c. The following is an exact internal characterization over T.

**Theorem 20.1.** A admits a finite Boolean retraction iff there is a uniformly represented family (U_c)_{c∈C} such that each U_c is an ordinary Boolean ultrafilter on the ambient algebra B_τ and c∈U_c.

**Proof from a retraction.** Put U_c(p) iff c≤Hp. Because Hp belongs to A and c is an A-atom, precisely one of c≤Hp and c≤H¬p holds. Preservation of the finite operations gives the filter and ultrafilter laws. Since Hc=c, the filter contains c. The graph is represented and rigid, being defined by an order test on represented values.

**Proof to a retraction.** Given the uniformly represented U-family, define

    Hp := join{c∈C : U_c(p)}.

This is an admitted join. Complete primality of ambient atoms, or the A-atom decomposition, gives c≤Hp iff U_c(p). Thus the ultrafilter laws establish H⊤=⊤, H¬p=¬Hp and H(p∧q)=Hp∧Hq. The range lies in A. If q∈A, each relative atom c is below either q or ¬q. Since c∈U_c, this gives U_c(q) iff c≤q; hence Hq=q. Unique-value comprehension represents H. ∎

A relative formulation is equivalent: U_c can be an ultrafilter on the relative algebra B_τ↓c, using p↦p∧c to pass between the forms. Theorem 20.1 does not identify U_c with an atom. Exactly that extra conclusion follows when U_c is closed under all admitted meets; its meet then belongs to U_c and is a nonzero ambient atom, as in §9. Therefore finite retraction becomes complete retraction exactly when the selected block ultrafilters are internally complete.

If every block is internally Frege-finite, finite retractions do select actual atoms. An ultrafilter containing a finite join of atoms contains one summand, by finite Boolean primeness and Frege induction. It cannot contain two distinct atoms. The unique selected atom is uniformly definable from U_c. Thus all-type finite retractions imply choice for internally finite nonempty families, while the complete schema supplies unrestricted Functional Choice. This distinction is not based on external versus internal finiteness: the induction is internal.

### BPI is sufficient in full-in-a-model semantics; a converse is not claimed

In ZF plus the Boolean Prime Ideal Theorem, every set-indexed family of nonempty sets (X_i) admits a simultaneous family of ultrafilters, one on each P(X_i). Here is a direct compactness proof. Use propositional variables v_{i,A} for i∈I and A⊆X_i. Impose the Boolean equations v_{i,X_i}=1, v_{i,∅}=0, v_{i,X_i\A}=¬v_{i,A}, and v_{i,A∩B}=v_{i,A}∧v_{i,B}. Every finite part is satisfiable: it involves only finitely many indices, and ZF proves finite choice of one point in each of those X_i, giving principal truth assignments. The Boolean algebra of finite propositional formulas modulo the imposed relations is nontrivial; BPI supplies a prime ideal, and its quotient truth assignment satisfies all equations. Collect its positive A-values into U_i. This produces the entire family at once, without invoking Choice to choose the ultrafilters separately.

Apply this to the blocks of any complete subalgebra of a full powerset algebra. Theorem 20.1 supplies a finite Boolean retraction. Consequently, in a model M of ZF+BPI, take a one-world relational Henkin hierarchy whose domains are the full function/powerset domains **as calculated in M**. Every all-type finite-retraction instance holds. Boxed Plenitude and all-type Intensional Choice hold: there is only one world, and unique-value functions are available in M. Atomicity is supplied by singleton tuples. These are full Gallin-style domains relative to M, and need not be externally full domains in a larger metatheory.

If M fails AC, choose in M a nonempty family (X_i) with no choice function, and take the individual domain large enough to contain disjoint tagged copies of I, ⋃_i X_i and ω. The membership relation, with a default value on the other individual inputs, is serial and admits no represented choice function. Thus Functional Choice fails, while quantified AxiomInfinity_e holds. This gives the relative-consistency separation

    T + all-type Intensional Choice + all-type finite Boolean retractions
      + AxiomInfinity_e + ¬Functional Choice.

The needed consistency of ZF+BPI+¬AC is established in the literature: Miroslav Repický, “A proof of the independence of the Axiom of Choice from the Boolean Prime Ideal Theorem”, Commentationes Mathematicae Universitatis Carolinae 56 (2015), 543–546, presents such a model and cites the original Halpern–Lévy result. [Publisher-library record and article](https://dml.cz/handle/10338.dmlcz/144758). This source supports the set-theoretic consistency input; the typed retraction interpretation above is the present argument.

No converse from the finite-retraction schema to BPI has been proved here. The exact established principle is uniform ultrafilter selection on the admitted partition blocks. Ordinary BPI is a sufficient external set-theoretic assumption; identifying the exact weakest set-theoretic choice principle would require an additional argument. In particular, one must not replace “ultrafilter” by “principal ultrafilter” or claim the finite-operation retraction schema equivalent to full Choice.


## 21. The canonical configuration algebra already exists as a rigid field

This makes the free-algebra account of §11 more precise without asserting external powerset fullness. Fix any original type σ. Let P_σ be the rigid field of rigid properties Y^{σt}. Define C_σ to be the field of rigid predicates A^{(σt)t} that vanish off P_σ:

    C_σ(A) iff Rigid(A) and forall Y(AY -> Rigid(Y)).

Its top is the field P_σ itself, its bottom is empty, and complementation is relative to P_σ. Thus this is a represented Boolean algebra field, not literally a unital subalgebra of the entire ambient B_{(σt)t}. That distinction prevents a hidden mismatch of top elements.

C_σ is internally complete: an admitted family of its elements has the pointwise relative meet

    lambda Y [Rigid(Y) and forall A(UA -> AY)],

after rigidifying U when necessary. BF gives rigidity, and λ-comprehension gives admission. Its atoms are the rigid singleton predicates h_Y(Z):=(Z=Y), for Y∈P_σ. Every nonzero A contains such a singleton, and every A is the admitted join of the singleton predicates h_Y with AY. Define the coordinate generators

    g_x(Y) := Rigid(Y) and Yx.

All these are C_σ-elements, and x↦g_x is represented.

**Theorem 21.1.** Over T alone, C_σ is the internally free complete atomic Boolean algebra on the index field D_σ: every represented assignment x↦Gx into any internally complete atomic Boolean algebra B given by a rigid admitted field, order and operations on a relational carrier extends to a unique represented complete Boolean homomorphism C_σ→B. Targets on an individual carrier can instead be handled by functional-graph notation; no forbidden C arrow returning e is asserted.

**Existence.** For an atom b of B, form the rigid profile Y_b(x):=(b≤Gx). Define

    H(A) := join{b : Atom_B(b) and A(Y_b)}.

All displayed predicates and joins are admitted; unique-value comprehension represents H. Evaluation at b gives b≤H(A) iff A(Y_b). This proves preservation of all admitted meets and Boolean complements, as well as H(g_x)=Gx. The target's atomicity makes equality at all atoms equality of algebra elements.

**Uniqueness.** The singleton h_Y is the admitted meet of the literals g_x for Yx and ¬g_x for ¬Yx. Indeed a rigid property Z has exactly that literal profile iff it is coextensive with Y, hence identical to Y in T. Every A is an admitted join of these h_Y. A complete homomorphism is therefore determined by its generator values. No Choice is used. ∎

This target statement is about internally complete ATOMIC Boolean algebras represented by admitted fields and operations. It is not a claim of a free object among all complete Boolean algebras, nor that C_σ contains every external subset of the external profile set P_σ.

### EU and separation are injectivity and surjectivity of one canonical map

For a candidate relation R^{σt}, Theorem 21.1 yields a canonical complete Boolean homomorphism

    Φ_R:C_σ→B_t,       Φ_R(g_x)=Rx.

Its dual atom map sends a world a to its rigid R-profile Y_a(x):=(a≤Rx). Hence, for this same fixed witness R,

    EU_σ(R)  iff Φ_R is injective,
    S_σ(R)   iff Φ_R is surjective,
    exact configuration(R) iff Φ_R is an isomorphism.

These directions follow from the general complete-map duality of §9. More directly, EU says every profile singleton h_Y has a nonzero image, which detects injectivity by atomicity. Separation says every world profile fiber is a singleton, so every proposition is the inverse image of the admitted profile predicate lambda Y exists a(Atom(a) and Y=Y_a and a≤p), which proves surjectivity.

The range of Φ_R is exactly the internally complete subalgebra generated by the Rx. It consists of the propositions constant on equal-profile classes, as in §1. Thus EU does not posit the abstract existence of a configuration algebra: that algebra is already available as a rigid higher-type field in T. EU asserts that it embeds in the world algebra through the chosen coordinates; separation asserts that the same map covers the world algebra; exactness identifies the two. For E=N and a full Gallin model, C_e is the ordinary P(P(N)); in proper Henkin models both profile and subset fields may be proper.

If existential EU_σ and existential S_σ have different witnesses, the last equivalence does not by itself combine them. The fixed-witness equivalences above use no Choice. Combining independent cardinal bounds into a common exact-coordinate witness requires the additional internal embedding/Schroeder–Bernstein argument supplied elsewhere under Functional Choice.


## 22. EU and separation need not have a common exact witness without Choice

This answers a further independence question left open by the fixed-witness equivalences in §21. The construction uses the full finite-support Henkin hierarchy of §2, but its worlds and individuals are different nominal sets.

Let E=Q with its usual dense order, and let G=Aut(Q,<). Let U be the set of all finitely supported subsets of Q under this action. Such a subset is exactly a union of some of the finitely many open intervals and singleton points cut out by a finite rational set. Let

    W := U minus {empty, Q}.

Use W as the S5 world set, with its inherited G-action, and E as the individual set. Supports here are finite subsets of the rational atom base Q, not finite sets of worlds. At every relational type take all finitely supported functions under the simultaneous action, as in §2. Every world has finite Q-support. Hence the same equivariance proof gives all C λ/quantifier closure; singleton world-and-tuple supports give Atomicity; freezing a functional graph at a world supplies Plenitude. Thus T holds. The argument identifying the Frege numerals with the standard finite cardinals still applies, so quantified AxiomInfinity_e also holds.

Rigid individual properties in this model are exactly the members of U. For Y∈U, the associated rigid property has value W at x∈Y and empty elsewhere. Conversely the extension of a rigid individual property is a finitely supported subset of Q. This correspondence is equivariant.

### The separating witness

Define S^{et} by

    Sx is true at w iff x∈w.

This membership relation is equivariant with empty support, hence admitted. Different worlds are different Q-subsets, so S separates worlds. Thus S_e holds.

### A different witness realizing every profile

For nonconstant w∈U, let a(w) be its leftmost essential endpoint. Concretely, use the least finite set of points cutting Q into intervals and singletons on each of which w is constant. This set is nonempty because w is nonconstant; an endpoint is essential precisely when deleting it would merge cells with different membership values. The leftmost endpoint and the immediately-right membership value are intrinsic and order-equivariant.

Define f(w) by leaving w unchanged strictly to the right of a(w), and assigning to all points at or to its left the membership value of w immediately to its right. This erases the first endpoint, produces an element of U, and is G-equivariant.

The map f:W→U is surjective. Given Y∈U, choose a rational a left of all its essential endpoints (any a if Y is constant). Let c be the constant value of Y on the initial interval. Define w to agree with Y above a and to take value 1−c at and below a. Then a is the leftmost essential endpoint of w, w is nonconstant, and f(w)=Y. This proof chooses one auxiliary point for a single desired Y; it does not produce or require an admitted uniform section.

Define R^{et} by

    Rx is true at w iff x∈f(w).

Equivariance makes R admitted with empty support. Surjectivity of f says that every rigid individual profile occurs at some world. Hence EU_e holds.

### Why no relation can realize every profile exactly once

Suppose a relation V^{et} were exact. Its profile map

    k_V:W→U,       k_V(w)={x:Vx is true at w}

would be a bijection. If the finite set S supports V, it supports k_V: for every g fixing S, k_V(gw)=g(k_V(w)). The profile belongs to U because S together with a finite support of w supports its extension.

Now G_S has exactly 2|S|+1 orbits on Q, namely the singleton points in S and the open intervals between them. Therefore its fixed subsets of Q form a finite set of size

    |U^{G_S}| = 2^(2|S|+1).

The G_S-fixed worlds are those same subsets with the two constants removed:

    |W^{G_S}| = 2^(2|S|+1) − 2.

An equivariant bijection must induce a bijection between fixed-point sets: the forward implication is equivariance, and the reverse follows by applying injectivity to k_V(gw)=g(k_V(w)). The two finite cardinalities differ, a contradiction.

Consequently this full Henkin construction satisfies

    T + AxiomInfinity_e + EU_e + S_e + no exact-coordinate witness.

In particular it fails □Functional Choice, since that principle combines the two profile cardinal bounds by the section and Schroeder–Bernstein argument. The present nonexistence proof is direct and does not use that implication as a premise. This is an internal choice obstruction despite the externally countable world and profile sets; an external bijection exists in the ambient ZFC metatheory but none has finite support.

The example concerns existential EU and existential separation with potentially different witnesses. It does not weaken the elementary theorem that the same R satisfying both is already exact. It also respects the powerset-profile restriction: U is precisely the admitted rigid individual-property field, not an arbitrary replacement set. Thus a generic set-theoretic failure of a dual Cantor–Bernstein principle was not silently assumed.


### Stronger calibration of the endpoint-world countermodel

The finite-retraction construction in the companion mixing-model report §§17–18 applies unchanged to this W. Its least-support lemma, ordered-orbit tail ultrafilters and orbitwise transport require only G=Aut(Q,<) and finite Q-support of all elements. At relational type τ the ambient atoms form W×D_{α₁}×...×D_{αₙ}, which is another such nominal set. Finiteness and trivial action of W were used there only to prove Intensional Choice, not to construct the retractions.

Consequently the present model satisfies all-type Boolean retractions preserving every admitted internally well-ordered indexed meet and join, in addition to T, quantified Infinity_e, EU_e and S_e, and still has no common exact-coordinate witness. The well-order proof uses admitted stabilizer orbits: an orbit has an internal least point, which its stabilizer fixes, so the orbit is a singleton. It does not assume that an internal well-order is externally well-founded. One common finite support for an indexed family then gives one common tail for its ultrafilter decisions.

Intensional Choice for individuals fails here. At world w require an output x strictly above the greatest essential endpoint of w. This serial relation is equivariant and admitted. If a selector had finite support S, choose a one-endpoint world w with its endpoint a above every member of S. The selected x would be fixed by G_{S∪{a}}, whose only fixed rationals are S∪{a}; but no such rational is above a. Hence there is no selector. This identifies the precise limitation rather than transferring the fixed-finite-world IC argument to a different world action.

The endpoint decoder and fixed-point-count obstruction were independently audited by both sibling research lanes. The inheritance of well-ordered-family retractions was independently checked with the mixing-models lane. These are agent cross-checks, not named-human or Lean certifications.


## 23. A single propositional retraction suffices to combine the witnesses

Full Functional Choice is sufficient to combine existential EU_e and S_e, but is stronger than needed. This refinement was suggested by the root research lane.

**Theorem 23.1.** Over T, EU_e + S_e + Ret_t implies an exact-coordinate witness. More precisely, if R witnesses EU_e, it suffices that its generated complete subalgebra A_R admit a complete Boolean retraction; no retraction hypothesis at other types is needed.

Let U be the rigid individual-profile field. The EU witness gives the represented surjection f_R:W→U. Its kernel equivalence is equality of R-profiles, and its associated complete subalgebra is exactly A_R by §§1 and 21. A complete retraction onto A_R yields, by §16, a representative c(w) in each profile class, constant on that class. For each Y∈U there is therefore exactly one w satisfying

    f_R(w)=Y and c(w)=w.

EU gives existence; the class-selector property gives uniqueness. This admitted rigid graph represents a section i:U→W of f_R, and hence an injection. To represent a map on the whole ambient property type, use any one fixed world as default outside U; there is no infinite choice here.

The possibly different separating witness supplies an injection j:W→U. The internal Schroeder–Bernstein proof uses no Choice. For completeness, let Z⊆W be the least admitted rigid subset containing W minus range(i) and closed under i∘j. Define it by intersection of all admitted rigid subsets satisfying those two clauses. The field of such subsets is nonempty, containing W, and comprehension provides Z. If Z_0=W minus range(i), minimality gives

    Z = Z_0 union i(j(Z)):

the right side is contained in Z, contains Z_0, and is closed under i∘j, hence contains Z by minimality. Define h:W→U by j on Z and by the unique inverse of i off Z. The latter exists because W minus Z is contained in range(i). Injectivity follows separately on each piece from injectivity of i,j; a collision between pieces would put the outside point i(j(w)) back in Z. For u∈U, if i(u) is outside Z it is its preimage under the inverse piece. If i(u)∈Z, it is not in Z_0, so the displayed fixed-point identity gives i(u)=i(j(w)) for some w∈Z, and injectivity of i yields u=j(w). Hence h is surjective.

All subsets, images and graph clauses in this construction are admitted rigid predicates. Unique-value comprehension therefore represents h. Finally put

    Vx := exists w[Atom(w) and w and h(w)(x)].

At world w this relation has precisely the profile h(w). The bijectivity of h makes V an exact-coordinate witness. ∎

The same proof works at any index type σ, with U the rigid σ-property field. Ret_t remains the relevant retraction hypothesis because the partition being selected is a partition of world atoms, regardless of the generator type.

The endpoint-world model in §22 directly fails Ret_t. Indeed there is no admitted injection U→W at all: if such an injection had finite support S, it would inject the finite fixed-point set U^{G_S} into W^{G_S}, contradicting their cardinalities. In particular the profile surjection f_R has no admitted section. Its complete generated subalgebra A_R is therefore a concrete nonretracting propositional subalgebra. The finite and well-ordered-family-preserving retractions already verified for that model cannot be strengthened to complete ones.

This gives a precise boundary: complete propositional retraction is sufficient for combining separate universality and separation witnesses, while all-type preservation of even all admitted well-ordered families is insufficient.


## 24. Two limits on the algebraic terminology

### Choice retractions are not invariant under all automorphisms

Suppose an internally complete atomic Boolean algebra B has at least two atoms. Its two-element subalgebra {0,1} has complete Boolean retractions exactly given by evaluations at atoms, by §9. No such retraction H is invariant under every complete Boolean automorphism of B. If H evaluates at a, choose a different atom b and use the admitted transposition of a and b. Then H(a)=1, whereas H(π(a))=H(b)=0. The required atom transposition is already available in T; in the propositional case its all-type logical lift is part of the recorded no-pure-contingency argument cited in §0.

Consequently full Functional Choice gives existential retractions, and can choose a represented family of them for subalgebras of a fixed carrier, but cannot give a family invariant under all automorphisms preserving the inclusions. Adding this invariance would make the requirement false even in ordinary full models with two worlds. “Natural” in the informal sense of a concise structural principle must not be confused with categorical naturality of the selected retractions.

By contrast the canonical map Φ_R of §21 is uniquely determined by its explicitly supplied generators. It respects symmetries carrying those generators along: for a complete Boolean automorphism α of the target, uniqueness gives Φ_{αR}=α∘Φ_R. Its canonicity has a different source from choosing a splitting of an arbitrary inclusion.

### Atomic targets are essential to the free-object assertion

For a concrete full-model boundary, let E=N and C_e=P(P(N)). Consider the complete Boolean algebra of regular open subsets of Cantor space 2^N. Its nth coordinate cylinder G_n is clopen. For any binary profile X, the meet of the literals G_n or ¬G_n prescribed by X is zero: their set intersection is the singleton {X}, whose interior is empty. In the regular-open algebra, arbitrary meets are interiors of intersections, joins are interiors of closures of unions, and complement is interior of set complement.

If there were a complete Boolean homomorphism C_e→RO(2^N) sending every coordinate generator to G_n, it would send each singleton profile atom to that zero meet. But top in C_e is the join of all its singleton atoms, so complete join preservation would send top to zero, contradicting unitality. Thus the coordinate assignment does not extend.

In a full Gallin model all these sets and operations can be represented as rigid higher-type fields and operations. The failure is therefore not a missing external subset or an encoding issue: the target is internally complete but atomless. Theorem 21.1 correctly restricts to complete ATOMIC targets. No assertion about the existence or nonexistence of a different free object in the category of all complete Boolean algebras is made here.


## 25. Finite retractions are exactly uniform ultrafilter-valued choice

Let P_ρ be the rigid field of rigid ρ-properties. An ultrafilter on that field is a rigid predicate U on P_ρ which contains top, excludes bottom, preserves binary intersections, and decides every relative complement. All quantifiers are restricted to the admitted rigid properties; an external subset of D_ρ absent from the hierarchy is not an argument of U.

Define **Ultrafilter Choice** at (σ,ρ) as follows. For every serial rigid relation R^{σρt}, there is an admitted rigid relation K(x,P), with P ranging over P_ρ, such that for each x, K_x is an ultrafilter on P_ρ and K_x(R_x). An arbitrary actual serial relation may first be rigidified using T, so restricting the displayed definition to rigid R loses no actual choice instances. Semantically K_x is a finitely additive {0,1}-valued probability concentrated on the possible R-outputs for x. Principality is not required.

**Theorem 25.1.** Over T, all-type finite Boolean retractions are equivalent to all-type Ultrafilter Choice.

**Retractions imply Ultrafilter Choice.** Fix a world atom a. In B_{σρt}, let

    c_x(u,v) := a and u=x and R(x,v).

Seriality makes each c_x nonzero; distinct x give disjoint c_x. Partition the ambient atoms by putting all atoms below one c_x into one class and making every remaining atom a singleton class. The relation is rigid and admitted by the world/tuple atom coding of §16. The associated complete subalgebra has the c_x among its relative atoms. Let H be a finite Boolean retraction onto it. For rigid P^{ρt}, put

    K_x(P) iff c_x <= H(lambda u v[a and u=x and Pv]).

By Theorem 20.1 this is the pullback of the ultrafilter attached to c_x. Intersecting all arguments with c_x shows that the displayed map respects relative complement, even though the ambient predicate lambda u v[a and u=x and Pv] is not unital in the whole B_{σρt}. Since the value at R_x is c_x, K_x contains R_x. Every clause is uniform in x, so K is represented. No choice of an ultrafilter separately for each x is made.

For clarity about that relative unit, write d_x(P)=lambda u v[a and u=x and Pv]. Then d_x(P)∧d_x(¬P)=0 and d_x(P)∨d_x(¬P)=d_x(⊤). Since c_x≤d_x(⊤) and H fixes c_x, we have c_x≤H(d_x(⊤)). The relative atom c_x therefore lies below exactly one of H(d_x(P)) and H(d_x(¬P)); binary intersections transfer in the same way. This establishes the ultrafilter laws without incorrectly treating d_x as a unital map into the entire ambient algebra.

**Ultrafilter Choice implies retractions.** For a complete subalgebra A⊆B_τ, use as inputs its relative atoms c and as possible outputs the ambient atoms b≤c. Extend this relation to unused inputs by one fixed ambient atom if required. Ultrafilter Choice supplies a uniform ultrafilter K_c on rigid properties of ambient atoms, concentrated on the atoms below c. Pull it back along the Boolean map

    p ↦ lambda b[Atom(b) and b<=p].

The resulting uniform ultrafilter on B_τ contains c. The Boolean map here has codomain the relative powerset of the ambient atom field. If UFC is stated on the entire carrier D_τ, concentration on the nonempty fiber {b:Atom(b) and b≤c} makes K_c contain the ambient atom field, so relative complements give exactly the same pullback laws. Theorem 20.1 constructs the finite retraction. ∎

Thus the exact finite-operation principle has a direct choice interpretation: select a Boolean-consistent collection of observations about each output, without requiring those observations to be realized by one output. Complete Boolean retractions require internal meet preservation and thereby force realization by a point. The internally well-ordered-preserving variants in the ordered nominal models show that preservation along all well-ordered observation families still need not suffice.

Finite fibers give ordinary choice by internal finite primeness, as already proved in §20. In combination with Finite Multiple Choice, this yields full Relational Choice: first restrict each fiber to a represented finite nonempty subfiber, then select its unique ultrafilter point. Conversely full Choice gives both principles. The companion mixing report supplies the independent-factor models and the full typed proof; this paragraph records the consequence, not a separate claim of set-theoretic novelty.

## 26. Fine ultrafilters isolate the missing filter-extension strength

Use the following exact internal definitions.

- **FE:** every proper admitted rigid filter on the rigid properties of any admitted rigid field extends to an admitted ultrafilter.
- **FineUF:** for every admitted rigid field I, the field Fin(I) of its rigid internally Frege-finite subfields has an admitted ultrafilter V containing every cone C_i={A∈Fin(I):i∈A}.

Filters here live on the admitted relative Boolean algebra of rigid subsets of the indicated field. Field restrictions and off-field defaults are allowed throughout; this is equivalent to a whole-type formulation by requiring the filter to contain the field predicate. FineUF is not ordinary existence of some ultrafilter on Fin(I): it must contain every displayed cone, which is the cofinality requirement.

**Theorem 26.1.** Over T,

    FE iff (Ultrafilter Choice and FineUF)
       iff (all-type finite Boolean retractions and FineUF).

**FE implies FineUF.** The cone family has the finite intersection property internally. For an internally finite F⊆I, its cone is nonempty because F itself belongs to Fin(I). Finite unions of finite subfields are finite by Frege induction. The admitted upward closure of these cones is therefore a proper filter. Apply FE.

**FE implies Ultrafilter Choice.** Fix a serial rigid R⊆D_σ×D_ρ. Let J be the rigid field of finite partial choice graphs: a member g is a rigid single-valued relation, every edge satisfies R, and its domain is internally finite. This is an admitted field of type σρt objects. For each x let C_x⊆J contain the graphs whose domain includes x. Every finite family of these cones has nonempty intersection: finite choice is proved in T by successor induction, so any internally finite input field admits a partial R-choice graph on that field. Consequently the admitted filter generated by the cones is proper.

FE supplies an ultrafilter V on J containing every C_x. For P∈P_ρ define

    K_x(P) iff V({g∈J: exists y[g(x,y) and Py]}).

The domain cone C_x is V-large. On it, uniqueness of g(x,y) makes the events for P and ¬P complementary and makes intersections agree. Thus K_x is an ultrafilter. Since all graph edges satisfy R, it contains R_x. The formula is uniform in x and P, giving the represented kernel. This argument avoids selecting one local graph for every finite domain: only the existence of each finite-domain graph is used to verify properness of the filter.

**Ultrafilter Choice plus FineUF implies FE.** Let F be a proper rigid filter on the rigid subsets of a field Y. Let I be its rigid field of members. For each A∈Fin(I), the finite meet

    m_A(y) := Yy and forall P(AP -> Py)

is a filter member and is nonempty. This is proved by finite induction from the filter laws. Apply Ultrafilter Choice to the serial relation m_A(y), obtaining a uniform ultrafilter K_A on Y containing m_A. FineUF supplies an ultrafilter V on Fin(I) containing each cone C_P for P∈F. Put

    U(P) iff V({A∈Fin(I):K_A(P)}).

This is an ultrafilter, because each K_A and V respect complements and finite intersections. If P∈F, every A containing P satisfies m_A⊆P, so K_A(P). The decision set is therefore a superset of C_P and belongs to V. Thus U extends F. All event predicates, finite-meet graphs and ultrafilter sums are admitted by λ-comprehension; no external family or uniform witness choice is inserted. ∎

This theorem identifies a precise extra compactness ingredient beyond finite retractions. It does not establish that FineUF follows from finite retractions, and does not by itself supply a model separating them. Section 32 subsequently gives a literature-dependent separation. Consequently finite retractions must not be identified with the Boolean Prime Ideal Theorem.

In ordinary full set semantics FE is the usual ultrafilter-extension form of BPI. Internally, identifying it with any chosen abstract-Boolean-algebra or propositional-compactness formulation requires the corresponding finite-algebra/quotient coding. The stated theorem uses FE directly and does not rely on that identification.

## 27. Ultrafilter lifting and a countable compactness consequence

Ultrafilter Choice has useful consequences below full filter extension.

First, every admitted surjection f:X→Y lifts admitted ultrafilters. Choose a kernel K_y concentrated on the fiber f^{-1}(y). Given an ultrafilter V on Y, define

    U(A) iff V({y:K_y(A)}).

Then U is an ultrafilter on X and its pushforward under f is V: for B⊆Y, K_y(f^{-1}(B)) holds exactly when y∈B. The same kernel defines a represented lifting operation for all admitted V at once. This is stronger than merely observing that each principal ultrafilter has some lift. In full set theory, the pointwise existence of such lifts is studied as PUU; see Herrlich, Howard and Keremedis, “On preimages of ultrafilters in ZF”, Commentationes Mathematicae Universitatis Carolinae 57 (2016), 241–252, especially the definitions and Theorem 4. [Article](https://dml.cz/handle/10338.dmlcz/145755). Their results provide context only; the uniform typed lifting above is proved by the displayed formula.

Second, suppose an admitted ultrafilter V on the internal natural-number field contains every final segment {n:n≥k}. Given a represented descending sequence of nonempty rigid sets F_n⊆Y, Ultrafilter Choice supplies K_n containing F_n. Its ultrafilter sum along V extends every F_k, since K_n(F_k) holds for all n≥k. Therefore finite retractions plus such an unbounded natural-number ultrafilter imply extension of every represented countable filter base, after replacing a sequence by its finite initial intersections.

The hypothesis is explicitly final-segment containment. In a nonstandard Henkin arithmetic, “nonprincipal” alone need not have that meaning without additional internal-finiteness facts. In the ordered full-support nominal models the Frege naturals are standard and fixed by the group; all external subsets of that pure numeral field are admitted, so ordinary ambient ZFC supplies a free ultrafilter satisfying the hypothesis. Those models can therefore satisfy this countable filter-extension principle while still failing Dependent Choice and the concrete countably indexed selection instance in the mixing report. Countable filter extension should not be confused with countable Choice.


## 28. FE is equivalent to an explicit internal Boolean Prime Ideal principle

Define **BPI_int** to say: every admitted nontrivial Boolean algebra, whose carrier is a rigid admitted field and whose operations and equality are given by rigid admitted graphs, has an admitted ultrafilter. This includes algebras whose operations are not inherited pointwise from an ambient type algebra. A homomorphism to {0,1} can be represented by its rigid positive-value predicate, so an operation with individual output is never required.

**Theorem 28.1.** Over T, BPI_int is equivalent to FE of §26. Consequently

    BPI_int iff (all-type finite Boolean retractions and FineUF).

This is a newly supplied typed coding proof, not an unqualified transfer of a full-set theorem.

**BPI_int implies FE.** For a proper admitted filter F on a represented Boolean algebra B, let I={b:¬b∈F}. This is a proper ideal. Define b~c iff their Boolean symmetric difference belongs to I. The equivalence classes have canonical rigid codes

    q_b := lambda c[Bc and b~c].

Their field Q={q_b:b∈B} is admitted. Boolean operations are defined on class codes by q_b∧q_c=q_(b∧c), and similarly for complement and constants. The ideal laws prove that these values are independent of representatives. Their unique-value graphs are admitted; no simultaneous selection of representatives is needed. Properness of I gives q_0≠q_1. Apply BPI_int to Q and pull its ultrafilter back along b↦q_b. Every member b of F maps to q_1, so the pullback extends F. Applying this to the rigid powerset fields gives FE.

**FE implies BPI_int.** Let B be a nontrivial represented Boolean algebra. Every internally finite field F⊆B lies in an admitted finite Boolean subalgebra. Here is the finite induction needed for that claim. The subalgebra generated by the empty field is {0,1}. If a finite subalgebra C has been obtained and u is a new generator, the algebra generated by C and u is exactly

    {(x∧u)∨(y∧¬u):x,y∈C}.

It is finite, contains C and u, and is closed under Boolean operations by coordinatewise calculation. Finite products and images are internally finite by successor induction. Equivalently, the generated algebra is the intersection of all admitted subalgebras containing the given finite field; the displayed finite construction proves that intersection finite. No external assertion about all finite sets is substituted for internal finiteness.

Every nontrivial finite Boolean algebra has an atom: the finite field of nonzero elements has a minimal element under the Boolean order, by finite induction. Evaluation at that atom is a {0,1}-valued homomorphism. Thus every finite input field F has a finite subalgebra C containing it and a homomorphism v:C→{0,1}.

Let J be the admitted rigid field of these finite valuation tables (C,v). The carrier predicate C and the positive-value predicate v have the same relational type; an ordered pair can be coded by the rigid singleton relation lambda C' v'[C'=C and v'=v]. The conditions “C is a finite subalgebra”, “v vanishes off C”, and “v is a Boolean homomorphism on C” are formulas in the existing C language. No formula-string or syntax-tree construction is required.

For b∈B let C_b be the cone of tables whose domain contains b. Every internally finite family of cones has nonempty intersection by the preceding finite-subalgebra argument. Their admitted upward closure is a proper filter on J. FE gives an ultrafilter V containing every C_b. Define

    U(b) iff V({(C,v)∈J : Cb and vb}).

On the V-large cone C_b, the table evaluates b and ¬b consistently. On C_b intersect C_c it consistently evaluates b,c and b∧c. These large-cone identities show that U contains 1, excludes 0, decides complements and preserves binary meets. Hence U is an admitted ultrafilter on B. The displayed formula supplies uniformity, with no chosen valuation table for each finite domain. ∎

This theorem also calibrates the algebraic scope of finite retractions. Restricting an ordinary finite Boolean homomorphism to an internally complete ATOMIC ambient algebra leads to Ultrafilter Choice. Allowing arbitrary abstract Boolean algebras introduces the additional FineUF compactness requirement. At this stage the exact separation was not yet established. Section 32 subsequently supplies the reverse separation using a verified published ZFA result and an explicit typed transfer. The ordered nominal models cannot supply that separation: §31 proves they satisfy BPI_int.


## 29. FineUF alone is insufficient: a compact pair-flip model

The full pair-flip nominal hierarchy supplies one direction of separation for the factorization in §28. Let E be an infinite union of labeled two-element blocks, let G be the product of their independent flips, and let W be finite, nonempty and fixed pointwise. Use finite supports in the atom base, or equivalently supports consisting of finitely many whole blocks. This is the previously audited model with T, quantified Infinity_e and all Intensional Choice, but no selector from the blocks.

Every typed object has a finite G-orbit: a finite support meets only finitely many blocks, and only their finitely many flips can change that object. More generally, if a rigid field I has support S and H=G_S, each H-orbit in I is finite. Let O=I/H be the external set of these orbits. In the ambient ZFC metatheory choose a fine ultrafilter V on the ordinary finite subsets of O. Map each finite family of orbits to its union, which is a finite H-fixed subset of I. Push V forward along this map and restrict to the admitted rigid predicates on Fin(I).

The resulting ultrafilter is H-invariant: every image point is H-fixed, so a predicate and its H-translate have the same inverse image. It is therefore admitted with support S. It is fine, since for i∈I the event “the finite orbit family includes H·i” is V-large and implies that its union contains i. Internal Frege finiteness in this full nominal hierarchy is standard, so every finite union used here belongs to the intended Fin(I).

Thus FineUF holds at every type in this model. Finite Boolean retractions fail because they would choose actual points from the finite pair blocks; BPI_int fails for the same reason. This proves that FineUF alone does not imply finite retractions or BPI_int, even with all Intensional Choice and quantified Infinity. The construction uses ordinary external ZFC to verify existence of the supported ultrafilter; it does not claim an internal orbit quotient or a chosen internal representative from each orbit.

The mixing-models lane independently audited this argument. The converse separation—finite retractions without FineUF/BPI_int—is supplied in §32 using a verified published ZFA result and an explicit typed transfer.

## 30. Ultrafilter Choice forces nonprincipal ultrafilters on infinite fields

The following useful consequence narrows the search for a countermodel to finite retractions implying BPI. All fields, properties, kernels and filters below are admitted and rigid. Precisely, for a rigid field I of type σt, Fin_σ(I) means that I has an internally Frege-finite cardinality (there is a finite cardinal n with n(I)); Inf_σ(I) means ¬Fin_σ(I). The theorem assumes Inf_σ(I), not merely external infinitude of its semantic extension. P(I) consists of admitted rigid σ-properties contained in I, and every subset event and filter below is relative to its displayed field.

**Lemma 30.1.** If a Boolean algebra has an admitted well-order of its carrier, every proper admitted filter on it extends to an admitted ultrafilter, without a general Choice assumption.

**Proof.** Process its elements in that well-order, putting b into the filter when it is consistent with the earlier decisions and putting ¬b in otherwise. This transfinite description has an explicit comprehension proof. Consider all admitted assignments on initial segments which follow that rule and whose selected literals, together with the original filter, have the internal finite intersection property. The empty assignment qualifies. Two qualifying assignments agree on their common domain, by taking the least point of disagreement. Their domains are comparable initial segments, so their union is a functional admitted assignment on an initial segment.

The union of all qualifying assignments still has the finite intersection property: any finite set of decision indices has a greatest index, and some qualifying assignment contains it and all smaller indices. The union also follows the same decision rule, since each individual decision already occurs with its entire predecessor segment in a qualifying assignment. If its domain were proper, append the least missing element. At least one of b and ¬b preserves the finite intersection property: if both failed, two finite witnesses, combined, would contradict the previous property's consistency. The prescribed choice of the positive branch when possible is unique. This produces a longer qualifying assignment, a contradiction. Thus the union is total. Its chosen literals generate a proper filter deciding every Boolean element, hence an ultrafilter. All tests quantify over admitted internally finite fields; no external ordinal recursion or selected family of partial assignments is assumed. ∎

**Theorem 30.2.** Over T plus Ultrafilter Choice, every internally infinite field I has an admitted nonprincipal ultrafilter on its rigid properties.

Assume for contradiction that all ultrafilters on I are principal. Let P(I) be the rigid field of rigid subsets of I. Suppose U were a nonprincipal ultrafilter on P(I). Its coordinate-limit profile is

    v(i) iff Ii and U({X∈P(I):Xi}).

This is an admitted member of P(I). For every X≠v the symmetric difference X△v is nonempty. Apply Ultrafilter Choice to choose a kernel K_X concentrated on X△v, using all of I as the harmless fiber at X=v. Take its U-sum:

    V(A) iff U({X:K_X(A)}).

This is an ultrafilter on I. For any i∈I, if X≠v and K_X({i}) holds, then i∈X△v, because K_X contains that difference. Hence the event K_X({i}) is contained in

    {X:i∈X△v} union {v}.

The first set is U-small by the definition of v, and the second is U-small by nonprincipality of U. Their finite union is U-small. Therefore V contains no singleton, contradicting the assumption about ultrafilters on I.

It follows that every ultrafilter on P(I) is principal. Apply Ultrafilter Choice to the relation A(X) for all nonempty admitted subfields A⊆P(I), with a default fiber elsewhere. Each selected ultrafilter contains A and has a unique principal point, giving an admitted ordinary choice function on the nonempty subfields of P(I). The standard internal Zermelo construction then well-orders P(I): take the union of all compatible choice-generated initial well-orders, where the next element is the chosen point of the remaining field. Compatibility follows at the least disagreement; if the union omitted a point, the choice function would extend it. The union is internally well-ordered: given a nonempty admitted subset K of its domain, take x∈K and a partial order containing x. If K meets the predecessor segment of x, its least member there is least in all of K; otherwise x is least. This uses only represented relation codes and their admitted union.

Now P(I), regarded as a Boolean algebra, has an admitted well-order. The cofinite filter on I is proper because I is internally infinite. Lemma 30.1 extends it to an ultrafilter. Such an ultrafilter contains the complement of every singleton and therefore is nonprincipal, again a contradiction. ∎

Thus a prospective finiteRet-without-BPI model cannot simply omit all free ultrafilters. In particular, whenever an internally infinite natural-number field with finite initial segments is available, finite retractions already supply an ultrafilter containing every final segment. The countable filter-extension consequence of §27 then needs no separate ultrafilter-existence assumption. In nonstandard arithmetic the conclusion still uses internal finite primeness: a nonprincipal ultrafilter contains no internally finite set, so it contains the complement of each internally finite initial segment.

The proof is a new typed argument in these notes, independently audited by both companion research lanes. It does not establish FineUF, which demands simultaneous membership of every coordinate cone on Fin(I), not just nonprincipality. The failed generalization is precise: an ultrafilter on Fin(I) determines a coordinate profile L={i:C_i belongs to the ultrafilter}; non-fineness says L is a proper subfield, but gives neither a unique point nor principality. Thus the unique-point extraction and well-order construction in Theorem 30.2 do not apply. No implication or separation between Ultrafilter Choice and FineUF is claimed here.

## 31. The ordered models satisfy full internal BPI

The ordered nominal models must not be used to separate finite retractions from BPI_int. They satisfy the latter, including the endpoint-world model of §22.

**Source fact.** Andreas Blass, *Partitions and Permutation Groups*, §2, printed p.2, states extreme amenability of Aut(Q,<) with the pointwise-convergence topology. Section 3, printed pp.3–4, explicitly identifies the finite-support ordered Mostowski permutation model as satisfying BPI while failing Choice. No publication year is inferred from the draft's placeholder copyright line. [Verified primary text](https://janos.cs.technion.ac.il/RESEARCH/AMS-Book-files/pdfs/11_Blass.pdf).

Here is the precise transfer to the typed models, independent of identifying their entire hierarchy with a set-theoretic permutation universe. Work in the external ZFC metatheory. Let B be any admitted rigid Boolean algebra, with carrier and operation graphs supported by a finite S⊆Q, and let F be a proper admitted rigid filter on B. Enlarge S to support F. Put H=Fix(S). This is a group of Boolean automorphisms of B preserving F.

If S has n points, its n+1 complementary open intervals are each order-isomorphic to Q. Restriction identifies H topologically with a finite product of copies of Aut(Q,<). Finite products of extremely amenable groups are extremely amenable: for a continuous action of G₁×G₂ on a nonempty compact Hausdorff space, the G₁-fixed subspace is nonempty compact and G₂-invariant, and a G₂-fixed point in it is fixed by the product. Induct on the number of factors.

Let K be the external Stone space of all ordinary ultrafilters on the external Boolean algebra B which extend F. External ZFC proves that K is nonempty and compact Hausdorff: view its points as Boolean homomorphisms B→2 satisfying the equations U(b)=1 for b∈F. These conditions define a closed subspace of 2^B, and the ordinary external ultrafilter-extension theorem gives nonemptiness. This is a semantic construction in the metatheory, not an assumption that the typed model already satisfies BPI.

The H-action on K is continuous. For b∈B, the evaluation clopen is {U:U(b)=1}; b has a finite support, so its H-stabilizer is open. Around any (h,U), keeping h'^{-1}b equal to h^{-1}b by restricting h' to an appropriate open coset, and keeping U' in the corresponding evaluation clopen, preserves membership of h'U' in the chosen clopen. This proves joint continuity on a clopen base.

Extreme amenability gives U∈K fixed by H. Therefore the positive-value predicate of U has finite support S. In the full finite-support Henkin hierarchy every such predicate is admitted. It is rigid because it depends only on the argument b, not on the current world. Consequently U is an admitted ultrafilter extending F. This proves FE, and hence BPI_int and FineUF by §§26 and 28.

The argument uses only that every typed object has finite Q-support and that all supported predicates at each relational type are admitted. It therefore applies with finite fixed worlds, fixed countably many worlds, ordered worlds, and the endpoint-subset worlds of §22. Its conclusion concerns internally represented algebras and filters; it does not turn the typed property fields into external full powersets.

In particular, the endpoint model satisfies

    T + quantified Infinity_e + EU_e + S_e + BPI_int
      + all internally well-ordered-family-preserving Boolean retractions,

while having no exact profile witness and failing IC_e and complete Ret_t. Thus even full internal Boolean Prime Ideal compactness does not suffice to combine separate universal-extension and separation witnesses into one exact configuration witness. The positive complete-retraction criterion in §23 remains genuinely stronger on that example.

## 32. Literature-dependent separation of finite retractions from BPI

**Verified source premise and limits.** P. Howard and E. Tachtsis, *On the minimal cover property in ZF*, Topology and its Applications **173** (2014), 94–106, in Remark 4 following Theorem 10, explicitly report that Form 344 is strictly weaker than BPI in ZFA. Form 344 is the assertion that every indexed family of nonempty sets admits an indexed family of ultrafilters on those sets. They refer to Howard–Rubin, *Consequences of the Axiom of Choice*. [Primary article](https://www.sciencedirect.com/science/article/pii/S016686411400248X). The article's searchable publisher text was inspected; its exact printed page for that sentence was not recovered, so no page number is invented. The earlier permutation-model construction underlying that cited separation has not been reconstructed here. The following is an explicit typed transfer of the reported set-theoretic separation, not a new independent construction of that set-theoretic model.

Let M be a model of ZFA satisfying Form 344 but failing BPI. Select in M a nontrivial Boolean algebra B having no ultrafilter in M. Put E=(B×{0})∪(ω^M×{1}), and take the singleton world set W={*}. Define the complete finite-type hierarchy inside M: D_e=E, D_t={0,1}, and for each relational arrow type σρ, D_(σρ) is the function set (D_ρ)^(D_σ) as computed in M. Application and logical operations are the usual ones. Modal necessity and possibility are the identity because W has one world.

This construction needs no Choice in M. Power Set supplies each function domain, Separation supplies Boolean operations and quantification over a type domain, and Replacement supplies each uniquely defined λ-function. More precisely, induction on any fixed C-term/formula translates its interpretation into a set-theoretic definition in M; the relevant graph is an M-set with the required domain and codomain, hence belongs to the assigned arrow domain. All quantifiers range over M's indicated type domains, so comprehension is Henkin closure, not external full comprehension.

The interpretation does not require M to be transitive or standard. Each internal function graph induces an external function on the external realizations of its M-domain and M-codomain. M's function and extensionality axioms make this interpretation single-valued and injective on internal function objects. A fixed standard finite C-formula has the displayed set-theoretic translation in M, so its internal comprehension witness supplies the required external Henkin object. Claims about finiteness and ω in this construction remain internal to M and to the resulting typed model.

C and □Plenitude hold. Extensional identity is literal function identity; every represented total functional graph has its represented function by the graph-to-function construction in M. Every nonzero relational Boolean element contains a singleton tuple, and those singleton relations are in M, giving Atomicity at every relational type. All Intensional Choice holds at the single world: an existential witness is already a constant choice of intension, with no multiple-world selection. The ω-tagged field has the admitted successor injection into its proper tail, so the model satisfies the quantified Infinity_e used in these notes, not merely external infinitude.

Form 344 transfers to typed Ultrafilter Choice. A rigid typed serial relation R determines in M the indexed family of its nonempty fibers. Form 344 supplies an M-family of ultrafilters on those fibers. Extend each to the ambient output field by the canonical formula

    K_x(P) iff P∩R_x belongs to the selected ultrafilter on R_x.

The resulting characteristic graph is an M-set at the required relational type, hence admitted. Thus all-type UFC holds, and §25 gives every finite Boolean retraction.

The tagged copy of B is an admitted individual field. Its Boolean operations are admitted functional relation graphs of the appropriate types. Any admitted ultrafilter on this coded algebra would be an M-subset of its carrier; transporting it through the tagging bijection would give an M-ultrafilter on B, contrary to the choice of B. Thus BPI_int fails. Since UFC holds, Theorem 28.1 forces FineUF to fail. Complete Ret_all and □Functional Choice also fail, since either would imply BPI_int by the previously established implications.

Consequently, relative to the published ZFA separation, there is a full-in-M singleton-world Henkin model of

    T + all Intensional Choice + quantified Infinity_e
      + all-type finite Boolean retractions
      + not BPI_int + not FineUF.

Theorem 30.2 additionally gives a nonprincipal ultrafilter on every internally infinite rigid field in this model. This answers the earlier fineness question negatively: even Ultrafilter Choice together with this all-field nonprincipal-ultrafilter conclusion does not imply FineUF. The coordinate-limit proof cannot be strengthened to arbitrary fineness on this basis.

Combined with §29, this gives both directions of independence of the two factors in

    BPI_int iff (finite Ret_all and FineUF).

The pair-flip direction is constructed directly in these notes. The reverse direction uses the published set-theoretic separation through the explicit interpretation above. Earlier statements in §§26–29 describing that reverse separation as unsettled record the stage of the investigation; this section supersedes that status, with the stated literature dependency.

## 33. Uniformization inside spaces of ultrafilters

A useful closure argument explains how much uniformity finite retractions already supply. Let R_x be a represented family of nonempty rigid fields. Suppose C_x is a represented nonempty field of ultrafilters on R_x, and suppose membership in C_x is specified by any admitted family of fixed positive or negative evaluations. For example, these may require an ultrafilter to contain every member of a specified filter, to exclude every singleton, or to contain every cone from a specified fineness family.

Ultrafilter Choice supplies an ultrafilter L_x on the field of candidate ultrafilters, concentrated on C_x. Define its evaluation sum

    U_x(P) iff L_x({V∈C_x:V(P)}).

Because each candidate V satisfies the Boolean ultrafilter laws, their evaluation events satisfy the same laws. Therefore U_x is an ultrafilter. Every specified positive evaluation holds on all of C_x, and every specified negative evaluation fails on all of C_x; the sum preserves all these individual constraints. All displayed fields and events are admitted by comprehension. This does not require selecting one candidate ultrafilter from each C_x.

In particular, Theorem 30.2 makes the candidate field of nonprincipal ultrafilters nonempty for each internally infinite R_x. Applying this construction yields a represented family of nonprincipal ultrafilters on every represented family of internally infinite fields. The same argument makes FE uniformly applicable to families of proper filters once FE is assumed. It also makes FineUF uniform once pointwise FineUF is assumed. None of these uniformization consequences supplies existence of a candidate satisfying new constraints when that candidate field may be empty.

**Historical caution about §30.** Howard–Rubin's 1998 numerical list gives the exact family-ultrafilter statement as Form 344 (printed p.61), and uniform nonprincipal-ultrafilter choice as Form 123. Their relationship table records 344→70, where 70 is existence of a free ultrafilter on ω, with code 7; the code legend (printed p.319) means that the question was asked and its status was then unknown. This is historical evidence, not a current open-problem claim. Theorem 30.2 has been rechecked as an ordinary ZF/ZFA argument as well as a typed argument by all three mathematical lanes. Its ω case has the especially simple additional check: any nonprincipal ultrafilter on P(ω) pushes to a free ultrafilter on ω by taking the least coordinate at which a subset differs from its ultrafilter limit profile. If no free ultrafilter on ω existed, all ultrafilters on P(ω) would therefore be principal; Form 344 would give a choice function on the nonempty subsets of P(ω), hence a well-order of P(ω), and greedy extension of the cofinite filter would be a contradiction. No claim of historical novelty or of resolving a problem still open in the literature is made.


**Equivalence with uniform nonprincipal-ultrafilter choice.** Define UniformFreeUF to say that every admitted family of internally infinite rigid fields has an admitted family of nonprincipal ultrafilters on its fields. The preceding evaluation-sum argument proves UFC⇒UniformFreeUF. Conversely fix a serial relation R with output type ρ. By classical logic, the whole field D_ρ is internally finite or internally infinite. In the finite case, finite induction constructs an admitted linear order on D_ρ, and taking the least point in each fiber gives ordinary choice and hence principal ultrafilter kernels. This is one order of a single finite field, not a choice of orders for an arbitrary family.

In the infinite case inflate each fiber R_x to R_x×D_ρ. Encode ordered pairs (y,z) by the rigid singleton binary relation λu v(u=y∧v=z), so every inflated fiber is an admitted field at a relational type. For each x, any one witness y∈R_x gives an admitted injection z↦(y,z) from D_ρ into that fiber; hence the fiber is internally infinite. This is a proof of pointwise infinitude and does not select the witnesses uniformly. UniformFreeUF gives a uniform ultrafilter on each inflated fiber. Push it forward by the represented first-coordinate projection to obtain an ultrafilter concentrated on R_x. The result may be principal, as permitted by UFC. Thus, over T and without a separate Infinity axiom,

    finite Ret_all iff UFC iff UniformFreeUF.

The finite/infinite split avoids any unnoticed assumption that a natural-number object or an infinite field exists in every T-model. In a model with every type domain internally finite, UniformFreeUF is vacuous and UFC follows by the finite-field argument.

## 34. A three-level algebraic hierarchy and an extension formulation of BPI

There is a concise categorical definition of the middle level. An admitted nontrivial internally complete atomic Boolean algebra C is **injective for finite Boolean homomorphisms** when, for every admitted injective Boolean homomorphism j:A→B between represented Boolean algebras and every admitted Boolean homomorphism h:A→C, there is an admitted Boolean homomorphism H:B→C with H∘j=h. Here the maps preserve only finite Boolean operations, the carrier fields and operation graphs are rigid, and A and B need not be atomic or internally complete. All maps with individual-valued carriers are expressed by functional graphs.

**Theorem 34.1.** Over T, BPI_int is equivalent to injectivity, in this sense, of every represented nontrivial internally complete atomic Boolean algebra. For the reverse direction it suffices to require injectivity of the two-element algebra.

**Proof of the forward direction.** Fix j and h. For each atom c of C, evaluation at c after h is an ultrafilter U_c on A. Its image under j generates a proper filter F_c on B. Indeed any finite meet of its generators is j(a) for some a∈U_c; since a≠0 and j is injective, this meet is nonzero. The upward closure is admitted. BPI_int extends F_c to an ultrafilter on B, by the quotient argument in §28. This gives pointwise existence of extensions.

Uniformity does not require Functional Choice. BPI_int implies UFC by §26. Apply UFC to the nonempty field of all admissible extensions for each c, and use §33's evaluation sum to obtain a uniform extension K_c. Now define

    H(b) = join {c: c is an atom of C and K_c(b)}.

The joined family is admitted. Atomic complete primality shows that c≤H(b) iff K_c(b). The ultrafilter laws consequently give H(0)=0, H(1)=1, H(¬b)=¬H(b), and H(b∧d)=H(b)∧H(d). Since K_c extends U_c along j, we have c≤H(j(a)) iff c≤h(a) for every atom c; atomicity then gives H(j(a))=h(a). No preservation of arbitrary meets by H is asserted.

For the converse take C=2, let A=2, embed A by its unique unital map into any nontrivial Boolean algebra B, and set h=id_2. An extension H:B→2 is exactly an ultrafilter on B. Thus the two-element injectivity statement gives BPI_int. ∎

Combined with §§16, 25, 31 and 32, this yields a strict hierarchy over T, even with quantified Infinity and all Intensional Choice in the separating models:

    all complete subalgebra inclusions split by complete Boolean maps
      iff □Functional Choice
      strictly implies
    injectivity of complete atomic algebras for finite Boolean maps
      iff BPI_int
      strictly implies
    all complete subalgebra inclusions split by finite Boolean maps
      iff UFC iff UniformFreeUF.

The first separation is the ordered full-support model with fixed finite worlds: §31 supplies BPI_int, and the interval-selection obstruction supplies failure of Functional Choice. The second is the literature-dependent full-in-M construction of §32. In both splitting statements the range includes admitted complete subalgebra fields, not only entire type algebras. This distinction matters to the exact equivalences.

The middle statement must not be confused with requiring a retraction onto every arbitrary Boolean subalgebra of an atomic ambient algebra. That demand is generally false even in full ZFC models: a finite Boolean retraction from P(ω) onto its finite–cofinite subalgebra would fix every singleton, and hence preserve membership of every n in every input set. It would therefore be the identity on P(ω), which cannot have finite–cofinite range. The extension theorem instead requires the *target* to be internally complete and atomic and extends a given map into it.

## 35. Every admitted world permutation lifts through the type hierarchy

This is a generalization of the already recorded atom-transposition lift, not a new strengthening of T. In particular, finite transitivity or a swap of two atoms must not be advertised as an additional axiom.

Let π be an admitted permutation of the world-atom field. By §9 it induces an admitted complete Boolean automorphism P_t of the proposition algebra, characterized by

    P_t(p) = join {π(a): Atom(a) and a≤p}.

Its inverse is induced by π^{-1}. Set P_e to the identity on individuals. At each relational arrow type σρ define recursively

    P_(σρ)(X) = P_ρ ∘ X ∘ P_σ^{-1}.

This is notation for a λ-term: if σ=e, leave the individual argument unchanged; otherwise P_σ^{-1} is an admitted operator at relational type σσ. Thus no forbidden individual-valued arrow is inserted. The analogous recursion with inverses defines P_(σρ)^{-1}; βη and the inductive inverse equations prove that the operators are inverse bijections. At each fixed finite type only finitely many previously constructed operators are used, so λ-closure supplies the graph/operator at that type. No comprehension over a collection of all types is assumed.

These maps preserve application by construction. They fix the Boolean constants and operations because P_t is a Boolean automorphism. They fix equality predicates because each P_σ is bijective and equality has rigid values 0 or 1. They fix quantifier constants because complete Boolean preservation commutes with every admitted meet, and substitution by P_σ permutes the quantified domain:

    P_t(meet_x P_t^{-1}(F(P_σ x))) = meet_x F(x).

All families appearing here are admitted by λ-comprehension. They fix the background necessity constant since, over T, □p has value 1 exactly when p=1, and otherwise has value 0; P_t fixes 0,1 and preserves the equation p=1. Consequently the recursively defined family preserves every logical constant and all term formation. It is a logical automorphism of the unpointed intensional algebra.

The qualification “unpointed” matters. Atoms transform by P_t(a)=π(a), and evaluation satisfies

    π(a)≤P_t(p) iff a≤p.

Thus truth is preserved when the evaluation atom is transformed as well. A pointed actual-world structure is fixed only when π fixes its designated atom. Likewise a formula with parameters is preserved with those parameters transported; it need not be preserved while arbitrary distinguishing parameters are held fixed.

For example, if π preserves every coordinate proposition R_x, then its lift fixes R when individuals are fixed. Under S_e(R), distinct worlds have distinct coordinate profiles, so the only such π is the identity. Hence complete world symmetry of the underlying pure logic is compatible with a separating description R which has trivial world stabilizer. This distinguishes a structural automorphism theorem from a demand that every contingent parameter be invariant.

## 36. Individual permutations and pure equality-pattern normal forms

The lift in §35 also starts from any admitted rigid bijection f of the individual field, represented by its functional graph. Its inverse is represented by the converse graph. At arrows with individual input use relational binding instead of a forbidden e→e function term: if ρ has tuple of argument types ᾱ and final output t, define

    P_(eρ)(X)(x)(z̄) := exists y[f(y,x) and P_ρ(Xy)(z̄)].

There is exactly one preimage y, rigidly. Thus this formula is the pointwise expansion of conjugation by the inverse individual bijection, at every world, and gives the required admitted relation by λ-comprehension. All other inductive cases are as in §35. Quantification over individuals is preserved because f permutes their field. Consequently any admitted individual bijection and any admitted world permutation lift simultaneously, with the same qualification about transporting the evaluation atom.

Fix a pure parameter-free term R of finite individual arity n. For each equality pattern P on the n positions, write P(x̄) for its conjunction of required equalities and inequalities, and define the closed pure proposition

    θ_P := exists x̄[P(x̄) and R(x̄)].

At a fixed model every two tuples with the same equality pattern are related by a finite permutation of the individual field. A finite bijection between their ranges extends to a permutation of their finite union: extend the partial injective map to a bijection on that union by matching the two finite complements. Finite induction proves the required matching, without any general Choice. Extend that finite permutation by the identity off the union. Its graph is admitted and rigid. The lifted logical automorphism fixes R, and its proposition component is the identity if the world permutation is the identity. Thus R has exactly the same proposition value on the two tuples.

It follows that, over T,

    R(x̄) = disjunction over equality patterns P of [θ_P and P(x̄)].

Equality here is equality of proposition intensions; alternatively use the necessary biconditional. If a pattern is unrealizable, θ_P is false and its summand contributes nothing. The statement is per pure formula/term and per model: the coefficients θ_P remain closed pure sentences, and no uniform algorithm or theory deciding their truth is asserted. They may distinguish models with different cardinal or higher-type structures.

The coefficients are bivalent in each T-model. One route uses NPC for the pure closed θ_P. Another uses world transpositions fixing all individuals: they fix R(x̄), and a proposition fixed by every atom transposition cannot contain one atom while omitting another. Hence each R(x̄) is either 0 or 1. This reasoning is a consequence of the recorded atom-swap theorem and its general lift, not a new principle requiring every parameter to be invariant.

Two consequences clarify what Functional Choice does and does not canonically provide. Every pure unary individual property is empty or universal in a fixed model. If there are at least two individuals, no pure parameter-free strict linear order of the individual field exists: a transposition reverses an off-diagonal pair while leaving any such relation invariant, contradicting asymmetry and totality. Nor can a pure parameter-free graph choose one individual from every nonempty individual property. The universal individual property is fixed by every individual permutation, so its chosen point would have to be fixed by every transposition, which is impossible when another individual exists. These statements are compatible with □Functional Choice: it asserts existence of selectors and orders, whose extra parameters may break the symmetry, not a parameter-free canonical selector.

## 37. Intensional Choice is injectivity of the proposition algebra

For this section all objects are admitted nontrivial internally complete atomic Boolean algebras with rigid carrier fields and operation graphs. The morphisms are admitted **complete** Boolean homomorphisms, preserving every admitted family meet/join. Carrier fields, including relative rigid powerset fields, are allowed; restricting the category to whole type algebras would not automatically be equivalent.

In this admitted category the categorical monomorphisms are exactly the injective homomorphisms, and epimorphisms are exactly the surjective ones. If h identifies a≠a′, the two complete maps from the four-element Boolean algebra sending its generator to a and a′ witness failure of monicity. If a complete h:A→B is not surjective, its dual atom map is not injective; two distinct atoms of B with the same image yield different evaluations B→2 which agree after h, witnessing failure of epicity. Conversely set-theoretic injectivity and surjectivity imply cancellation immediately. These finite testing algebras and their maps are represented in T. Thus the projective/injective language below has its ordinary categorical sense, not a restriction to an unidentified subclass of epis or monos.

First record the exact world-choice translation. For each type σ, IC_σ is equivalent over T to the assertion that every rigid serial relation Q⊆Atoms(t)×D_σ has an admitted rigid single-valued selection on the world-atom field. Given Q, define the intension

    F(x) := exists a[Atom(a) and a and Q(a,x)].

It is necessarily instantiated. An IC selector G≤F yields the rigid world selection Q'(a,x) iff a≤Gx. Conversely, from a necessarily instantiated F, the rigid relation Q(a,x) iff a≤Fx is serial. Complete primality of atoms for the admitted family {Fx:x∈D_σ} proves seriality; no external distribution over an unrepresented family is needed. A world-indexed selector Q' defines

    G(x) := join {a:Atom(a) and Q'(a,x)},

and G≤F is necessarily uniquely instantiated. Each construction uses admitted comprehension and the strong world atoms of T.

**Theorem 37.1.** Over T, all-type Intensional Choice is equivalent to injectivity of the proposition algebra B_t in this category of complete atomic algebras and complete homomorphisms.

For the forward implication take a complete Boolean embedding j:A→B and a complete Boolean homomorphism h:A→B_t. The atomic duality of §9, applied to these rigid represented fields, turns j into a surjection

    f:Atoms(B)→Atoms(A),

and h into a map

    g:Atoms(t)→Atoms(A).

The pullback relation f(b)=g(w) is a rigid serial relation indexed by worlds. Intensional Choice at the carrier type of B selects b=k(w) uniformly. The complete homomorphism H:B→B_t dual to k then satisfies H∘j=h. All fiber predicates, atom maps and inverse-image homomorphisms are admitted.

Conversely, given a rigid serial relation Q⊆Atoms(t)×D_σ, let Z be its field of coded pairs (w,x). Use the rigid singleton relation λa y(a=w∧y=x) as its pair code. The admitted relative rigid powerset algebra P_int(Z) is internally complete and atomic, with singleton-pair atoms. The first-coordinate projection Z→Atoms(t) is surjective. Its inverse-image map is therefore a complete Boolean embedding

    j:B_t→P_int(Z),   j(p)={ (w,x)∈Z : w≤p }.

Injectivity of B_t, applied to h=id_(B_t), yields a complete Boolean retraction H:P_int(Z)→B_t. By atomic duality, H is a section of the first-coordinate projection. Its second coordinate is an admitted world-indexed choice function for Q. The preceding translation gives IC_σ. This works for each σ, proving the equivalence. ∎

There is an instructive asymmetry. Every object of this complete-homomorphism category is already projective in T. Any surjective complete homomorphism has a section by §18: its dual atom map is injective, and a left inverse uses its unique inverse on the image and one default atom elsewhere. Composing that section with any given morphism supplies a projective lift. On the other hand, all objects are injective exactly when □Functional Choice holds, by the complete-retraction equivalence of §16.

Thus the same category gives precise definitions at three strengths:

    T: every complete atomic algebra is projective;
    T + IC_all: the proposition algebra is injective;
    T + □Functional Choice: every complete atomic algebra is injective.

This is distinct from §34, whose morphisms preserve only finite Boolean operations and whose input algebras may be non-atomic. In particular, injectivity of 2 for *finite* Boolean maps is BPI, whereas injectivity of 2 for *complete* maps between complete atomic algebras is already available in T: a single target atom asks for a witness in just one nonempty fiber, not a uniform choice over a family.

### Additional nontrivial-world variant of §32

The literature-dependent finiteRet-without-BPI model can have genuine contingency. Replace its singleton W by the fixed two-element set {0,1} in M, put D_t=P^M(W), and keep all higher arrows as M-function sets. Interpret □ by universal quantification over W. The same set-theoretic comprehension induction verifies λ and quantifier closure. A relational Boolean atom is the singleton of a world and an argument tuple, so Atomicity holds at every relational type; freezing an admitted graph at either world gives Plenitude. Intensional Choice holds at every type because M proves choice from two nonempty sets by elementary finite logic; the two chosen witnesses define the selector intension. Rigid UFC kernels and the coded bad Boolean algebra are unchanged. Thus §32's separation may be stated with two worlds, quantified Infinity, all Intensional Choice, finite Ret_all, and failure of BPI_int/FineUF.

### Pure existential principles need not have pure selected witnesses

The last two symmetry arguments also distinguish the simplicity of an existential axiom from definability of one selected witness. Here “pure” means a parameter-free term in the original logical signature; an added designated object or a specified generator family is additional data.

There is no pure universal-extension witness R of type et when the individual field is nonempty. World permutations fixing individuals fix every value Rx of a pure R, so each Rx is bivalent and the world-profile map is constant. The admitted empty and universal individual fields are distinct, so a constant profile map cannot realize both. This does not refute the existential principle EU_e or its compatibility with Functional Choice; it excludes a pure term selecting its witness.

If there are at least two world atoms, there is no pure complete bivalent evaluator E:t→t. By §9 such an evaluator determines its unique world atom by the pure term

    w = forall p[Ep -> p].

Every world permutation would fix this pure w, while a transposition of w with another atom would move it. This is a contradiction. Equivalently, pure closed propositions are bivalent under T and cannot be one proper world atom. Again, the theorem that every world atom has its evaluator, and the availability of choice-selected evaluators, do not produce a parameter-free canonical evaluation world.

## 38. One canonical membership inclusion per type suffices

This is an equivalent definition audit, not an additional principle. Fix a type σ. Let P_σ^+ be the admitted rigid field of nonempty rigid σ-properties, and let

    M_σ = { (X,x) : X∈P_σ^+ and Xx }.

Ordered pairs have the rigid singleton-relation code described above. The first projection π:M_σ→P_σ^+ is an admitted surjection. Let P_int(Y) denote the relative rigid powerset algebra of a represented rigid field Y. The canonical inverse-image map

    j_σ : P_int(P_σ^+) → P_int(M_σ),
    j_σ(B)(X,x) iff B(X),

is a complete Boolean embedding. Both algebras and this map are defined in the existing logical language, using admitted properties only.

A complete Boolean retraction of j_σ is equivalent to a choice function on all nonempty rigid σ-properties. Under atomic duality its atom map is precisely a section X↦(X,c(X)) of π. Conversely a section gives the complete retraction A↦[X↦A(X,c(X))]. Composing c with the represented fiber map of an arbitrary rigid serial relation yields ordinary choice for every input type and output σ. Rigidification supplies the corresponding actual nonrigid relation instance over T. Consequently

    every j_σ has a complete Boolean retraction, for all σ,
      iff □Functional Choice.

A finite Boolean retraction of j_σ is equivalent to a universal ultrafilter-choice operator K_σ: for every X∈P_σ^+, K_σ(X) is an ultrafilter on the rigid σ-properties and contains X. To see this from a retraction H, evaluate H at the singleton atom X of its target and pull along the second-coordinate inverse-image map. Explicitly,

    K_σ(X,P) iff H({(Y,y)∈M_σ:Py})(X).

This is an ultrafilter because H and evaluation preserve finite Boolean operations. It contains X because the fiber π^{-1}(X) is contained in the second-coordinate event for X, and H fixes the image of j_σ.

Conversely, given K_σ define

    H(A)(X) iff K_σ(X, {x:Xx and A(X,x)}).

Because K_σ(X) contains X, it respects relative complements inside X and finite intersections. Hence H is a Boolean homomorphism and H∘j_σ=id. Its graph is admitted by one comprehension formula. Composing K_σ with x↦R_x gives an ultrafilter kernel for any represented serial relation with output type σ. Therefore

    every j_σ has a finite Boolean retraction, for all σ,
      iff UFC iff finite Ret_all iff UniformFreeUF.

Thus both full Functional Choice and its ultrafilter weakening can be stated using a distinguished pure membership inclusion at each type, without quantifying over all subalgebra fields. The inclusion itself is canonical; a chosen retraction need not be canonical or pure. For σ=e and at least two individuals, no pure finite retraction can serve this role: on a two-element subset X its induced ultrafilter is principal, and swapping X's two members fixes X while moving the selected point.

## 39. Fineness has a simpler whole-type formulation and uniform restriction

The FineUF schema can be restricted to whole type domains without loss. For each σ ask for an admitted ultrafilter V_σ on Fin(D_σ) containing every cone C_x={F:x∈F}. Given such a V_σ and any admitted rigid I⊆D_σ, define the restriction map

    r_I:Fin(D_σ)→Fin(I),   r_I(F)=F∩I.

Finite intersection with a subfield is internally finite by Frege induction. The map is admitted uniformly in I. Push V_σ forward along r_I to obtain

    V_I(A) iff V_σ({F∈Fin(D_σ):A(F∩I)}).

This is an ultrafilter on Fin(I). For each i∈I, the inverse image of its cone is exactly C_i, so V_I is fine. The formula is uniform over all admitted fields I of this type, and hence over any represented family of such fields. The empty field causes no problem: its finite-subset field is the singleton {∅}.

Consequently FineUF already supplies uniform fine ultrafilters on families of subfields of a fixed type, without UFC. The more general ultrafilter-candidate averaging in §33 remains valid, but is unnecessary for this particular uniformization. This does not erase the separation in §29: obtaining a fine ultrafilter on finite subsets does not select a point, or a local ultrafilter, from each arbitrary nonempty fiber.

Combining §§26, 28 and 38 gives a particularly economical exact package: BPI_int consists of finite Boolean retractions of the canonical membership inclusions j_σ, together with one fine ultrafilter V_σ on the internally finite subfields of each whole type domain. The first part chooses generalized local witnesses; the second coordinates internally finite sets of requirements. Both parts are independent over T by §§29 and 32, with the latter direction retaining its explicit published-model dependency.


## 40. A sharper factorization: fine ultrafilters and finite choice

Write ACfin_all for ordinary functional choice restricted to represented rigid serial relations whose nonempty output fibers are internally Frege-finite. Input and output types are arbitrary; input pairs and function graphs are represented by rigid relational codes. Over T, rigidification and NPC translate between this rigid schema and its boxed counterpart. No assertion here identifies internal finiteness with external finiteness.

**Theorem.** Over T,

    BPI_int iff FineUF + ACfin_all.

The forward implication follows from §§25–28: BPI_int supplies UFC and FineUF, and a uniformly chosen ultrafilter on a finite nonempty fiber has a unique principal point, yielding ACfin_all. For the converse it suffices by §28 to prove FineUF + ACfin_all ⇒ UFC. There are two direct internal constructions.

### 40.1 Finite families of partial choice graphs

Let R⊆D_σ×D_ρ be represented, rigid and serial. Let J be the rigid field of all internally finite partial single-valued R-choice graphs. Each member g of J is a rigid relation of type σρt, its domain is internally finite, and g(x,y) implies R(x,y). The empty graph belongs to J. FineUF gives an admitted fine ultrafilter V on Fin(J).

For F∈Fin(J) let Cov(F,x) mean that some g∈F is defined at x. On the represented field of pairs (F,x) satisfying Cov, the value field

    A_(F,x) = { y : ∃g∈F g(x,y) }

is nonempty and internally finite. Its finiteness follows by Frege induction on F, adding at most one value for each new single-valued g. ACfin_all uniformly chooses c(F,x)∈A_(F,x). Extend c to uncovered pairs using one fixed y₀∈D_ρ; choosing this one default is elementary existential reasoning, not a choice schema.

For each x, seriality supplies some y with R(x,y), so the singleton graph {(x,y)} belongs to J. Its fine cone is contained in {F:Cov(F,x)}. Thus the coverage event is V-large for each x. This proof uses a witness for one arbitrary x; it does not choose singleton graphs uniformly in x.

Define, for an admitted rigid ρ-property P,

    K_x(P) iff V({F : Cov(F,x) and P(c(F,x))}).

Since coverage is V-large, this is the pushforward of V under c(-,x), unaffected by the chosen default. It is an ultrafilter, and it contains R_x because every chosen covered value satisfies R. The displayed formula represents K uniformly in x and P. This proves UFC.

All fields in this argument are defined by formulas from R. Internally finite F, partial graphs and their finite value images are used throughout; there is no external enumeration, external powerset, or preselected family of finite partial choice functions.

### 40.1a A simpler version: finite sets of relation pairs

The preceding proof can be shortened without changing its assumptions. Let J be the rigid field of coded pairs (x,y) satisfying R(x,y), and let V be a fine ultrafilter on Fin(J). For F∈Fin(J), put

    Cov(F,x) iff ∃y [(x,y)∈F],
    A_(F,x) = {y:(x,y)∈F}.

On covered pairs (F,x), A_(F,x) is internally finite and nonempty, directly by finite projection. ACfin_all supplies c(F,x) in this value field; use one default elsewhere. For every x, seriality gives some (x,y)∈J, whose fine cone is contained in the coverage event. Thus coverage is V-large, with no uniform prior selection of y. The same displayed pushforward formula for K_x in §40.1 gives an admitted ultrafilter concentrated on R_x.

This version avoids the field of partial functions altogether. The original construction is retained above, but finite sets of relation pairs give the more economical proof and definition audit. Both use only one fine ultrafilter on the relevant admitted field, finite-fiber choice, and comprehension.

### 40.2 Finite partitions by truth patterns

A second proof can be more perspicuous. Let P_ρ be the rigid field of admitted rigid ρ-properties. Fix a fine ultrafilter V on Fin(P_ρ). For x and F∈Fin(P_ρ), partition the nonempty field R_x by agreement on every property in F. Represent each cell by its characteristic ρ-property, and let Cells(x,F) be the field of nonempty cells. It is internally finite and nonempty: begin with the single cell R_x and, on adjoining a property, split each current cell into its intersections with that property and its relative complement, discarding empty pieces. Frege induction proves the claim. The *field of cells* is finite; the cells themselves need not be finite.

ACfin_all selects one cell C_(x,F)∈Cells(x,F), uniformly in x and F. Put

    K_x(P) iff V({F : C_(x,F)⊆P}).

Every selected cell is nonempty and contained in R_x. Hence K_x contains the relative top R_x and rejects the empty property. The event for P∩Q is exactly the intersection of the events for P and Q. On the V-large cone {F:P∈F}, each selected cell lies either in P or in its complement, exclusively. Therefore K_x decides every P, respects complements, and is an ultrafilter containing R_x. Again the formula is uniformly admitted. No element of a cell is selected.

This proof also exhibits why finite choice is precisely the additional resource here: it chooses a finite truth-pattern cell, while fineness makes the resulting decisions coherent over any fixed finite set of tests.

### 40.3 Strictness and source status

Both factors are independent over T. The explicit finite-pair-flip construction of §29 satisfies FineUF and fails ACfin_all: choosing one member of every named pair would require an unsupported orientation. The model transferred in §32 satisfies UFC, hence ACfin_all, but fails FineUF. That latter separation retains its explicit dependence on the published ZFA model existence in Howard–Tachtsis, Remark 4; no underlying permutation construction has been reconstructed in this report.

The equivalence is an internal typed derivation presented here, not a historical novelty claim. Howard–Tachtsis, *On the minimal cover property in ZF*, Topology and its Applications 173 (2014), 94–106, DOI 10.1016/j.topol.2014.05.021, Theorem 10 proof (1), explicitly recalls the classical equivalence of BPI with Rado's selection lemma plus choice for finite sets, citing Rav. The next section identifies the exact Rado principle corresponding to FineUF, without appealing to an unexamined formulation.

## 41. FineUF is exactly the indexed Rado selection principle

Fix a rigid field I⊆D_σ, a rigid family of internally finite nonempty fields A_i⊆D_ρ, and an *already supplied admitted family of local choices*

    g(F,i)∈A_i whenever F∈Fin(I) and i∈F.

The Rado principle RL asks for an admitted global choice h(i)∈A_i such that

    ∀F∈Fin(I) ∃F'∈Fin(I)
       [ F⊆F' and ∀i∈F h(i)=g(F',i) ].

All quantifiers range over admitted objects. The local data g are part of the premise: replacing them by the weaker statement that each finite F has some choice graph changes the principle. In fact g({i},i) already supplies an ordinary choice for this particular family; RL asks for a global choice with the stated coherent finite approximation property.

Let RL₂ restrict every A_i to the fixed two-element rigid field {⊥,⊤}⊆D_t. Then over T,

    FineUF iff RL iff RL₂.

### FineUF implies RL

Take a fine ultrafilter V on Fin(I). For each i, the cone C_i={F:i∈F} is V-large. Its partition according to the value g(F,i) has the internally finite set A_i of possible values. Internal finite primeness of V gives a unique a∈A_i for which

    {F : i∈F and g(F,i)=a}

is V-large. Define h(i)=a by this unique-value condition; the graph is admitted, and no choice principle is required to select unique values. For any F∈Fin(I), internal finite-intersection closure of V makes the intersection of these large events over i∈F large, hence nonempty. Any F' in that intersection contains F and satisfies the required simultaneous agreement. Internal finite-intersection closure follows by Frege induction from the ordinary binary filter law.

RL implies RL₂ by specialization.

### RL₂ implies FineUF

Let I⊆D_σ be any admitted rigid field and put Z=Fin(I). If I is empty, Z={∅} and its principal ultrafilter is fine. Suppose I is nonempty and fix one i₀∈I. Let B=P_int(Z), the admitted rigid event field on Z.

Form the represented tagged disjoint union K of an I-copy, with labels r_i, and a B-copy, with labels e_P. This does not require a new sum type. For example, use rigid singleton-relation codes of triples (b,i,P), with b∈{⊥,⊤}; represent r_i by (⊥,i,P₀) for the fixed empty event P₀, and e_P by (⊤,i₀,P). Equality of codes gives precisely equality within the appropriate tagged copy.

For F∈Fin(K), let

    u_F = { i∈I : r_i∈F }.

This is internally finite, by finite projection. Supply the following binary local-choice table on F:

    g(F,r_i)=⊤;
    g(F,e_P)=⊤ iff P(u_F).

The graph is admitted uniformly in F and the label. RL₂ gives h:K→{⊥,⊤} with the finite approximation property. Define

    U(P) iff h(e_P)=⊤.

This is an ultrafilter on B. To verify any of the top, bottom, complement or binary-intersection laws, take a finite F containing the corresponding event labels. The approximation property supplies F'⊇F for which all those h-values are simultaneously the truth values of the events at the single point u_(F')∈Z. Point evaluation obeys the Boolean laws, so the same laws hold for U.

For i∈I let C_i={u∈Z:i∈u}. Apply approximation to the two-label field {r_i,e_(C_i)}. The resulting F' contains r_i, so i∈u_(F'); therefore g(F',e_(C_i))=⊤ and U(C_i). Thus U is fine. The construction uses finitely many labels for each Boolean law, so it inserts no external propositional compactness or formula-syntax coding.

Together with §40 this yields the concise exact decomposition

    BPI_int iff RL₂ + ACfin_all iff RL + ACfin_all.

The FineUF/Rado factor already handles coherent finite approximation when the local choices are supplied. ACfin_all supplies the missing uniform choice of finite truth-pattern cells. This is an equivalence of schemas in the fixed typed framework, with no new syntax or infinitary proof rule.


## 42. Uniform complete evaluators measure well-orderability of the atom field

The existence of a complete bivalent evaluator is very different from a single admitted function choosing one for every nonzero input. At B_t write UCE_t for the existence of S:t→(t→t) satisfying

    ∀p≠⊥ [ CE_t(S p) and (S p)(p)=⊤ ],

where CE_t means unital Boolean homomorphism into {⊥,⊤}, preserving every admitted rigid meet. The zero input is unconstrained. All arrows displayed here return relational types and therefore exist in the original type grammar. The completeness requirement is internal, as in §9.

**Theorem.** Over T,

    UCE_t iff the rigid field W=Atoms(t) is internally well-orderable.

Indeed §9 associates to S(p) its unique world atom c(p) below p. Every admitted nonempty rigid field A⊆W is exactly the atom field below p_A=∨A; hence A↦c(p_A) is a represented choice function on *all* nonempty subfields of W. The internal Zermelo argument in §30 well-orders W. Conversely, a well-order of W gives the least atom c(p) below every nonzero p; set S(p)=E_(c(p)). At p=⊥ use the evaluator of the least atom of W, which exists because W is nonempty. These assignments are represented by unique-value comprehension.

Thus UCE_t implies Ret_t: choose the least atom in each block of a represented world partition, and use §16. The converse fails. UCE_t also has a different direction of indexing from IC_all: it selects worlds from arbitrary nonempty world subfields, whereas IC_all selects arbitrary typed objects from families *indexed by worlds*.

### 42.1 Two explicit separations

In the full finite-support hierarchy with one individual and G=Sym(W) acting on an externally infinite W (§§2 and 4), IC_all holds and UCE_t fails. A supported well-order of W is impossible: a transposition of two worlds outside its finite support preserves the supposed order but reverses the order of those two points. The same argument directly forbids a supported choice function on all two-element world fields.

This model nevertheless satisfies Ret_t. Let E be an admitted equivalence relation on W with finite support S, and put O=W\S. The full symmetric action on O forces E restricted to O to be either equality or the universal relation. In the equality case no point of O can be E-related to a point of S: invariance would then relate that point of S to every point of O, contradicting equality on O. Thus all O-classes are singletons, and only finitely many classes inside S remain; choose one representative of each. The resulting transversal is O together with a finite subset of S and is supported. In the universal case O lies in one cofinite E-class; choose one u∈O for that class and one representative of each remaining class, all lying in S. This is a finite supported transversal. Consequently every represented world partition has an admitted transversal, so Ret_t follows from §16. This proves

    T + IC_all + Ret_t does not imply UCE_t.

For the other direction take fixed worlds W=ℕ and individuals E=ℕ×{0,1}, with G the group of independent flips of the named individual pairs. Use the full finite-support hierarchy of §2; G fixes every world. Therefore D_t=P(ℕ), and the usual order of world atoms is an admitted empty-support well-order. UCE_t and Ret_t hold. But the empty-support relation that, at world n, allows precisely the two individuals (n,0),(n,1) has no admitted selector: outside a selector's finite support, the flip of pair n fixes the world and the relation while moving its selected individual. Hence IC_e fails. The same λ/comprehension, Plenitude and atomicity verifications as §2 apply. Thus

    T + UCE_t + Ret_t does not imply IC_e.

Both are direct model constructions, with no appeal to the literature-dependent ZFA separation in §32. In particular UCE_t is strictly stronger than Ret_t and independent of IC_all over T.

### 42.2 Uniform evaluators at relational types recover full Functional Choice

For B_(σt), define UCE_(σt) by the analogous admitted selector of complete bivalent evaluators on every nonzero σ-property. Its atoms are exactly the codes (w,x), equivalently w∧haecceity_x, with w∈W and x∈D_σ. The same proof shows that UCE_(σt) is equivalent to internal well-orderability of this admitted atom field.

Equivalently, at this fixed σ it says that both W and D_σ are internally well-orderable. A well-order of the product restricts to each factor after fixing one element of the other; conversely the lexicographic product of their well-orders is an admitted well-order. Every nonempty admitted subset of the product has a least first coordinate, and then a least second coordinate in that fiber, which proves this internally without external completeness.

There is also a direct choice extraction. Fix one world atom a. For any nonempty rigid σ-field X, the relation a∧X is nonzero. Its selected evaluator is generated by a unique atom a∧haecceity_x below a∧X; this determines a unique x∈X. Uniformity in X gives universal point choice at output type σ. Conversely, full Functional Choice chooses an atom below each nonzero relation and hence chooses its complete evaluator. Consequently

    UCE_(σt) for every σ iff □Functional Choice.

No new evaluator primitive or infinitary conjunction syntax has been added: all maps and meets are admitted constructions in the fixed language. Bare evaluator density remains available in T by atomicity; the additional strength lies precisely in assembling the witnesses into one admitted selector. Uniform existence also does not supply a parameter-free pure selected witness, as §§24 and 37 show.


### 42.3 Universal profiles plus ordered worlds select individuals without IC

EU_σ + UCE_t implies universal point choice at output type σ, without assuming IC_σ. Let R witness EU_σ and use UCE_t to well-order W. For each admitted rigid σ-property X, choose the least world whose R-profile is X. This is a unique-value definition and gives an injection P_σ→W; transporting the well-order therefore well-orders the admitted rigid profile field P_σ. The singleton-profile map x↦haecceity_x embeds D_σ into P_σ, so D_σ is well-orderable. Choosing the least member of every nonempty rigid σ-field gives arbitrary-input relational choice with output σ, and rigidification handles current nonrigid relations.

Equivalently, order each x by the least world whose R-profile is its singleton. This avoids any preliminary selection of an individual at a world. This uses the well-ordering of worlds to dispense with IC in the earlier EU_σ + IC_σ + Ret_t bridge. At σ=e,

    EU_e + UCE_t ⇒ individual-output Relational Choice,
    EU_e ⇒ (UCE_t iff UCE_(et)).

The second equivalence follows from §42.2 and the preceding derivation of a well-order of E; its reverse implication needs only nonemptiness of E. No assertion of all-type Functional Choice follows from the individual-output conclusion alone.


### 42.4 Uniform retraction operators give the same distinction

UCE_t is equivalent to the existence of one admitted operator assigning a complete Boolean retraction H_A:B_t→A to every represented internally complete Boolean subalgebra A⊆B_t. In fact it suffices to assign these retractions uniformly for the subalgebras

    A_p={⊥,p,¬p,⊤},  p≠⊥.

Repeated elements are harmless when p=⊤. The element p is an atom of A_p. Evaluating H_(A_p) at this relative atom gives

    S(p)(q)=⊤ iff p≤H_(A_p)(q).

This is a complete bivalent evaluator containing p, so the uniform retraction assignment yields UCE_t.

Conversely use UCE_t to choose an atom c(b)≤b for each nonzero proposition b. For every complete subalgebra A and each relative atom b of A, use c(b) as its representative. Define uniformly

    H_A(q)=∨{b∈Atoms(A):c(b)≤q}.

The subalgebra/partition duality of §1 and §16 proves that this is a complete Boolean retraction onto A. All relative-atom fields and joins are admitted, and the displayed formula is uniform in A. On invalid subalgebra codes the operator may take the identity map as a default. Thus the gap between Ret_t and UCE_t is exactly the passage from separate existence of retractions to one admitted selector of them; it is not a change from finite to complete preservation.

There is a parallel finite-operation statement. An admitted operator choosing finite Boolean retractions for all complete subalgebras of B_t is equivalent to an admitted function choosing, for every nonzero p, a finite bivalent evaluator containing p. Under B_t≅P_int(W), this is universal ultrafilter choice on nonempty admitted world subfields. The forward proof again uses A_p; conversely choose an ultrafilter K_b concentrated on each block b and set

    H_A(q)=∨{b∈Atoms(A):K_b(q)}.

Finite Boolean preservation and H_A|A=id follow from the blockwise ultrafilter laws. The finite version need not choose actual atoms. Neither uniform operator is required to be pure or invariant under all automorphisms.


### 42.5 The purity obstruction requires complete evaluation

In the Sym(W) finite-support model of §42.1, with W infinite, there is a pure finite Boolean evaluator:

    E(p) := not Fin({w:Atom_t(w) and w≤p}).

Here Fin is the internally Frege-finite predicate; the displayed term uses only the original logical vocabulary and its pure definitions. In this model D_t is the finite–cofinite algebra and internal finiteness is standard (§3). Therefore E(p)=⊤ exactly when p is cofinite. This defines a nonprincipal ultrafilter and hence a unital finite Boolean homomorphism B_t→{⊥,⊤}; it is invariant under all world permutations.

It is not complete. The admitted empty-support family {¬w:Atom_t(w)} has meet ⊥, while E sends every member to ⊤. Thus a canonical pure finite evaluator can exist even though no pure complete evaluator exists. This is a model-specific verification of the displayed pure term, not a theorem that the term is a Boolean evaluator in every T-model. The complete-preservation hypothesis in §§9, 24 and 37 is essential.


## 43. Independent audit of the generic Boolean Henkin boundary model

The construction is in the companion `structural-mixing-models.md`, §31; this section records an independent audit, not a second construction or a literature attribution. It is a direct ordinary-ZFC construction using a countable M≺H_θ, not an assumption of a countable transitive ZFC model.

The highest-risk closure step passes. For each M-coded full-domain family f, its Boolean join q belongs to M. Genericity meets the M-coded dense set of nonzero conditions lying below ¬q or below some f(x); elementarity supplies an M-witness x in the latter case. Therefore q is true at a generic world exactly when some admitted instance is true. The dual argument gives universal quantification. This inducts through arbitrary finite typed formulas, and definability plus elementarity supplies the full-domain lambda maps whose restrictions are admitted. Distinct M-functions remain distinct on M-inputs by elementarity, so intensional identity is faithful.

The choice calculation also passes. Necessary seriality on admitted inputs reflects to full-domain seriality by elementarity. The rowwise Boolean antichain construction supplies a relation with disjoint rows of the same Boolean join, and genericity turns those rows into actual unique values. This yields the stated modalized relational selection. It does not supply an object-valued operation. Such an operation for the truth-answer relation U(p,q) would code an M-ultrafilter whose trace equals the generic world, contradicting the M-coded dense set B⁺\V. Rigid-coded choice and BPI are separately valid by ordinary full-domain choice followed by elementarity; no rigidification of arbitrary actual generic extensions is asserted.

For Infinity, the rigid successor graph on the individual domain ℕ directly witnesses a proper self-injection. This avoids needing a separate analysis of the finite-cardinality class in this model. The construction thus correctly separates uniform finite Boolean evaluators and extensive relational/rigid choice from the complete evaluator density equivalent to T.
