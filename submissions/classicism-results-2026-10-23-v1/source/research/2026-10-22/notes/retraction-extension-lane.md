# Relational extension and Boolean homomorphism research

Original arguments by OpenAI Codex, 22 October 2026. Scratch research, not independently checked; no database or Lean edits. The fixed theory is C. The current comparison baseline is **C + □Functional Choice** (earlier instructions used C + □Plenitude). All new conclusions below are ordinary mathematical arguments, not claims from the cited source literature. The familiar Boolean-extension argument is reconstructed here; no novelty claim is made.

## Standing distinctions and recorded input

Types are the map's relational types. Write B_σ for the Boolean algebra at a relational type σ, with its algebraic order and Boolean operations. Identities and Boolean equations are identities of entities, not merely coextension at the evaluation point. A subalgebra A is a property A^{σt}; its membership, closure, and homomorphism hypotheses below are **unboxed** unless explicitly boxed. The codes A and B may be distinct but coextensive; our orders on graph codes are preorders.

The proved-only Engine was consulted with optional assumptions in the premise set, not its background. It confirms □Functional Choice ⇒ Zorn, Boolean Completeness, Plenitude, □ND, and BF; □Plenitude alone already implies Functionality via □ND ⇒ BF ⇒ Functionality. Relevant source records include `transversal-choice-r-implies-zorn-r`, `c5-and-actuality-imply-completeness`, `necessary-nd-implies-bf`, and `barcan-r-implies-functionality-r`. Definitions are `background.md`, `zorn-r.yaml`, `boolean-completeness-r.yaml`, and `plenitude-r.yaml`.

Uniform unboxed choice of a unique described relational entity is just Plenitude at input type τt. Consequently ordinary pointwise compatible gluing and partial-map extension, including operators performing those constructions, should not be counted automatically as additional principles. Exact uniqueness of an operation follows from Functionality, which the boxed benchmark already has.

## 1. Internal Boolean homomorphism extension

**Theorem (Sikorski form).** Suppose A is an actual Boolean subalgebra of B_σ and h is an actual Boolean homomorphism from A into B_τ. Boolean Completeness at τ, Zorn at graph type στt, and Plenitude at input σ/output τ suffice for an operation H^{στ} which is a Boolean homomorphism on all B_σ and agrees with h on A. More generally the target may be a predicate C⊆B_τ which is a Boolean subalgebra and internally complete in its own order.

Here “h is a homomorphism on A” means h0=0, h1=1, h(¬a)=¬h(a), and h(a∧b)=h(a)∧h(b) for a,b∈A. One may start with a single-valued graph instead of an operation h.

**One-generator extension lemma.** Let D⊆B_σ be a subalgebra with a homomorphism f into a complete target C, and let b∈B_σ. Let

    c = sup_C { f(a) : a∈D and a≤b }.

This property of C is definable from the graph of f, so internal completeness suffices. For a∈D:

* a≤b implies f(a)≤c by the supremum property.
* a≤¬b implies f(a)≤¬c. Indeed for every d∈D with d≤b, a∧d=0, hence f(d)≤¬f(a); the supremum property gives c≤¬f(a).

The subalgebra D[b] consists of the elements (a₁∧b)∨(a₀∧¬b), with a₀,a₁∈D. Define

    f'((a₁∧b)∨(a₀∧¬b)) = (f(a₁)∧c)∨(f(a₀)∧¬c).

This is a definable functional graph. To prove well-definedness, equality of two displayed representations gives (a₁△a'₁)∧b=0 and (a₀△a'₀)∧¬b=0. The preceding two bullets then give f(a₁)∧c=f(a'₁)∧c and f(a₀)∧¬c=f(a'₀)∧¬c. Boolean operations act coordinatewise on the two disjoint components, so f' preserves 0,1, complement, and meet. Taking a₀=a₁=a proves extension of f; taking a₁=1,a₀=0 proves f'(b)=c.

**Zorn step, with types and coextension controlled.** Work at the type of graph relations P^{στt}. A valid P is an actual single-valued partial graph whose domain is a Boolean subalgebra containing A, whose range lies in C, which is a homomorphism on its domain, and which extends the initial graph h on A. Such graphs exist. For valid graphs use actual graph inclusion P⊆Q. This is only a preorder on intensional codes, and the conclusion needed is maximality up to reverse inclusion.

The recorded Zorn schema quantifies over an entire type, not an arbitrary subtype. Extend the order to all graph codes by declaring invalid codes below every code, and valid P below Q exactly when Q is valid and P⊆Q. The result is a preorder. Given a chain, take the actual union of its valid members together with the fixed initial graph. If the chain has any valid member it already contains the initial graph; otherwise the initial graph alone is used. Chain comparability makes the union single-valued. Any finitely many arguments relevant to a Boolean homomorphism law occur together in one chain member, so the union is a partial homomorphism on a subalgebra. It is an upper bound of every chain member, including invalid ones. The union is expressed by existential quantification over graph codes, hence is an admitted relation. A maximal code is valid (an invalid code lies strictly below every valid one). If its domain omits b, the one-generator lemma gives a strictly larger valid graph. Thus the maximal graph is total. Plenitude turns it into an operation H.

**Scope.** No optional premise is necessitated. The argument proves a C-implication from finitely many specified instances of Completeness, Zorn, and Plenitude. Necessitate that discharged implication and use K for the boxed version. Therefore □Functional Choice entails the boxed Boolean-extension schema. This is a substantial structural consequence of the benchmark, not a genuine extra axiom.

## 2. Retraction criterion and countermodels

A Boolean retraction onto A⊆B means a total Boolean homomorphism r:B→B with range contained in A and r(a)=a for a∈A.

**Theorem.** If B is internally complete, then, under the extension theorem's Zorn and Plenitude assumptions,

    A admits a Boolean retraction from B  iff  A is internally complete.

Forward: given any represented S⊆A, let b=sup_B S. Then r(b)∈A and is an A-upper bound because r is monotone and fixes S. If a∈A is any upper bound of S, b≤a, so r(b)≤r(a)=a. Thus r(b)=sup_A S. No preservation of infinite joins by r was assumed. Reverse: use the extension theorem with complete target A and initial identity homomorphism on A.

**Explicit ordinary classical counterexample.** In a full one-world model with individuals N, B_e→t=P(N). Its finite/cofinite Boolean subalgebra A has no retraction. If r fixed A and were a Boolean homomorphism P(N)→A, then for every n, {n}∧r(S)=r({n}∧S), so n∈r(S) iff n∈S; hence r(S)=S, impossible for S infinite and coinfinite. Equivalently, the family of even singletons has no supremum in A: any cofinite upper bound can have a further odd point removed.

All relevant predicates and operations exist in this full model, and it satisfies □Functional Choice. Thus “every Boolean subalgebra is a retract” is a genuine additional principle, not a consequence of the benchmark. It holds in full models all of whose type domains are finite, including full nontrivial finite-group action models, because every finite Boolean subalgebra is complete and the extension theorem applies. This gives consistency with □Functional Choice and nontrivial modality. Section 14 strengthens this observation to an exact internal finiteness equivalence under the benchmark.

## 3. Modal extension collapses contingency

Consider **Modal Boolean Extension**:

    ∀A^{σt} h^{στ}.
      □(Subalg(A) ∧ Hom_A(h))
        → ∃H^{στ}. (□Hom(H) ∧ □∀x^σ(Ax → Hx=hx)).

This asks for one homomorphism satisfying the partial specification at every possibility, unlike the boxed local extension theorem □∀A h(...→∃H...).

**Theorem.** Over C+□Functional Choice, Modal Boolean Extension is equivalent to Extensionality.

**Sharper scope.** The forward collapse below needs only unboxed Plenitude, which supplies ND, and the single Modal Boolean Extension instance σ=(tt)t, τ=t. The finite domain descriptions do not require BF or domains to be fixed. The full equivalence also holds over unboxed Functional Choice: FC gives Zorn and Plenitude, while Extensionality gives Boolean Completeness (both routes were checked in the proved-only Engine), so the converse uses §1 after modal collapse.

**Fixed finite algebraic witness.** At type tt use the three C-provably distinct closed operations k₀=λp.⊥, k₁=λp.⊤, and i=λp.p. At source type σ=(tt)t, let a=λx(x=k₀), b=λx(x=k₁), and c=λx(x=i). These are necessarily pairwise disjoint nonzero Boolean elements. Hence a,b are nonzero and a∨b≠1; the six elements 0,1,a,¬a,b,¬b are pairwise distinct, necessarily. This avoids relying on type t having at least three atoms.

By Plenitude choose h^{σt} with table

    h(0)=0, h(1)=1,
    h(a)=h(b)=1, h(¬a)=h(¬b)=0,

and arbitrary default values elsewhere. The table is consistent, and each displayed equality is necessary by NI. Let A_a={0,1,a,¬a} and A_b={0,1,b,¬b}. On each of these four-element Boolean subalgebras, h is a homomorphism into B_t.

For any proposition p put

    A_p(x) ↔ (p ∧ x∈A_a) ∨ (¬p ∧ x∈A_b).

At every possibility A_p is one of the two finite subalgebras and h restricts to a homomorphism there, so the modal premise holds. Suppose p and ¬p are both possible. A modal extension H would then possibly send a to 1 and possibly send b to 1. ND at the actual point turns each possible identity into an actual identity: H(a)≠1 would make that inequality necessary, and similarly for b. Thus H(a)=H(b)=1. Homomorphism preservation and a∧b=0 give 1=H(a)∧H(b)=H(0)=0, contradiction. Therefore no p is contingent. Every true proposition is necessary; this is the Fregean Axiom and gives Extensionality by the recorded result.

Conversely, over the benchmark, Extensionality collapses □ to truth. Apply the ordinary extension theorem and then regard its true conclusion as necessary.

**Explicit countermodel.** A full action model on the two-element group, with one individual, satisfies □Functional Choice and has a contingent proposition p={identity}. The A_p and h above witness failure. Only finite domains at the displayed fixed types are needed. The construction is metatheoretic and does not require executing a model enumeration.

**Fixed-source classification under □Functional Choice.** Let MBE_σ mean modal extension at source B_σ and target t (or, equivalently for this classification, at every relational target). Then

    MBE_σ  iff  Extensionality or B_σ has at most two atoms.

For necessity, if Extensionality fails choose a contingent p. Three distinct source atoms yield disjoint nonzero a,b with a∨b≠1, and the preceding finite-table obstruction applies. For sufficiency, Extensionality reduces the assertion to local extension. Otherwise assume at most two source atoms. Atomicity then makes B_σ either the two-element algebra or a four-element algebra {0,1,a,¬a}; the assertion that every source element is in this finite list is necessary by NI and BF. Every subalgebra is therefore trivial or whole. If the modal domain is possibly whole, the finite homomorphism equations for h hold possibly, hence actually by ND, and h is already a global homomorphism. If it is never whole, its possible domain is {0,1}; any two-valued evaluation homomorphism on B_σ agrees with h there (with top/bottom at the target type). Section 4's saturation criterion supplies the modal extension.

In particular MBE_t permits the two-world full C2 model: it is exactly the at-most-two-propositional-atoms condition, since Extensionality already gives one propositional atom. The all-type schema nevertheless collapses to Extensionality because higher relational Boolean algebras have at least three atoms. One can lower the single collapse witness to source σ=tt: conditional on a contingent p, the three haecceities of top, bottom and p are disjoint nonzero, and Atomicity supplies three atoms. The uniform closed-term proof above used σ=(tt)t to avoid that conditional choice. No “type t alone forces collapse” claim is made.

## 4. Exact saturation criterion

Under □Functional Choice, for any A,h the existence of a modal extension is equivalent to existence of an ordinary total Boolean homomorphism H agreeing with h on the **possible domain**

    Sat(A)(x) := ◇Ax.

Forward: □(Ax→Hx=hx) and ◇Ax imply ◇(Hx=hx), and ND yields Hx=hx. Reverse: if ◇Ax then Hx=hx gives □(Hx=hx) by NI; if ¬◇Ax then □¬Ax. Thus for every actual x, □(Ax→Hx=hx). BF yields □∀x(Ax→Hx=hx). Every actual global Boolean homomorphism is necessarily one: its defining equations persist by NI, and BF moves their quantifiers under □. Hence ordinary Hom(H) suffices for □Hom(H).

Consequently modal extension restricted to A with ∀x(Ax↔◇Ax) is already a consequence of □Functional Choice: Sat(A) and A have the same actual extension. The obstruction is not lack of local choices; it is algebraic incompatibility between specifications made at different possibilities.

## 5. A neighboring false strengthening

“Every automorphism of a Boolean subalgebra extends to an automorphism of the whole Boolean algebra” fails already in finite classical powerset algebras. In P({0,1,2}), the four-element subalgebra generated by {0} has an automorphism interchanging {0} and {1,2}; no automorphism of P({0,1,2}) can extend it, because Boolean automorphisms preserve atoms. In an atomic Boolean algebra with an atom a whose complement is not an atom, the same obstruction applies. Under □Plenitude one can find such an algebra at a sufficiently high fixed relational type, using three disjoint nonzero haecceities and Atomicity. Thus the unrestricted all-type automorphism-extension schema is incompatible with □Plenitude, and hence with □Functional Choice. A version preserving the cardinalities of atom blocks is a different, much weaker statement.

## 6. Exact algebraic amalgamation and finite obstructions

This section makes the saturation criterion non-tautological and does not rely on an external finite-equation schema being internally complete.

For S^{σt} and h^{στ}, define G_{S,h}^{στt} to be the least actual Boolean subalgebra of the product B_σ×B_τ containing the pairs (s,h(s)) for s∈S. No product type is needed: use binary relation codes. Explicitly, ProdSubalg(R) says

* R(0_σ,0_τ) and R(1_σ,1_τ);
* R(x,y) implies R(¬x,¬y);
* R(x,y) and R(x',y') imply R(x∧x',y∧y').

Put

    G_{S,h}(x,y) := ∀R^{στt}.
      (ProdSubalg(R) ∧ ∀s(Ss→R(s,h(s)))) → R(x,y).

This is an admitted formula and relation. Elementary quantifier reasoning proves that G itself is a product subalgebra, contains the prescribed pairs, and is included in every such product subalgebra. Its first-coordinate projection D={x:∃y G(x,y)} is the subalgebra generated by S. In detail, D is closed and contains S; conversely the relation “x belongs to the subalgebra generated by S,” with y unrestricted, is a product subalgebra containing all generators, so minimality gives the reverse inclusion.

Call the data **Boolean-compatible** when

    ∀y^τ (G_{S,h}(0_σ,y) → y=0_τ).                    (BCmp)

**Lemma.** BCmp is equivalent to G_{S,h} being single-valued. One direction uses G(0,0). For the other, from G(x,y) and G(x,z), closure under paired Boolean operations gives G(0,y△z). BCmp yields y△z=0, hence y=z.

**Amalgamation theorem.** Under the assumptions of §1,

    ∃H [Hom(H) ∧ ∀s(Ss→Hs=hs)]  iff  BCmp(S,h).

Necessity: the graph of H is a product subalgebra containing the prescribed pairs, so contains G; its zero fiber is trivial. Sufficiency: G is a functional homomorphism graph on its generated domain D; apply §1 to extend it. Thus the compatibility test refers only to Boolean consequences of the initial pairs, not to the existence of the requested extension.

Combining §4, under □Functional Choice:

    ∃H [□Hom(H) ∧ □∀x(Ax→Hx=hx)]
       iff BCmp(Sat(A),h).

This identifies the exact obstruction to modal amalgamation: Boolean consequences mixing specifications from different possibilities can produce a nonzero output over zero input. In §3, the two possible pairs (a,1),(b,1) produce (a∧b,1∧1)=(0,1).

### An entirely internal finite-support form

To state an exact finiteness claim without importing standard-model assumptions, define Fin_σ(X) by **extensionalized empty/adjoin induction**:

    ∀K^{(σt)t}.
      [(∀Y (Empty(Y)→KY))
       ∧ ∀Y a Z ((KY ∧ ∀x(Zx↔Yx∨x=a))→KZ)]
        → KX.

Here Empty(Y):=∀x ¬Yx. This is an explicit new abbreviation in the original language, not a new axiom or an alteration of the map's Frege-cardinality definition. Its use avoids identifying coextensive property codes. Every inductive K in this definition is coextension invariant: for nonempty Y choose a∈Y and use the adjoin clause to pass from Y to any coextensive Z; empty Y uses the base clause. Consequently Fin is coextension invariant, contains all empty properties, is closed under adjoining one member, and finite unions of Fin-properties are Fin (induct on one argument using the adjoin clause).

**Finite-support lemma.** For fixed h,

    G_{S,h}(x,y)
       iff ∃X^{σt} (Fin_σ(X) ∧ X⊆S ∧ G_{X,h}(x,y)).

Right-to-left follows from monotonicity in S. For left-to-right let J be the relation on the right. Its zero and unit pairs have empty support. A generator (s,hs) has singleton support. Complement keeps the same support. For a meet of pairs with supports X and Y, use the internally finite support X∪Y; monotonicity puts both pairs in G_{X∪Y,h}, whose product closure gives their meet. Thus J is a product subalgebra containing all S-generators, and G_{S,h}⊆J by minimality.

It follows that BCmp(S,h) holds iff BCmp(X,h) holds for every internally finite X⊆S. Therefore failure of modal amalgamation is witnessed by an internally finite collection of possible inputs. This claim is internal and proved by comprehension and induction above. It must not be replaced without qualification by “some externally standard finite tuple witnesses failure” in an arbitrary Henkin model.

For intuition, adjoining one more generator s has the paired Shannon normal form

    ((x₁∧s)∨(x₀∧¬s), (y₁∧h(s))∨(y₀∧¬h(s)))

with (x₀,y₀),(x₁,y₁)∈G_{X,h}. The set of all displayed pairs is exactly G_{X∪{s},h}, by closure and the two minimality inclusions. Induction on Fin therefore supplies the internal counterpart of “preserves all finite Boolean equations.” In full models, Fin has the ordinary set-theoretic finite extensions, and this is the familiar standard finite-equation criterion. With an explicitly added finite-word/finite-list sort one may formulate the same criterion by evaluating all internally finite Boolean words; the sort's induction and recursion axioms must be stated and conservativity is not claimed here.

## 7. Definition audit

The following terminology distinguishes materially different statements and could improve a future formulation without editing the existing records:

* **Local Boolean extension:** an unboxed partial homomorphism extends at the current evaluation point. The boxed local principle supplies a potentially different extension at each possibility. Both already follow from the benchmark.
* **Simultaneous modal extension:** one H satisfies all possible partial specifications. This is §3's strengthening and collapses contingency when unrestricted.
* **Possible domain Sat(A):** the property λx.◇Ax. It gives the exact common domain of the constraints, under the benchmark's ND and BF; it should replace vague language such as “all the local data.”
* **Boolean-compatible data:** the zero fiber of the paired generated relation is trivial. This is an exact intrinsic test for amalgamation, entirely expressible in C, and separates compatibility from the desired conclusion.
* **Internally finite support:** use an explicitly defined inductive notion or the map's finite-cardinality apparatus only after proving the needed equivalence. Do not silently read a metalinguistic finite-tuple schema as a single internal assumption.

These are proposed abbreviations and distinctions, not changes to published definitions. The Sat(A) criterion and paired-closure test are equivalent reformulations under the specified baseline; unrestricted simultaneous modal extension is a strictly stronger principle there; the finite-word sort is an optional language extension, not part of C.

## 8. Complete Boolean homomorphisms and atom maps

This gives a structural characterization of the root lane's universal qualitative variability principle, for a **fixed** R^{et}. It also gives an especially concise universal-property formulation of the stronger claim that every rigid individual profile occurs at exactly one propositional atom.

Work under C+□Functional Choice. The duality lemma below needs only Boolean Completeness, Atomicity, Plenitude and Functionality at the relevant types. A complete Boolean homomorphism H:B_σ→B_τ preserves 0,1, complement, finite meets, and every **represented** join: if p is the LUB of S^{σt}, then Hp is the LUB of the property λq.∃s(Ss∧q=Hs). All quantifiers and joins are internal. No identification with an external full powerset is assumed.

**Atom primeness for represented joins.** If a is an atom and p=sup S, then a≤p iff ∃s(Ss∧a≤s). The backward implication is immediate. Otherwise every s∈S is disjoint from a (the meet with an atom is either a or zero), hence s≤¬a. The supremum is then ≤¬a, contrary to a≤p. Atomicity also implies that every element p is the join of its atoms, because any positive part of p not beneath a proposed upper bound contains an atom.

**Duality lemma.** Complete Boolean homomorphisms H:B_σ→B_τ correspond to functions from the atoms of B_τ to the atoms of B_σ, by

    b≤H(p)  iff  f(b)≤p.                              (D)

“Functions on atoms” here means functional graphs on those predicates, or operations modulo agreement on atom arguments; arbitrary values on nonatoms are irrelevant and are not claimed unique.

*From H to f.* Since 1_σ is the join of all its atoms, completeness makes 1_τ the join of their H-images. For each target atom b, atom primeness gives a source atom a with b≤H(a). It is unique, since images of distinct source atoms are disjoint. Plenitude, using a fixed default value off the target atoms, represents the uniquely specified atom map. If a=f(b), then a≤p implies b≤H(a)≤H(p). If a is not ≤p, atomicity of a gives a≤¬p, so b≤¬H(p) and b is not below H(p). This proves (D).

*From f to H.* For p∈B_σ take H(p) to be the supremum in B_τ of the property

    { b : Atom_τ(b) and f(b)≤p }.

Completeness gives a unique value and Plenitude represents the assignment by an operation. Its atoms are exactly the displayed atoms, so (D) holds. The cases p=0,1 and p,q,¬p show preservation of Boolean operations using atom separation. For any represented S, source atom primeness gives f(b)≤sup S iff some s∈S has f(b)≤s. Applying (D) and target atom primeness proves H(sup S)=sup{H(s):s∈S}. Thus H is complete. The atom criterion determines every value H(p) uniquely, and Functionality determines H itself.

This internal duality is sufficient for the next theorem; full-model set cardinalities are not used.

## 9. A free complete atomic Boolean algebra universal property

For R^{et} and a propositional atom a, define its rigid profile

    (F_R a)x := a≤_t Rx.

Root's report proves that F_R a is rigid under □Plenitude and that two coextensive rigid profiles are identical. For any assignment g^{eτ} and target atom b, similarly put

    (F_g b)x := b≤_τ gx.

These are equality-built predicates, hence have settled instances and are rigid under the benchmark. The duality lemma gives

    H(Rx)=gx for all x
       iff F_R(f(b))=F_g(b) for every target atom b.    (F)

The equality on the right is identity of rigid profiles, justified by rigidity plus coextension. Equality on the left is recovered from agreement on all target atoms. This is the key factorization condition.

### Existence

For the fixed R, the following are equivalent under □Functional Choice:

1. Every rigid individual profile is F_R(a) for a propositional atom a.
2. For every g^{et}, there is a complete Boolean endomorphism H:B_t→B_t such that H(Rx)=gx for all individuals x.
3. For every relational target type τ and every g^{eτ}, there is a complete Boolean homomorphism H:B_t→B_τ with H(Rx)=gx for all x.

1⇒3: for each target atom b, choose a source atom f(b) with F_R(f(b))=F_g(b); Functional Choice provides a single atom map, with a default off the atom domain. Apply the duality lemma and (F). 3⇒2 is the target τ=t. For 2⇒1, let X^{et} be rigid and use g=X. Its instances are settled, so F_g(b)=X for every target atom b. At least one atom exists below 1. For an extension H, the associated f sends that atom to an a with F_R(a)=X. Thus the existence-only property is precisely the fixed-R version of root's UQV_e.

### Uniqueness

The following are equivalent:

1. F_R is injective on the propositional atoms.
2. Any two complete Boolean endomorphisms agreeing on all Rx are identical.
3. At every relational target τ, any two complete Boolean homomorphisms B_t→B_τ agreeing on all Rx are identical.

1⇒3: if H,K agree on the generators, (F) gives F_R(f_H(b))=F_R(f_K(b)) for every target atom b. Injectivity gives f_H(b)=f_K(b), hence H=K by (D) and Functionality. 3⇒2 is immediate.

For 2⇒1, suppose distinct source atoms a,c have the same R-profile. Define the complete evaluation homomorphisms

    E_a(p) := the proposition (a≤p),
    E_c(p) := the proposition (c≤p).

Because these are equality propositions, their values are exactly top or bottom under ND. Atom primeness verifies preservation of all represented joins, and finite Boolean preservation is immediate. The equal profiles give E_a(Rx)=E_c(Rx) for every x. But E_a(a)=top and E_c(a)=bottom, so they are distinct. This contradicts 2.

### Combined universal property

Hence, for a fixed R,

    F_R bijects propositional atoms with rigid individual profiles

is equivalent to

    every assignment g:e→t extends uniquely to a complete Boolean
    endomorphism H:t→t with H(Rx)=gx,

and is also equivalent to the same existence-and-uniqueness assertion for every relational target τ. This is exactly the universal property of a **free complete atomic Boolean algebra on the individual-indexed family Rx**, relative to the Boolean algebras available at relational types and to represented joins. The word “atomic” and the internal quantifier scope matter: no free object in the category of all possibly atomless complete Boolean algebras is claimed.

**Sharper premise audit.** This combined equivalence, and the uniqueness-only equivalence, already hold over □Plenitude. In the forward combined direction each target atom has a unique preimage profile atom, so Plenitude represents its map; no choice among a non-singleton fiber is needed. Boolean Completeness, Atomicity and Functionality are consequences of □Plenitude. The converse tests and evaluation homomorphisms also need no Choice. By contrast, the existence-only direction from merely surjective F_R in the preceding subsection explicitly uses Functional Choice to select among the fibers. This distinction should be preserved in any record.

The endomorphism form is a particularly short original-language definition. It uses one fixed type t→t for the extending map and a single sentence for its universal property; the all-target schema follows as a theorem. It is stronger than UQV_e alone because it also rules out duplicate worlds with the same profile. Injectivity alone is the quotient lane's world-individuation condition.

**Explicit consistency.** Take any nonempty set D of fixed individuals and the full one-object action model of the group G={0,1}^D under coordinatewise addition mod 2. Let R(x) be the proposition {g∈G:g(x)=1}. Propositional atoms are the singletons {g}; their R-profiles are exactly g, bijectively. The full model satisfies □Functional Choice in ZFC. Thus the universal property coexists with infinitely many individuals and worlds (e.g. D=N) and with genuine contingency.

**Strictness over UQV in full models.** UQV needs only a surjection from worlds onto profiles; the universal property needs a bijection. With infinitely many individuals D, take a full group with cardinality strictly above |P(D)|, e.g. G={0,1}^{P(D)}. There is a surjection onto P(D) (using a chosen injection D→P(D)), so some R satisfies UQV_e, but no R has injective profile map by Cantor/cardinal comparison. This is a metatheoretic full-model separation, not an unsupported internal cardinal-arithmetic identity.

## 10. Structural consequences of the duality and universal property

For composable complete homomorphisms H:B_σ→B_τ and K:B_τ→B_ρ, their atom maps satisfy f_{K∘H}=f_H∘f_K on atoms, directly from (D). The identity has the identity atom map. Thus §8 gives an internal contravariant equivalence between the available complete atomic Boolean algebras and their atom predicates with represented functions, with the usual qualification that an arbitrary atom predicate need not itself be one of the listed types.

The following exact correspondences are useful:

* H is injective iff f_H is surjective on source atoms. A missing source atom is sent to zero; conversely surjectivity lets equality of H-values be tested on every source atom.
* H is surjective iff f_H is injective. If f_H(b)=f_H(c) for distinct target atoms, every H-value contains b iff it contains c, so b is not an H-value. Conversely, for a target q, let p be the join of f_H(b) over atoms b≤q; atom primeness and injectivity give H(p)=q.
* H is an isomorphism iff its atom map is a bijection.
* Under Functional Choice, complete Boolean embeddings and complete Boolean surjections split by complete homomorphisms: choose a section of the associated atom surjection, or extend the inverse of the associated atom injection by any default atom. These statements concern complete homomorphisms and do not imply the false arbitrary-subalgebra retraction principle of §2.

Now suppose a fixed R has bijective profiles, equivalently the universal property in §9. Write H_g for the unique complete endomorphism extending g^{et}. Plenitude represents the uniquely specified assignment g↦H_g by one operation Sub^{(et)(tt)}. Define

    (g⋆h)x := H_g(hx).

Then H_R=id and H_{g⋆h}=H_g∘H_h by checking values on Rx and invoking uniqueness. It follows that ⋆ is associative and R is its two-sided identity. Thus the exact-profile principle supplies a canonical algebra of substitutions on all propositions, not only a cardinality statement about worlds.

There is also a canonical retraction from arbitrary propositional operations onto complete Boolean endomorphisms:

    Canon(K) := H_{λx.K(Rx)}.

Canon(K) is complete and agrees with K on every Rx. If K is already a complete Boolean endomorphism, uniqueness gives Canon(K)=K. Hence Canon is idempotent, and two operations with the same values on the generators have the same canonicalization. No claim that Canon preserves composition for arbitrary operations is made. For a complete K, however, Canon(K∘L)=K∘Canon(L), by the same generator check.

### Modal preservation is a different requirement

For a Boolean endomorphism H:B_t→B_t, commuting with the modal operator □ is equivalent, under the benchmark, to injectivity. Since each □p is a settled proposition, H(□p)=□p (Boolean homomorphisms fix top and bottom). Thus H(□p)=□H(p) for every p is exactly reflection of top, which for a Boolean homomorphism is equivalent to injectivity.

Consequently the free Boolean substitution property cannot be strengthened to arbitrary **modal** substitution. The all-true assignment g(x)=top is extended by evaluation at the all-true profile atom. There is also a distinct all-false profile atom because the individual domain is inhabited. This evaluation homomorphism is not injective, so it does not commute with □. Equivalently, sending a contingent generator Rx to top changes its modal status. The canonical substitution algebra is therefore Boolean and complete; preserving □ requires a restricted class of assignments.

## 11. Why “complete” must remain in the universal property

Replacing “complete Boolean endomorphism” by “Boolean endomorphism” is not a cosmetic simplification. Under □Functional Choice and the Axiom of Infinity at e, no R can have that stronger existence-and-uniqueness property.

Let A_R⊆B_t be the actual Boolean subalgebra generated by {Rx:x^e}, defined by intersection of all subalgebra predicates containing those elements. Say that R is internally finitely independent if every signed pattern on an internally finite set of distinct individuals has nonzero Boolean meet. Equivalently, for disjoint internally finite properties X,Y of individuals, the meet of {Rx:x∈X}∪{¬Ry:y∈Y} is nonzero. Empty patterns have meet 1. These are internal finite sets, not an external finite-tuple schema.

**Existence-only characterization.** Under □Functional Choice, arbitrary assignments g^{et} extend by ordinary Boolean endomorphisms iff R is internally finitely independent.

For necessity, a vanishing finite signed pattern can be sent to 1 by assigning its positive coordinates top and its negative coordinates bottom (Plenitude represents the assignment); a Boolean homomorphism cannot send 0 to 1. Preservation of an internally finite meet follows by induction. For sufficiency, independence says that every Boolean equation among a finite collection of Rx is a Boolean tautology in the distinct generators, hence is preserved by the corresponding gx. The internally finite version follows by the Shannon normal-form induction in §6. Therefore the paired generated graph has trivial zero fiber, and the algebraic amalgamation theorem extends it to B_t.

**Uniqueness characterization.** Under □Functional Choice, uniqueness among all Boolean endomorphisms agreeing on Rx is equivalent to A_R=B_t.

If A_R=B_t, the equalizer of two homomorphisms is a subalgebra containing all Rx, so they agree everywhere and are identical by Functionality.

Conversely suppose b∉A_R. In A_R consider the ideal

    I = { a∈A_R : ∃u,v∈A_R
                     (u≤b ∧ v≤¬b ∧ a≤u∨v) }.

It is proper: 1≤u∨v with u≤b and v≤¬b would give b=u∈A_R. The Boolean ultrafilter extension theorem (derivable from the benchmark's Zorn principle, as in the root lane) supplies an ultrafilter U of A_R disjoint from I. No a∈U lies below b or below ¬b. Consequently the filters generated in B_t by U∪{b} and U∪{¬b} are both proper. Extend them to ultrafilters V,W of B_t. Their restrictions to A_R both equal U, but b∈V and b∉W. Plenitude represents the two-valued evaluations E_V,E_W:B_t→B_t. These are Boolean homomorphisms, agree on every Rx, and disagree at b. They need not preserve arbitrary joins; that is exactly why they do not refute §9's complete-homomorphism uniqueness. This proves the characterization.

### Internal finiteness audit

The Fin_σ predicate introduced in §6 is C-equivalent to the map's existing finite-cardinality formulation:

    Fin_σ(X) iff ∃Z^{(σt)t}(FiniteCardinality_σ(Z) ∧ ZX).       (Fin)

Here is a proof respecting the intensional property codes.

1. By induction on FiniteCardinality, every finite cardinality Z is coextension invariant as a predicate of properties. The zero cardinality has this property. If Z has it, Suc(Z) does too: a witness y in X is also in a coextensive Y, and X\{y},Y\{y} are coextensive. The defining second-order induction for FiniteCardinality applies to the property of having this invariance.
2. Again by cardinality induction, every X to which a finite cardinality applies has Fin_σ(X). Zero applies only to empty properties. If Suc(Z) applies to X, a witness y has Z(X\{y}); by induction that remainder is Fin, and adjoining y gives X up to coextension. The Fin definition explicitly admits all such coextensive adjoinings.
3. Conversely the property “some finite cardinality applies to X” is empty/adjoin inductive. Zero handles every empty X. Given a finite cardinality Z applying to Y and X coextensive with Y∪{a}, if a∈Y then step 1 lets the same Z apply to X. If a∉Y, removing a from X gives a property coextensive with Y, so Suc(Z) applies to X. FiniteCardinality is closed under successor by its definition. Empty/adjoin induction now proves the other direction of (Fin).

Thus the map's Axiom of Infinity at e is exactly ¬Fin_e(top_e), and every internally finite individual property omits an individual.

### Atomlessness contradiction

Assume the ordinary Boolean universal property and Infinity_e. Existence gives internally finite independence, and uniqueness gives A_R=B_t. Every element of A_R has internally finite generator support: the relation “belongs to the subalgebra generated by some Fin subset of the generator family” is itself a subalgebra containing every generator, using finite unions of supports. This is the one-coordinate version of §6's finite-support lemma.

Let 0≠p∈A_R and choose a Fin set X of individuals supporting p. By (Fin) and Infinity_e choose z∉X. In the finite Boolean algebra generated by the Rx for x∈X, a nonzero p contains some nonzero signed-pattern cell; the standard finite partition argument is an induction on Fin(X), splitting each cell when a generator is adjoined. Independence ensures that both refinements of that cell by Rz and ¬Rz are nonzero. Hence p∧Rz and p∧¬Rz are both nonzero. Therefore p is not an atom. This applies to every nonzero p∈A_R=B_t, contradicting Atomicity.

This is an internal contradiction from □Functional Choice + Infinity_e + the ordinary Boolean universal property. In contrast, the **complete** Boolean universal property has the explicit infinite full group/Gallin realization G=2^D described in §9. Completeness of the morphisms is therefore essential to the intended infinitary generation: it excludes nonprincipal-ultrafilter evaluations, which agree on every finite Boolean expression but can disagree on an infinitary join.

## 12. Nonprincipal ultrafilters and infinitary truth

Under the benchmark T=C+□Functional Choice, at every relational type σ,

    Every internal Boolean ultrafilter on B_σ is principal
      iff Fin_σ(top_σ),

where top_σ in the right side denotes the universal property of entities of type σ. Thus T plus the Axiom of Infinity at t supplies a nonprincipal Boolean ultrafilter on propositions. “Internal” means that the ultrafilter is represented by an admitted predicate, and “principal” means its actual extension is {p:a≤p} for some atom a. This is not an assertion of identity between arbitrary coextensive property codes.

**Finiteness of atoms.** The Fin predicate is closed under subsets, finite unions and represented images. Each fact follows by its empty/adjoin induction: the image of X∪{a} is the image of X with f(a) adjoined; a subset of X∪{a} is its intersection with X with possibly a adjoined. Atomicity and Boolean Completeness then give

    Fin_σ(B_σ) iff Fin_σ(At_σ).

Only the reverse direction needs proof. For a finite property A of atoms, let s_A be its join. Induct on A to show the interval [0,s_A] is finite. The empty case is the singleton {0}. If a new atom a is adjoined, then a is disjoint from s_A, and every p≤s_A∨a is either q or q∨a for q=p∧s_A≤s_A, because p∧a is either 0 or a. The new interval is therefore a union of a finite interval and its represented image under q↦q∨a. The unchanged case a∈A is immediate. Since the join of all atoms is 1, finiteness of the atom property makes the entire Boolean algebra finite. This proof uses represented joins only and does not assume external standard finiteness.

**Cofinite-on-atoms filter.** If B_σ is not Fin, neither is At_σ. Define

    F(p) iff Fin_σ(λa. Atom_σ(a) ∧ a≤¬p).

Then F(1), ¬F(0), F is upward closed, and F(p)∧F(q) implies F(p∧q), by the finiteness facts just proved and the atom test for the excluded atoms. Every complement ¬a of an atom belongs to F. The internal Boolean ultrafilter-extension theorem, obtained from the benchmark's Zorn principle, extends F to an ultrafilter U. No atom belongs to U. A principal ultrafilter must be generated by an atom: a nonzero nonatomic generator m has a proper nonzero part q, and then neither q nor ¬q contains m, contrary to the ultrafilter dichotomy. Hence U is nonprincipal.

Conversely, if B_σ is Fin, an ultrafilter U is a finite property by closure under subsets. Its finite meet m belongs to U, by finite induction on U using filter closure; in particular m≠0. Every member of U lies above m, and upward closure gives the converse. Thus U is principal, and its generator m must be an atom. Together these arguments prove the stated equivalence. By §11's bridge (Fin), its infinitude hypothesis is exactly the map's quantified Axiom of Infinity at σ, not merely an external schema asserting n distinct elements for each standard n.

**The obstruction to interpreting every Boolean truth assignment as a world.** At σ=t, Plenitude represents U by the two-valued Boolean endomorphism

    ε_U(p)=top if Up;  ε_U(p)=bottom otherwise.

This endomorphism sends every atom to bottom while sending top to top. Since top is the represented join of all propositional atoms, ε_U fails completeness. Thus finite Boolean consistency alone does not make an internally represented truth assignment an atom/world; preservation of represented arbitrary joins is a substantive condition. If a rigid predicate of membership is desired, λp.(ε_U(p)=top) has the same actual extension as U and is rigid under the benchmark's necessity of identity and distinctness. The ordinary Boolean equations of ε_U are also necessary, using NI and BF. Even a necessarily Boolean homomorphism can therefore fail to be complete.

This does **not** refute Pure Maximalism: its quantified subject is closed pure C-consistent sentences, whereas U is a parameter-indexed assignment of truth values to a whole algebra of propositions. No conversion of this ultrafilter obstruction into an inconsistency of Pure Maximalism is asserted.

## 13. Partial retractions are exactly Plenitude

A useful definition audit is that the following apparently structural retraction schema adds no strength to Plenitude. For relational types γ and ρ, consider

    ∀A^{γt} i^{γρ}.
      [∀x,y(Ax∧Ay∧ix=iy→x=y)]
        → ∃r^{ργ}∀x(Ax→r(ix)=x).                 (PR)

Then C proves equivalence of Plenitude with the all-relational-type schema (PR). The schema may instead require the range of r to lie in A when A is inhabited; the same equivalence holds.

Plenitude implies (PR) by representing the unique inverse relation on the image of A and using a default γ-entity off that image. In the range-in-A formulation choose a default member of the assumed inhabited A.

For the converse, let U^{στt} be any actual total single-valued relation with relational output type τ; the input σ may be e. Encode a pair by

    P_xy := λu^σ v^τ.(u=x ∧ v=y),   γ:=στt.

Define the two C-available operations

    p(P) := λu^σ.∃v^τ Puv,
    h(P) := λz̄.∀u^σ v^τ(Puv→v z̄).

Here z̄ lists the argument types of the relational τ; for τ=t it is empty. C proves p(P_xy)=H_x, where H_x:=λu.(u=x), and h(P_xy)=y, by modalized functionality and the defining equations. Let A(P) assert that P=P_xy for some Uxy. On A, p is injective: equality of the haecceities H_x identifies x, and U's single-valuedness then identifies y, hence P_xy. Apply (PR) to i=p, whose target σt is relational, obtaining r with r(H_x)=P_xy whenever Uxy. Then

    f(x):=h(r(H_x))

represents U. The domain A is inhabited because U is total and every type is inhabited, so the range-in-A variant gives the same conclusion. This argument recovers Plenitude for arbitrary input types from retractions whose source and target are both relational. It uses no new coding type beyond C's existing relational hierarchy.

## 14. Exact finiteness boundary for arbitrary subalgebra retractions

Under T=C+□Functional Choice, for every fixed relational type σ,

    Every actual Boolean subalgebra of B_σ is a Boolean retract
      iff Fin_σ(B_σ).                                      (AR)

The proof requires an internal splitting lemma, for which no standard natural-number sequence or external countability is needed.

**Splitting lemma.** Under Zorn and Transversal Choice, any property S of any type which is not Fin partitions into two properties which are not Fin.

Consider partial matchings on S, represented by symmetric irreflexive binary relations M with at most one M-neighbor at each point and with both endpoints in S. Order valid graph codes by actual inclusion, and put all invalid codes below every valid one, as in §1. The empty matching is valid. The union of the valid members of any represented chain is again a matching: a putative conflict of two edges appears in a common chain member. The union is represented by an existential formula. Zorn therefore supplies a maximal matching M. It leaves at most one element of S unmatched; otherwise add the edge between two unmatched points and its reverse.

The relation E(x,y):=(x=y∨Mxy) is an equivalence relation on the whole type, with two-element classes for the matched pairs and singleton classes elsewhere. Transversal Choice gives a property V meeting each class once. Let L be the matched points in V and R the matched points outside V. The matching is a bijective graph from L to R. A represented functional relation sends finite properties to finite properties, by empty/adjoin induction (the image adds at most one output when one input is adjoined); this does not require an operation whose output is the individual type. Hence if either L or R were Fin, both would be, and adding the at-most-one unmatched point would make S Fin. Thus L and R are both non-Fin. Put the possible unmatched point into either part to obtain a partition of S. All Zorn hypotheses concern represented chains, with a represented union; no external maximality or standard-finiteness assumption was used.

**Proof of (AR), difficult direction.** If B_σ is not Fin, §12 shows its atom predicate is not Fin. Split the atoms into non-Fin parts P,Q and let b be the represented join of P. Atom primeness shows that the atoms below b are exactly P and those below ¬b are exactly Q. The finite/cofinite-on-atoms property

    A(x) := Fin_σ(λa.Atom(a)∧a≤x)
              ∨ Fin_σ(λa.Atom(a)∧a≤¬x)

is a Boolean subalgebra. This follows from closure of Fin under subsets and unions, the atom test for Boolean operations, and interchange of the two disjuncts by complement. It contains every atom and omits b, so it is proper.

No Boolean retraction onto A exists. Indeed any Boolean endomorphism r fixing every atom is the identity: for an atom a, a∧p is either 0 or a, and therefore

    a∧r(p)=r(a)∧r(p)=r(a∧p)=a∧p.

Atomicity makes equality of these atom tests imply r(p)=p for every p. An identity map cannot have range in a proper subalgebra. This contradicts the universal retraction premise.

Conversely, if B_σ is Fin, every subalgebra A and every represented S⊆A are Fin by closure under subsets. Finite Boolean joins, constructed by Fin induction, lie in A and are suprema in its inherited order. Thus A is internally complete. Section 2's retraction criterion supplies a Boolean retraction from B_σ onto A.

Consequently adding arbitrary-subalgebra retractions at a fixed σ to the benchmark is exactly adding the negation of the map's Axiom of Infinity at σ. The all-relational-type retraction schema is consistent with finite full group models and excludes Infinity at every relational type. This is a structural finiteness principle, unlike partial-set retractions in §13, which merely reformulate Plenitude.

## 15. Complete extension: exact infinitary compatibility and a stronger Sikorski theorem

There is a general constrained-extension theorem behind §9. Let s^{ισ} and g^{ιτ} be assignments indexed by any type ι, with σ,τ relational. For each target atom b∈At_τ define the source Boolean element

    m_b := inf { s x : b≤g x }
             ∧ inf { ¬s x : b≤¬g x }.                    (Fiber)

Both families are represented by existentially quantified properties of B_σ, so Boolean Completeness gives these infima. No infinitary connective is being added to C; inf is an abbreviation for its uniquely characterized internal Boolean bound.

Under T,

    ∃ complete Boolean H:B_σ→B_τ, ∀x H(s x)=g x
      iff ∀b∈At_τ, m_b≠0.                              (CE)

Moreover there exists exactly one such H iff every m_b is an atom of B_σ. The existence-and-uniqueness equivalence already holds over □Plenitude, because every required source atom is then specified uniquely; the existence-only implication from nonzero fibers uses Functional Choice.

For proof, an atom a of B_σ lies below m_b exactly when

    ∀x (a≤s x iff b≤g x).

The two directions of each truth-value specification are both imposed in (Fiber), and atoms decide every Boolean element. By §8's duality, a complete H with atom map f satisfies all constraints exactly when f(b)≤m_b for every target atom. A nonzero m_b has a source atom below it; Functional Choice selects these atoms simultaneously, and the converse half of the duality constructs H. If every m_b is itself an atom, these choices are unique and Plenitude alone represents them. Conversely, a zero fiber prevents existence, and if a nonzero fiber is not an atom, Atomicity supplies two different atoms below it. Change a given atom map at that single b to obtain distinct complete extensions. This proves both statements internally, with represented families and operations throughout.

For a Boolean homomorphism h on a subalgebra A⊆B_σ, complement closure and complement preservation simplify the formula to

    m_b = inf { a∈A : b≤h(a) }.                         (Subfiber)

Thus the failure of complete extension has a precise infinitary obstruction: some pulled-back target-atom ultrafilter has zero meet in the ambient source algebra. Ordinary Sikorski extension in §1 has no such obstruction; its extensions may be noncomplete.

### Preservation of existing internal joins is sufficient

Under T, if h:A→B_τ preserves every represented join which exists in A's inherited order, then h extends to a complete Boolean homomorphism B_σ→B_τ. No completeness assumption on A itself is required.

Fix b∈At_τ. Its pulled-back ultrafilter on A is U_b={a∈A:b≤h(a)}. Any such ultrafilter whose evaluation preserves all represented existing joins in A is principal. To see this, suppose U_b nonprincipal and set J:=A\U_b. Every A-upper bound u of J equals 1. Indeed, if u∈J, then J is exactly the principal ideal below u, so U_b is principal at ¬u, a contradiction. Hence u∈U_b; but ¬u∈J≤u, forcing u=1. Therefore J has supremum 1 in A. Join preservation would make 1 the target supremum of h[J], while b lies below no member of h[J]; atom primeness in B_τ contradicts b≤1.

Consequently U_b is principal, at a nonzero atom c of the algebra A. Its ambient infimum (Subfiber) is exactly c, since c belongs to U_b and lies below every member. This is nonzero even when c is not an atom of the ambient B_σ. The criterion (CE) supplies the complete extension. The proof uses only internally represented J and existing suprema, not an external Stone space.

**The condition is sufficient, not necessary.** Internal joins of A can differ from ambient joins. In a full model take B=P(2^N), let A be its clopen subalgebra for the product topology, and let h be two-valued evaluation at the all-zero sequence z. Each coordinate clopen C_n={x:x(n)=1} is sent to 0. Their union is 2^N\{z}, which is dense, so their least clopen upper bound is 1. Thus h fails to preserve this join in A. Nevertheless h has the complete ambient extension given by evaluation at z on all subsets of 2^N; its (Subfiber) is {z}, an atom of B. This example separates preservation of joins in A's own order from compatibility with ambient complete extension.

The exact fiber criterion is consequently the preferable definition when the intended requirement is extension to an ambient complete homomorphism. “Preserves all joins existing internally in the domain subalgebra” is a convenient stronger sufficient hypothesis and should not be silently substituted for it.

## 16. A compact structural finiteness package

Combining the preceding arguments, T proves the following equivalent conditions at each fixed relational type σ:

1. B_σ is internally Fin (equivalently, the map's quantified Axiom of Infinity at σ fails).
2. Every represented Boolean ultrafilter on B_σ is principal.
3. Every Boolean endomorphism of B_σ preserves every represented Boolean join.
4. Every Boolean homomorphism from B_σ to any relational B_τ preserves every represented Boolean join.
5. Every actual Boolean subalgebra of B_σ is a Boolean retract of B_σ.

Sections 12 and 14 prove the equivalence of 1,2,5. If 1 holds, any represented family in B_σ is finite, so preservation of binary joins and zero proves preservation of its supremum by Fin induction; this gives 4 and hence 3. If 1 fails, §12's nonprincipal-ultrafilter evaluation can take values in {0_σ,1_σ}⊆B_σ itself. It is an endomorphism sending every atom to zero and their represented join 1 to 1, refuting 3. Thus 3 implies 1 as well.

For σ=t, this provides several concise but exactly equivalent ways to impose internal finiteness of the propositional/world algebra. These are substantive extra principles relative to T, and all conflict with T+Infinity_t. They should not be confused with the theorem that Boolean **automorphisms** preserve arbitrary represented joins: an order isomorphism preserves every existing supremum regardless of finiteness. The force of 3 comes from including noninvertible endomorphisms.

## 17. Two-subalgebra gluing has an exact interpolation criterion

Let A,B be actual Boolean subalgebras of B_σ and C:=A∩B. Under T, the following are equivalent, for any fixed relational target B_τ:

* Every pair of Boolean homomorphisms h_A:A→B_τ and h_B:B→B_τ which agree on C has a common total Boolean homomorphism extension B_σ→B_τ.
* For all a∈A,b∈B,

      a∧b=0 → ∃c∈C(a≤c ∧ b≤¬c).                      (Int)

This is an algebraic interpolation condition on the concrete inclusions of the two subalgebras. It says exactly when agreement on the intersection is sufficient for gluing; the existence of a common codomain and agreement on overlap alone are not sufficient.

**Sufficiency.** Form the paired Boolean graph generated by (a,h_Aa) for a∈A and (b,h_Bb) for b∈B. Every generated pair has an internally finite disjunctive normal form

    (∨_i(a_i∧b_i),  ∨_i(h_Aa_i∧h_Bb_i)),

where a_i∈A and b_i∈B. This is the finite-support/normal-form argument of §6: generators have one row; joins use finite unions of rows; meets distribute over two finite row families; and complement uses ¬(a∧b)=(¬a∧1)∨(1∧¬b), followed by finite distribution. Rows may be represented by the admitted haecceity codes of pairs, so this is an internal Fin induction rather than an external finite-word assumption.

If the first coordinate is zero, each a_i∧b_i is zero. Choose the separator c_i∈C from (Int). Then h_Aa_i≤h_Ac_i=h_Bc_i and h_Bb_i≤¬h_Bc_i, so each image row is zero. Therefore the paired graph has trivial zero fiber. Section 6's exact compatibility theorem and Sikorski extension yield a common total homomorphism.

**Necessity.** Suppose a∈A,b∈B are disjoint and have no separator c∈C. On C consider the filters

    F_a={c∈C:a≤c},   F_b={c∈C:b≤c}.

Their joint generated filter is proper. Otherwise some u∈F_a,v∈F_b satisfy u∧v=0, and u is a forbidden separator: a≤u and b≤v≤¬u. Extend the joint filter to an ultrafilter U on C. The filters generated by U∪{a} in A and by U∪{b} in B are proper. For example, u∈U and u∧a=0 would imply ¬u∈F_a⊆U, a contradiction. Extend them to ultrafilters U_A,U_B. Both restrict to U on C, but a∈U_A and b∈U_B.

Their two-valued evaluations into {0_τ,1_τ} are represented by Plenitude (with arbitrary defaults outside the respective domains). They agree on C and send a and b to 1. A common homomorphism would then send a∧b=0 to 1, impossible. This proves necessity. Only represented filters and ultrafilter extension are used.

If C={0,1}, (Int) reduces to ordinary Boolean independence of the two subalgebras: every nonzero a∈A has nonzero meet with every nonzero b∈B. In P({0,1,2}), the subalgebras generated by {0} and by {1} have intersection {0,1} but fail this condition; their evaluations sending those two disjoint generators to 1 agree on the intersection and cannot be glued.

**Pairwise gluing does not settle a larger family.** In P({00,01,10,11}), let a,b be the two coordinate events and let c be their exclusive-or event. The four-element subalgebras generated by a,b,c are pairwise independent, so each pair satisfies (Int). Nevertheless assigning all three generators value 1 cannot extend to a homomorphism, because a∧b∧c=0. Thus pairwise overlap and pairwise interpolation are insufficient for three-way gluing. Section 6's paired-generated-graph criterion handles the necessary finite relations across the entire family.

## 18. A general graph form of the new choice/completeness theorem

Relational Choice plus Boolean Completeness gives more than an ordinary transversal. For any represented relation E^{σσt}, put

    K(x,y):=(x≠y)∧(Exy∨Eyx).

There is a property F^{σt} such that

    ∀xy □(Fx∧Fy→¬K(x,y)),
    ∀x(¬Fx→∃y(Fy∧K(x,y))).                           (MI)

Thus F is an actually maximal independent set in the symmetric graph obtained by deleting loops from E, and its pairwise independence is necessary for each pair of actual parameters. This does not assert □∀xy independence, necessary membership of F, or necessary maximality.

The proof is exactly the partial-selector construction in the separate conjecture proof. The predicate P consists of properties satisfying the first line of (MI); it is closed under represented algebraic chain suprema by evaluation's right adjoint. If x is outside F and has no actual K-neighbor in F, let

    q_x:=¬∃z(Fz∧K(x,z)),
    G:=λy(Fy∨(y=x∧q_x)).

The symmetry and irreflexivity of K are logical consequences of its definition at every world, so G remains in P. Actually q_x is true and G strictly extends F. Relational Choice chooses a progressive functional graph, strict whenever the second line of (MI) fails; the internal Bourbaki–Witt lemma supplies its fixed point. Only chain Boolean completeness at σt and Relational Choice at (σt,σt) are needed. Taking E to be an actual equivalence relation makes maximal independence exactly meeting every actual cell once, recovering the strengthened transversal conclusion.

### Why the ordinary union does not remove Boolean Completeness

Given a represented chain C of P-instances, one can always form

    J_C(x):=Hyp(C)∧∃F(CF∧Fx),

where Hyp(C) asserts that the C-members lie in P and form an algebraic chain. At the actual point, if C is such a chain, J_C has the actual union as its extension. Its guard also makes it pointwise necessarily independent: wherever Hyp(C) holds, the local members are comparable and locally independent. However J_C need not algebraically bound an actual member F of C, because CF and Hyp(C) may cease to hold. It is only an upper bound for **actual inclusion**.

Actual inclusion is a preorder on property codes, with coextensive distinct properties equivalent. Its supremum is unique only up to coextension. The fixed-point comparison then cannot infer that two chain-successor values are the same entity, because the selected functional graph may act differently on coextensive inputs. Consequently this guarded-union observation does not prove Transversal Choice from Relational Choice alone. The new completeness proof succeeds precisely because an algebraic chain supremum is unique as an entity.

### At full schematic scope, the robust graph principle is equivalent to Transversal Choice

The pointwise necessary independence in (MI) is a stronger conclusion about the witness, but it does not strengthen the full Transversal Choice schema. Here is the reverse construction without Boolean Completeness.

Assume Transversal Choice and fix E, K, and P as above. On property entities define an actual equivalence relation whose classes within P are actual-coextension classes and whose classes outside P are singletons:

    F≈G :⇔ (P(F)∧P(G)∧∀x(Fx↔Gx)) ∨ (¬P(F)∧F=G).

Transversal Choice gives a property selecting one entity from each ≈-class. Restrict it to P, obtaining Q. Actual inclusion is antisymmetric on Q: comparable in both directions means actual coextension, and Q has only one representative in that class.

Every represented actual-inclusion chain C⊆Q has an upper bound in Q. In the guarded union formula above, now let Hyp(C) explicitly say C⊆P and that every pair of C-members is comparable by actual inclusion. At any point where Hyp(C) holds, two members contributing x and y to the union are comparable there and individually satisfy the local independence condition. Thus J_C is in P, including when future points contain new objects or predicates. Its actual extension is the union of C. Replace J_C by its unique Q-representative to obtain an upper bound of C in Q.

The recorded implication Transversal Choice ⇒ Zorn applies to the represented antisymmetric order of actual inclusion on Q. It gives a maximal Q-member F. If F were not actually maximal independent, the guarded one-point extension constructed above would yield G∈P strictly extending F actually. Its Q-representative would contradict maximality. Hence F satisfies (MI).

Conversely, take E to be an actual equivalence relation. Actual maximal independence then meets every actual cell, and independence gives uniqueness. Thus (MI), for all admitted σ, is equivalent over C to Transversal Choice. The construction uses higher-type instances of Transversal Choice; it is not asserted as a same-type equivalence. An independent in-team audit checked this argument, including the necessary future-domain guards.

An even simpler final normalization strengthens the independence clause to a full □∀. If T is actually independent for the symmetric irreflexive K, put F(x):=T(x)∧∀y(T(y)→¬K(x,y)). Then F≈T actually, while □∀xy(Fx∧Fy→¬K(x,y)) is a logical theorem about this term. For transversals use F(x):=T(x)∧∀y(T(y)∧Rxy→x=y). This normalization needs no extra Choice, BC, or BF. It strengthens the final witness but cannot be inserted into the algebraic chain-join argument as a stronger invariant without a new proof.

## 19. Two no-go tests for a Relational Choice-only torsor countermodel

These are countermodel-design obstructions, not a proof of Relational Choice ⇒ Transversal Choice.

### A definable event can erase future origin tags

Suppose the root individual domain is a union of nontrivial torsors, R is their class equivalence at the root, and at every proper future point R is equality. Set

    p:=∃u v(Ruv∧u≠v),    C_x:=λz(p→Rxz).

At the root C_x has exactly x's R-cell as its extension. At every proper future point C_x is top, independently of x. Hence root Rxy implies C_x=C_y, while the converse follows at the root by reflexivity. Relational Choice on the C_x codes therefore produces a transversal. Restricting to term-generated Henkin domains does not remove these codes: they are λ-definable from R and x. The proposed future singleton tags on raw rows are erased by a definable guard.

A useful sufficient condition in C is the existence of p satisfying

    p ∧ □(p→Equiv(R)) ∧ ∀xy(Rxy→□(p→Rxy)).           (RG)

Then λz(p∧Rxz) is a canonical code for the actual R-cell, by the same argument. Only actual parameters x,y are carried through their pointwise boxes; the middle conjunct handles arbitrary future z. Thus Relational Choice gives a transversal for any actual equivalence R with (RG). The argument does not show that every actual equivalence has such a guard.

### Finite support without enough fixed defaults already refutes Relational Choice

Let a group G act by automorphisms of a candidate Henkin model, fixing the evaluation point and R as an entity. Suppose R has infinitely many root classes, all named model entities have finite individual supports, and for each finite A⊆D_e,

    Fix(G_A) ⊆ R[A],

where G_A fixes A pointwise and R[A] is the union of the root R-cells meeting A. Independent translations of infinitely many unnamed ℤ-torsors have this property. No fullness of the symmetric hierarchy is assumed.

Define the always-serial relation

    V(X,y):=¬∃x(Xx∧Rxy),
    U(X,y):=V(X,y)∨¬∃z V(X,z).

If S were a functional subrelation of U, let A be a finite support for S (enlarged to support R if necessary). The finite haecceity union X_A:=∨_{a∈A}H_a is admitted and fixed by G_A. Since finitely many cells do not exhaust the root domain, V(X_A,−) is nonempty. The unique S-output y for X_A must therefore lie outside R[A]. On the other hand uniqueness makes y fixed by G_A, contradicting the displayed assumption. Thus this whole class of finite-support Henkin constructions fails Relational Choice already at input et and output e.

Infinitely many individually named fixed default torsors defeat the displayed fixed-point assumption, so this is not a refutation of the stronger seed proposed by the parent agent. A selector can use a named default outside every finite cover. The unresolved issue is whether impredicative closure and the choice selectors themselves must collect enough of those defaults into one admitted property.

There is a precise added-language boundary. Suppose d_n names an anchor in each default torsor, n∈N externally, and every G_A-fixed point lies in a default torsor or a torsor meeting A. If the language/semantics admits the countable pointwise join

    D:=λx ⋁_{n∈N}(x=d_n),

then the preceding contradiction applies to X:=D∨X_A: its root cell cover includes every default torsor and every torsor meeting A, while some unnamed torsor remains outside. Each d_n is fixed, so X is fixed by G_A. This countable-comprehension argument is an explicit strengthening of bare C; it is not licensed merely by there being countably many constants in a finitary language.

## Attribution and remaining limits

Subsequent conjecture work produced a separate proof of the map's existing Goodsell conjecture RC+BC⇒TC. See `.reproduction/classicism-research/relational-choice-boolean-completeness-transversal-proof.md` for the full argument and audits. Its key construction is a chain-complete poset of pointwise necessarily partial transversals and an internal Bourbaki–Witt theorem for functional graphs; no Plenitude, BF, ND, or Actuality is used. Consequently §1's **graph** form of Boolean extension follows already from RC+BC, since these premises now supply Zorn. Its operation-valued conclusion still requires Plenitude. The existing database conjecture and formalization status remain unchanged.

The map's exact definitions and proved records supply the framework and input implications. The extension proof is a reconstructed standard Boolean-algebra argument; the retraction criterion, modal collapse, and saturation criterion are new arguments in this scratch research rather than attributed paper results. No claim of publication novelty is made. No proof has been independently checked by a human or formalized. Further results should be appended only after checking their typed internal formulation; external powerset-model classifications must not be silently promoted to internal C-equivalences.
