# Finite base domains with Barcan: reconstruction and a nonrigid complete cell

22 October 2026. Original argument developed by the construction and local-strengthening research subagents. Ordinary mathematical argument; no human check or Lean verification claimed. No repository records edited. Direct source of the new reconstruction and example: misc, this note.

## 1. Framework and claim

Work in the fixed relational type system of C: e and t, and sigma→tau only when tau is relational. Write E_n^sigma for the finite sentence asserting exactly n entities of type sigma. Let BF_sigma be the single predicate-form Barcan sentence

    forall X^(sigma t), (forall x^sigma, Box(X x)) -> Box(forall x^sigma, X x).

We use the standard action-model semantics and completeness for C used throughout the profile-root construction. In particular, entities transport along arrows, transport commutes with interpretation of terms, and quantifiers at a target range over the target domain. The proof does not replace these by constant-domain semantics.

Recorded background: C proves NI and Intensionality, and proves modalized Functionality. See `topics/classicism/principles/intensionality-r.yaml`, `results/classicism-implies-modalized-functionality-r.yaml`, and `results/barcan-r-implies-functionality-r.yaml`; their source locators are Bacon–Dorr, Classicism, draft 16 May 2023, section 1.5 pp. 17–18 and Proposition 2.1 pp. 20–21. The finite reconstruction below is a new argument.

**Reconstruction theorem.** Suppose a world o satisfies E_n^e, E_m^t, BF_e and BF_t, for positive external finite n,m. Its entire local typed structure, including interpretation of all logical operations and truth, is determined up to isomorphism by these finite base data:

* the n-element individual set;
* the m-element propositional Boolean algebra B, its Box operation, and its actual truth ultrafilter;
* the B-valued equality matrix delta_e(a,b) := (a=b).

Every type is finite at o and at every accessible world. Every transport between accessible worlds is surjective at every type. Every such world satisfies Functionality at every admitted operation type.

Consequently, a realizable finite diagram of those base data, conjoined with BF_e and BF_t, is a single pure sentence complete for closed pure sentences over C. If the base individual set is singleton, it is also complete for pure formulas with one free individual variable, independently of its interpretation.

The conclusion concerns Functionality, which compares entity-valued outputs. It does not assert Extensionality by actual truth coextension. Nor does it classify all complete C-extensions: BF at the base types is an additional hypothesis.

## 2. Finite base domains and BF give exhaustive transported lists

Fix sigma=e or t and enumerate D_sigma(o) as a_1,...,a_k. The actual sentence forall x, disjunction_i(x=a_i) holds. Each actual x equals one of the a_i; NI and finite modal distribution therefore give

    forall x, Box(disjunction_i(x=a_i)).

Apply BF_sigma to obtain

    Box(forall x, disjunction_i(x=a_i)).                         (1)

Thus every arrow h:o→v transports this finite list onto D_sigma(v). This does not require h to be injective. Every further arrow g:v→w is also surjective: the composite gh:o→w is surjective, and its image is contained in the image of g. Therefore both base types are finite throughout the generated cone, and all their transports within the cone are surjective.

Only C's NI and modal rules, followed by the assumed BF instance, were used. No optional hypothesis was necessitated.

## 3. Simultaneous induction on higher types

We prove, at every world v accessible from o, finiteness, surjectivity of every outgoing transport, and Functionality. Suppose these facts are established for the proper subtypes sigma and tau of sigma→tau. The output tau is relational.

### 3.1 Functionality

Suppose f,g of type sigma→tau agree as entities on every current argument. At any arrow h:v→w, every sigma-argument at w is h(a) for a current a. Naturality and the assumed equalities give

    h(f)(h(a)) = h(f(a)) = h(g(a)) = h(g)(h(a)).

Hence Box(forall x, f(x)=g(x)) holds at v. C's modalized Functionality gives f=g. This proves Functionality at the new type at every world in the cone before surjectivity at the new type is needed.

Consequently each f is determined by its current finite table of values. Since D_sigma(v) and D_tau(v) are finite, D_(sigma→tau)(v) is finite.

### 3.2 Exact characterization of current tables

Enumerate the current sigma-domain as a_1,...,a_k. Put delta_sigma(a,b)=(a=b), viewed as an element of the local propositional Boolean algebra. A tuple p_1,...,p_k of tau-entities is the table of a function exactly when

    delta_sigma(a_i,a_j) <= delta_tau(p_i,p_j)   for all i,j.   (2)

Necessity follows from congruence: C proves necessarily that equal arguments have equal values.

For sufficiency, define scalar multiplication at a relational type by

    q ·_tau p := lambda z_bar, q and p[z_bar],

where z_bar lists the argument types of tau; for tau=t this is ordinary conjunction. Let

    f := lambda x, join_i (delta_sigma(x,a_i) ·_tau p_i).       (3)

This lambda is always admitted. Under (2), Intensionality gives

    delta_sigma(a_j,a_i) ·_tau p_i
      = delta_sigma(a_j,a_i) ·_tau p_j.

Indeed, (2) is Box(delta_sigma(a_j,a_i) -> p_i=p_j), which implies the necessary pointwise equivalence of the two localized relations. Thus, substituting x=a_j in (3), each summand is the corresponding scalar part of p_j; the i=j summand is p_j because delta_sigma(a_j,a_j)=top. The finite join is p_j. Hence f realizes the specified table.

This proves that the domain is exactly the finite set of compatible tables (2), rather than the unrestricted function set in general.

### 3.3 Surjectivity at the new type

Let h:v→w, and let F be any sigma→tau entity at w. Enumerate D_sigma(v) as a_i. For each i, choose an arbitrary lift p_i in D_tau(v) of F(h(a_i)); this uses the already proved surjectivity at the output subtype. There are only finitely many choices.

Define f at v by the lambda (3) using these p_i. **The chosen root tuple need not be compatible, and we do not claim f(a_i)=p_i at v.** This is harmless: the lambda exists regardless of compatibility.

At w its interpretation is

    h(f) = lambda x, join_i (delta_sigma(x,h(a_i)) ·_tau F(h(a_i))).

The list h(a_i) exhausts D_sigma(w), possibly with repetitions. The displayed output tuple is the table of the existing entity F and therefore satisfies (2). The interpolation argument of section 3.2 gives agreement with F on all current inputs. Functionality at w, proved in section 3.1, gives h(f)=F.

Thus every outgoing transport is surjective at the new type. The simultaneous induction is complete. In particular, BF holds at all types at every world of the cone, by the usual direct semantic argument using surjective transports.

## 4. Reconstructing equality, quantifiers and abstraction

The induction above reconstructs the finite domains and application. We now verify that it also determines every logical operation as an entity, not just its current truth value.

At t, C's Intensionality and identity elimination give

    delta_t(p,q) = Box(p iff q).                              (4)

At sigma→tau, enumerate the current sigma-domain by a_i. Then

    delta_(sigma→tau)(f,g)
      = meet_i delta_tau(f(a_i),g(a_i)).                      (5)

To check identity of these propositions, evaluate them at an arbitrary accessible world. The transported a_i exhaust its sigma-domain. The right side is true exactly when the transported functions agree as entities on every input, which is exactly their identity by Functionality there. Intensionality identifies the two propositions. Thus (5) is an entity identity, not merely an actual biconditional.

For X of type sigma t, the same exhaustion gives the entity identities

    forall x^sigma, X(x) = meet_i X(a_i),
    exists x^sigma, X(x) = join_i X(a_i).                      (6)

The notation in (6) equates the proposition denoted by the quantified formula with the displayed Boolean combination. The proof again checks every accessible world and applies Intensionality. Repetitions in the transported list do not affect finite meets or joins.

Boolean operations at relational types are pointwise. A lambda abstraction is the unique compatible table whose entries are the recursively interpreted body at each input. Equations (2), (4), (5), and (6), together with ordinary application, therefore give a simultaneous reconstruction of all domains, all term operations, and the denotation and truth value of every formula from the finite base data in section 1.

No reconstruction or uniqueness of the underlying category of worlds is needed. Different action presentations with the same finite base data induce isomorphic local typed logical structures.

To express a particular base diagram, existentially quantify finite lists enumerating e and t, assert the complete finite Boolean and Box tables, the e-equality table, and the truth or falsity of each listed proposition. These are finitely many ordinary pure formulas. Conjoin BF_e and BF_t. Any two realizations have isomorphic typed logical structures. Thus every closed pure sentence has one fixed truth value in all realizations; completeness for C gives completeness of C plus this finite diagram. If e is singleton, the same argument applies to a formula with one free individual variable.

## 5. An explicit pure two-world-chain cell

Let F be the Fregean Axiom, and put A_1 := F and E_1^e. Define the following single closed pure sentence:

    A_chain := E_1^e and E_4^t and BF_e and BF_t
               and exists p^t [p and Atom_t(p)
                                and Box(p)=bottom
                                and Box(not p)=not p].        (7)

This formula uses no signature constants. Bottom, Box, and Atom are the usual pure definable operations/predicate. Since a four-element Boolean algebra has two atoms, an atom p has complement b=not p equal to its other atom. The conjunct p selects the actual truth ultrafilter. Its propositional base table is forced to be

| u | bottom | p | b=not p | top |
|---|---|---|---|---|
| Box(u) | bottom | bottom | b | top |
| actual truth | false | true | false | true |

Box(bottom)=bottom and Box(top)=top are theorems of C. The individual domain is singleton and its equality matrix is top. Therefore (7) fixes every item of the finite base data in section 1. By reconstruction, C+A_chain is complete for closed pure sentences and pointed-complete for formulas with one free individual variable.

## 6. Explicit consistency model and domain counts

Take two worlds r→s, with only identity arrows otherwise. Each individual domain is singleton, with the unique transport. At s use the full singleton extensional typed structure. At r, for a relational type tau=sigma_1...sigma_k t, use

    D_tau(r) = P(product_i D_sigma_i(r)) × D_tau(s).

For k=0, the first factor is the two possible actual truth values, so D_t(r)=2×2. An entity's first coordinate is its arbitrary actual extension; its second is the transported entity at s. Application takes fibers of the actual extension and applies the transported component. All extensions are allowed. This is the ordinary full two-world coalescence: abstraction is closed because its actual extension is allowed and its transported abstraction belongs to the terminal full domain. Equality is identity of these complete intensions; the classical clauses and Logical Equivalence validate C.

Every transport is surjective: for a relational target entity choose any actual extension, and the individual transport is the unique map between singletons. Hence BF holds at every type. Propositions identify with subsets of {r,s}; Box is the interior for the reflexive two-point chain, and actual truth at r is membership of r. Thus p={r}, b={s} satisfy (7).

Some exact domain counts are:

| type | at r | at s |
|---|---:|---:|
| e | 1 | 1 |
| t | 4 | 2 |
| et | 4 | 2 |
| tt | 64 | 4 |
| (et)t | 64 | 4 |

For example D_tt(r) has 2^4 independent actual extensions and 2^2 terminal extensions, hence 64 entities. It is not the unrestricted 4^4=256 function set: compatibility requires that inputs identified at s have outputs identified at s. The model is nonrigid already at t: p transports to bottom and b transports to top.

## 7. Its Fregean successor and the exact nonseparation conclusion

In any A_chain world, write B={bottom,p,b,top} as in section 5. By (6), the Fregean Axiom is the finite meet

    F = meet_(u,v in B) ((u iff v) -> delta_t(u,v)).

Using (4), every factor has the form (w -> Box(w)), with w ranging over all four elements. Its meet is b: the factor w=p is b, while the factors w=bottom,b,top are top. Also E_1^e=top as an entity, because the sole individual transports onto every accessible individual domain. Consequently

    A_1 = F and E_1^e = b

as a proposition entity at every A_chain world. The atom b is actually false and nonbottom. Therefore C proves

    A_chain -> (Diamond A_1 and not A_1).                     (8)

Thus two distinct pointed-complete cells need not exclude ordinary accessibility from one to the other. The exact claim is (8), not a claim about the separate signature principle named Separated Structure in the map. In particular, one cannot infer that every other complete cell is bottom as an entity at an A_chain world merely because it is actually false there. A_1 is a concrete counterexample.

Using the separately audited profile-root pointed-completeness criterion, Max+Atom_t(A_chain) is consistent, and pure Strong Possibility entails Atom_t(A_chain). This corollary uses the criterion in `.reproduction/classicism-research/profile-root-construction-20261022.md`, section 12; the reconstruction and equation (8) themselves do not assume Max or Strong Possibility.
