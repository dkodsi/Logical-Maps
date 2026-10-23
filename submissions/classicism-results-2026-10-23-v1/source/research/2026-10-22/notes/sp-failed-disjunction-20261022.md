# Pure Strong Possibility: existential-disjunction search

Original research notes, 22 October 2026. Author: OpenAI Codex research agent.
No literature-priority claim, named-human verification, or Lean verification.
Fixed background: C and its original pure, finitary relational type language.
No main database records have been edited. Direct source of new deductions:
this note (`misc`). Background: Bacon and Dorr, *Classicism*, draft 16 May
2023, §2.4 pp. 35–36 and §2.6 p. 42, as transcribed in the local records.

## 1. Exact target

Write M = Max(C). An existential identity sentence is a closed formula

    E = ∃x_1 ... x_k θ(x_1,...,x_k),

where θ is a finite Boolean combination of identities between equally typed
pure terms. The terms themselves may contain ordinary quantifiers and lambda
abstraction. In particular, “quantifier-free” describes the outer matrix of
identity atoms; it does not prohibit quantified subterms.

The supplied universal-reflection characterization reduces pure-SP consistency
to the existential-identity disjunction property of M. A negative answer would
be provided by E,F in this fragment with

    M ⊢ E∨F,    M ⊬ E,    M ⊬ F.

The following results restrict where such a counterexample can occur. They
do not settle whether one exists.

## 2. The complete one-individual identity diagram

Let a be a fresh individual constant, and T(a),S(a) pure terms with no other
free variables. Every M-model, at every actual individual a, satisfies

    T(a)=S(a)  iff  C(a) ⊢ T(a)=S(a).

The theorem direction is immediate. For the converse use the previously
proved unary Possibility+ consequence of pure Max: if a pure P(x) is
C-consistent, then M entails ∀x◇P(x). Apply this to T(x)≠S(x). Necessity of
identity gives T(a)=S(a)→□(T(a)=S(a)), contradicting that possibility. Thus
when C(a) does not prove the identity, M entails its universal negation.

For completeness, unary Possibility+ is obtained without adding a signature
Maximalism assumption. If C+P(x) is consistent, a singleton-root coalescence
can have a successor satisfying P of the image of its sole individual. Thus
Q := E_1 ∧ ∀x◇P(x) is C-consistent. M gives ◇Q. Transport an arbitrary actual
individual to the unique individual of a Q-point, then use transitivity to
obtain ◇P of the original individual. This is the same construction and
argument in `profile-root-construction-20261022.md`, §6.

Consequently M decides every finite Boolean combination θ(a) of such
identities uniformly at every actual a. The decision depends on the
C(a)-theoremhood of the finitely many identity atoms. It is not a claim that
arbitrary truth formulas P(a) are decided.

## 3. No disjunction counterexample with only individual witnesses

**Theorem.** Suppose E_1,...,E_n are existential identity sentences and every
outer existential variable in each E_i has type e. If

    M ⊢ E_1∨...∨E_n,

then M proves at least one E_i.

**Proof.** Take a singleton-individual M-model, supplied by ordinary
singleton-root coalescence (or the profile-root construction). Some E_i is
true there. Every witness variable of E_i consequently denotes its sole
individual a. Write E_i=∃x̄ θ(x̄); then θ(a,...,a) holds. Replace every x_j by
the same free variable z, producing θΔ(z). By §2, M decides θΔ(z) uniformly
at every actual individual. Since it is true in this M-model, the decision
must be the positive one: M proves ∀z θΔ(z). Individuals are nonempty, so
M proves E_i. ∎

Quantified subterms are fully allowed throughout this argument. In particular,
one cannot evade the theorem by hiding a quantifier inside one side of an
identity. The theorem concerns outer witness types, not subterm complexity.

The argument also yields a convenient decision description for this fragment:
E is M-provable iff its diagonal matrix θΔ(z) holds in the complete C(a)
identity diagram. If it fails there, a singleton M-model refutes E. E may
still hold in larger M-models (for example ∃x,y x≠y).

## 4. Positive identity formulas are independently harmless

A companion research agent observed the following, included here as a
compatible independently checkable restriction. If E is existential-positive
in identity atoms (only ∧,∨ and existential quantification; no negative
identity atoms), C proves E→□E. True identities persist by NI, finite positive
Boolean combinations persist, and an existential witness transports; no BF
is required. For a closed pure E, C proves E iff it proves E=⊤. Therefore:

* if C proves E, M proves E;
* otherwise M contains E≠⊤, and persistence yields M⊢¬E.

Thus M decides every closed existential-positive identity sentence. A failed
existential-identity disjunction must use genuine disequalities essentially.
Writing an inequality as `(s=t)=⊥` does not preserve its meaning: this says
necessary distinctness and belongs to the positive fragment, whereas s≠t
need not persist under ordinary necessity.

## 5. Two tempting encodings that do not work

1. Actual truth P is not equivalent to the equation P=⊤. The latter is □P.
   In particular a universal identity assertion ∀x I(x) cannot be replaced
   by `(∀x I(x))=⊤` without the missing persistence/Barcan justification.
2. A componentwise Cartesian product of identity structures is not automatically
   a C-model. Its mixed selector r=(⊤,⊥) obeys (r=⊤)=r and (r=⊥)=¬r under
   componentwise operations, yet literal identity makes both r=⊤ and r=⊥
   false. C's actual bivalence forbids this. This observation is from the
   companion product investigation and is not a construction.

A pure fixed term cannot produce that mixed selector by varying its actual
truth across M-models while retaining both stability equations: M already
fixes its identities with ⊤ and ⊥. Any useful product construction has to
avoid the selector issue and supply quantifier witnesses.

## 6. Remaining mathematical obstruction

All M-models have the same pure one-individual term subalgebra. This algebra
satisfies every M-consistent universal identity law. It follows that bare
finite term diagrams cannot by themselves expose an inconsistency in the
joint universal requirements.

The unresolved issue is representability with actual truth and Henkin
quantifier clauses. The term subalgebra need not be closed under existential
witnesses for formulas evaluated as actual truths. Taking a subalgebra of an
M-model preserves its equational operations but does not by itself preserve
its higher-order quantifier truth clauses. Conversely, adding arbitrary root
extensions preserves those clauses but introduces extra elements that may
violate the desired universal laws.

An existential term-witness theorem for M would settle the disjunction target
positively, but is stronger than needed and has not been proved here. A
minimal common algebra could require algebraic witness adjunctions beyond
pure term denotations, just as a prime algebraically closed field requires
roots not represented by rational ground terms. The analogy is only a
warning against conflating the two targets; it is not a C-model construction.

## 7. A general component-profile obstruction

This observation concerns proposed constructions, not arbitrary SP-models.
Suppose a C action model is built with a distinguished object o and a family
of component targets. If f,g of the same type at o are distinct but have equal
transports along every arrow into the components, put k=(f≠g). Then k is true
at o and transports to the bottom proposition along every component arrow.
Indeed equal transported entities have the top identity proposition, by NI.
Thus ◇k can be true only along arrows into the remaining root objects.

If a closed pure P is true at every such root object, C-model semantics gives

    □(◇k→P), hence □ne P.

If M+¬P is consistent, the SP instance ◇ne¬P contradicts this conclusion.
In particular, when there is only one root object, its endomorphisms all have
that same closed pure truth theory. Choose P as E_1 if E_1 holds there, and as
¬E_1 otherwise. Both alternatives' negations are M-consistent. Hence any
noninjectivity of the joint component-profile map rules out SP.

More generally, if there are only m exceptional root objects, some E_n with
1≤n≤m+1 is false at every one of them. Take P=¬E_n; M+E_n is consistent by
coalescence with n actual individuals. Therefore the joint component-profile
map must be injective at every type of any SP-object in such a construction.
Forward-closed components are a sufficient familiar setup. They are not
needed if equality of transports means equality of ENTITIES, since a bottom
transport remains bottom along every subsequent arrow even if it returns.

In a singleton root whose every entity has the component profile of a pure
term T(a), injectivity implies that entity equals the actual denotation T(a).
Thus this particular family can realize SP only if it achieves genuine
all-type term generation. Replacing isolated ghosts by an atomless root-only
part does not solve the problem. The argument uses a true identity
*disequality* of two duplicate profiles, not an actual atom.

## 8. The monism disjunction is NOT a counterexample

Define

    H(P) := ∃r [r≠⊥ ∧ r=◇r ∧ r≤P].

C proves H(P)↔□ne P. From a □ne witness q take r=◇q; S4 idempotence of
◇ gives r=◇r. Conversely r≠⊥ and r=◇r imply r is actually true, since
◇r is by definition r≠⊥; use q=r. Thus H is existential in the identity
fragment, with ≤ expanded as a Boolean identity.

A tempting failed disjunction was H(E_1)∨H(¬E_1). Each branch is individually
unforced by Max, and C proves ¬E_1→H(¬E_1). The following construction gives
a Max-model with BOTH branches false. It therefore decisively removes this
candidate, rather than merely failing to prove it.

### 8.1 The two-object retract core

Let the root category have objects 0,1 and arrows h:0→1, j:1→0 with jh=id_0.
Its remaining nontrivial endomorphism is hj at 1. Give 0 one individual and
1 two; h includes the sole individual and j collapses the two. Coalesce a
C-complete set of component action models below both roots. For every root i,
component object V, and map u:E_i→D_e(V), include an exit (i,V,u); compose
with root arrows by precomposing u, and with component arrows using their
individual transport maps.

At a relational type σ=τ_1...τ_k t, construct root domains by induction on
type. An entity at root i is an extension family over all arrows out of i.
At an arrow to W its extension is a subset of the product of the already
constructed argument domains D_τj(W). Admit every such family whose tail
along every component exit is an entity of the original component model.
All root extension coordinates are unrestricted. Root-arrow tails stay in
the domains because their component tails are among the required component
tails. Application takes fibers; abstraction uses its ordinary extension at
each target. At component targets it lands by the component's term closure;
at root targets fullness admits its extension. Quantifiers use the domain
of the target object. These clauses validate H. H-equivalent abstractions
agree in every extension coordinate, so Logical Equivalence holds and the
construction validates C. This is a new multi-root adaptation of coalescence,
not a theorem attributed to the source's one-root statement.

Every C-consistent pure sentence is realized at a reachable component,
so both roots satisfy M. At 0, E_1 is true; at 1, ¬E_1 is true. For every
actual truth q at 0, the h-transport of q is possible at 1, witnessed by j,
since jh=id_0. Hence

    at 0:  ∀q [q→◇(¬E_1∧◇q)],

which is exactly ◇ne¬E_1. Thus H(E_1) is false at 0, and H(¬E_1) is false
because H implies its argument. This proves

    M + E_1 + ¬H(E_1) + ¬H(¬E_1)

consistent.

### 8.2 What the return arrow accomplishes

The return arrow is not an illicit Barcan step: it provides a specific future
witness for each transported current truth. Nor does it force the two objects
to have the same individual domain: the inclusion 1→2 has a left inverse,
not a two-sided inverse. All original distinctions at 0 survive h, while new
distinctions and entities may exist at 1.

The preceding component-profile obstruction does not apply, because the
retraction core has two different pure truth theories. It does still prohibit
full SP in finite-root constructions with duplicate profiles, since some
other E_n is omitted by all their root objects.

## 9. A stronger retract model: canonical atoms here, atomlessness there

The following refinement was developed in coordination with the parent
research chat. It supplies a substantial consistent package of SP's known
consequences. It is NOT a full SP-model.

### 9.1 Contexts and root arrows

Use two bookkeeping contexts

    Γ_0={z:e},
    Γ_1={x:e,y:e,d_0:t,d_1:t,...}.

These markers are semantic construction devices, not constants in the final
pure language. The individual sets are {z} at 0 and {x,y} at 1.

A root arrow i→j substitutes each source individual marker by a target
individual marker. It substitutes each source d_n by a target d_m or by one
of the logical propositions ⊤,⊥. There are no d-markers in Γ_0. Compose these
substitutions normally, fixing ⊤,⊥. In particular:

* 0 has only its identity endomorphism;
* 0→1 consists of h_x:z↦x and h_y:z↦y;
* a map j:1→0 sends x,y to z and independently sends every d_n to ⊤ or ⊥;
* every such j satisfies jh_x=jh_y=id_0.

Only marker substitutions and the two Boolean constants are needed. Arbitrary
term substitutions are unnecessary and are not silently assumed.

Take C-complete component models. For every component object V and every
assignment I of Γ_i's markers to correctly typed elements of V, add an exit
(i,V,I). Compose exits with root substitutions by evaluating those marker or
Boolean-constant substitutions, and with component arrows by transport.

### 9.2 Profiles and domains, without a circular domain definition

A component profile at root i and relational type σ is represented by one
term T in the finite-variable language of Γ_i, evaluated at every component
assignment I. Identify profiles with the same such family. At 0 these are
exactly the pure one-individual profiles T(z).

Proceed by induction on type. At root 0 admit ALL extension families at root
arrows, together with any one Γ_0 component profile. At root 1 admit extension
families with a Γ_1 component profile and a finite support S⊂Γ_1: S contains
the profile term's free markers, and at two root arrows to the same target
that agree on S the extension coordinates are identical. Component profiles
use the original component domains. All argument domains at root and component
objects are already available at this type-induction step.

Transport closure is direct:

* A tail of a root-1 entity along a root-1 endomorphism is supported by the
  finitely many generic markers appearing among the images of S. Images ⊤,⊥
  need no support.
* A root-1 tail along j:1→0 has a pure z-profile and arbitrary root-0 extension
  coordinates, so it lands in the root-0 domain.
* Every h_x-tail of a root-0 entity is automatically supported by {x}, and
  every h_y-tail by {y}. The reason is that a root-0 arrow to a root target is
  determined entirely by the image of z. Two root-1 arrows agreeing on x
  therefore have the same composite with h_x, and likewise for y.
* Component tails land by the profile definition and ordinary substitution.

This explicitly avoids defining the same-type root domains by a recursive
landing condition. Root-0 fullness and root-1 finite support already imply
all the required root-to-root landing conditions.

For a supported root-1 entity, two arrows agreeing on a support give equal
transported ENTITIES, not just equal actual extensions: after any further
root or component arrow, the composites still agree on that support, and
the profile term also has its free markers in the support. This observation
is essential when terms contain identity or quantified subterms.

A term with parameters has a component profile obtained by substituting their
profile terms. At root 1 its extension is supported by the union of their
finite supports: arrows agreeing there give exactly the same transported
parameter entities in the same target model. Lambda abstraction consequently
has an admitted extension family and profile. Root 0 has full extension
coordinates, and its h-tails have the supports just described. Quantifiers
range over the target object's domains. H and Logical Equivalence now follow
as in §8.1. Hence this is a C-model.

### 9.3 The fresh splitter propositions

For each d_n define a root-1 proposition D_n with component profile d_n.
At a root arrow f:1→0 its actual extension is the truth bit assigned by f(d_n),
which is ⊤ or ⊥. At a root arrow f:1→1 it is true exactly when f(d_n)=⊤;
a generic marker d_m is assigned false at the identity of root 1. These
coordinates give a natural entity: composition replaces d_n by its assigned
marker or Boolean constant. D_n has finite support {d_n}.

Let p≠⊥ at root 1, supported by finite S. Some arrow f makes its extension
true. Choose d_n outside S. If f is a root arrow, change only f(d_n), first
to ⊤ and then to ⊥. These are legitimate arrows with the same target that
agree on S; p remains true at both, while D_n has opposite truth values. If
f is a component exit, similarly change only the interpretation of d_n to
that component's ⊤ or ⊥. Thus p∧D_n and p∧¬D_n are nonzero disjoint parts
of p. Every nonzero proposition at 1 splits, so its Boolean algebra is
atomless and Actuality is false there.

The same argument works at every relational type: use the constant lift of
D_n and a nonempty extension tuple witnessing X≠⊥. Its two modified arrows
have the same target and the same extension of X. Thus every relational
Boolean algebra at root 1 is atomless.

### 9.4 Root 0: Max, monism, Actuality and all the finite Fregean atoms

Both roots satisfy M, since their component exits realize every C-consistent
closed pure sentence. At 0 the individual domain is singleton; at 1 it has
exactly two individuals.

At root 0 let w have true extension only at id_0, false extension at h_x,h_y,
and bottom component profile. This is admitted; its h-tail is supported by
the empty set, being true at root arrows landing at 0 and false at those
landing at 1. The proposition w is a true atom, and entails every actual
truth. Hence Actuality holds at 0.

Put A_n=F∧E_n as before. Both roots are non-Fregean: root 0 has infinitely
many pure component profiles, and root 1 is atomless. Thus A_n has false
extension at EVERY root arrow. At an A_n component, a pure term T(z) has a
fixed truth value independent of the pointed finite extensional structure.
Consequently for every root-0 proposition p, p∧A_n is literally either ⊥ or
A_n throughout all root and component coordinates. The latter profile is
nonzero. Thus root 0 satisfies Atom(A_n), simultaneously for every positive n.

### 9.5 A genuine distinctness-preserving route to opposite properties

For any root-0 truth q and any return j:1→0, jh_x=id_0 implies that the
h_x-transport of q is possible at root 1. Every pure sentence P true at
root 1 therefore satisfies ◇ne P at root 0. In particular root 0 satisfies

    Max + E_1 + Actuality + {Atom(A_n): n≥1}

and also

    ◇ne(E_2 ∧ Atomlessness_t ∧ ¬Actuality).

The target actually satisfies atomlessness at every relational type, so
finite conjunctions of any of these atomlessness assertions have the same
single witness h_x. In particular ◇ne¬Atom(A_n) holds for every n.

The already established atom-persistence lemma then shows BF_t fails at 0;
E_1 together with ◇E_2 refutes BF_e there. Retracts of relational types to t
extend this to every admitted BF instance, and the known Functionality→BF
argument refutes every Functionality pair. These are deductions from the
constructed properties, not claims that the map's engine has recorded this
new model.

The root-0 proposition domain is externally countable: there are just three
root-arrow truth bits, and countably many pure z-profiles. The original
profile-root argument for internal countability can be repeated because
root-0 higher relation extensions are full. This statement is internal
countability, not Countable Boolean Completeness.

The model is not SP. It has only two root objects and duplicate bottom
component profiles; §7 applies using E_3, which is false at both roots but
consistent with M. Concretely ◇w is supported on root arrows, so H(¬E_3)
holds at 0 and ◇ne E_3 fails. The construction nonetheless shows that the
major known atomicity, non-Barcan, monism, and opposite-possibility constraints
are jointly consistent. It also shows that Actuality alone does not collapse
□ne to actual truth: return arrows are decisive.

## 10. Positive identity term witnesses and the exact retraction limitation

### 10.1 Positive identity term-witness extraction

Let a:e be a fresh individual parameter and let B be the many-sorted pure
C(a) term algebra, quotiented by C(a)-provable identities. Its operations are
all syntactic term contexts, including those containing quantified subterms.
No claim is made here that B admits a truth interpretation satisfying H.

**Theorem.** Suppose a finite positive existential identity sentence E(a)
(with a finite disjunction of finite conjunctions of typed identities as its
matrix) is true for a in some Max model. There are pure a-terms witnessing
one disjunct, with every resulting ground identity provable in C(a).

For the reduction from truth in Max to C(a)-provability, E(a) is persistent:
C proves E(a)→□E(a), by NI and transport of its witnesses. If C(a) did not
prove E(a), unary Possibility+ would make ¬E(a) possible at every individual
of every Max model. Thus E(a) could not be true in a Max model. Consequently
C(a) proves E(a).

Now use the original singleton pure-profile Max root. It satisfies E(a).
Choose a true finite disjunct and its actual witnesses. Every individual
witness equals the sole individual a; every relational witness has a pure
a-term component profile. Replace witnesses by those profile terms. Each
positive identity between the original root entities entails equality of
their entire component profiles. Since the components are C-complete and
include every interpretation of a, the corresponding substituted identity
is C(a)-provable. This proves the theorem without any Herbrand theorem or
assumption that the term algebra itself is a Henkin model.

In particular, every finite positive equational diagram over B realized
in a Max model with chosen individual a has a solution in B. Coefficients
from B are merely pure a-terms and are included in the substitution.

### 10.2 Every such target maps into an elementary extension of B

Let N be any Max model, with a chosen individual a, and identify B with its
canonical term subalgebra in N. The inclusion is injective by unary
Possibility+. Work solely in the many-sorted algebraic language of term
operations. Expand the elementary diagram of B by one constant c_n for
every element n of N, adding every positive operation/equality equation
true of the c_n in N, and setting c_b=b for b∈B. Every finite subset is
satisfiable in B by §10.1; the elementary-diagram part is already true there.
Compactness gives an elementary extension B* of B and a term-operation
homomorphism j:N→B* fixing B.

This is an algebraic statement. Neither B nor B* has been supplied with an
H-truth predicate. It does not construct a categorical successor, an actual
Henkin model, or a return map to B itself. Disequalities in N are not imposed
on j and may collapse. An ultrapower version follows by the usual finite-
diagram ultrafilter construction, if desired, but is not needed here.

### 10.3 An infinite obstruction to returning into a pure-profile source

Let A_n=Fregean∧Exactly_n_e, for n≥1. In Max these are pairwise disjoint,
nonzero pure propositions. A pure a-term T can realize at most one complete
binary pattern

    T∧A_n=A_n  (n∈S),       T∧A_n=⊥  (n∉S)

of C(a)-provable identities. There are only countably many pure a-terms,
so choose S⊆N_{>0} which none realizes.

The theory Max+E_1, with a new proposition constant p and all the displayed
pattern equations with p in place of T, is consistent. Every finite subset
is satisfied in any singleton Max model by taking p to be the finite join
of the A_n whose positive equations occur in that subset. Disjointness
settles the finitely many negative equations. Apply compactness to obtain
one model N satisfying the whole theory and whole pattern.

There is no term-operation homomorphism N→B fixing pure terms. Its image
of p would be a pure a-term having the excluded S-pattern. More strongly,
there is no such map from N into ANY singleton root construction in which
every proposition has a pure a-term profile over a C-complete component
family. Indeed the image of p would have some profile T(a), and its pattern
equalities would force all the excluded C(a)-identities by component
completeness. Extra root truth bits or extra root extension coordinates do
not repair this contradiction.

Thus an arbitrary prescribed Max model cannot be installed as a retract
target while retaining a pure-profile singleton source. No finite positive
identity diagram witnesses this obstruction: every finite part has the
explicit finite-join solution. The source must acquire new profiles or
another completion, and the H/Henkin truth issue then returns. This is a
construction obstruction, not a failed finite existential-identity DP and
not a refutation of SP.

## 11. What a nonfull root policy must preserve

A category construction with h:0→1 and j:1→0, jh=id_0, requires genuine
type-preserving term homomorphisms in both directions. Thus h embeds the
entire source term algebra and j is a surjective retraction onto it. Merely
embedding the common algebra B into the prescribed target N supplies neither
j nor suitable source truth domains. Section 10 gives all finite positive
equations needed for a map into B, and gives an actual map into B*, but shows
why the map need not land in B or any pure-profile root.

For a proposed nonfull target policy, the necessary closure audit has two
separate parts:

1. Every admitted entity must land in the specified domains after every
   root and component arrow. A root-to-root loop makes these simultaneous
   image restrictions, and finite support alone does not automatically
   verify them.
2. Every parameterized lambda term must be admitted. This includes lambda
   terms containing quantifiers over the full chosen target domains and
   literal identities of transported entities. Closure under Boolean
   operations or application alone does not establish this requirement.

The mixed full/pinned construction in §9 passes because h-tails of root-0
entities automatically have one-marker support, while all j-tails land in
the unrestricted root-0 extension coordinates. An arbitrary prescribed N
has no comparable automatic image theorem. Section 10.3 proves that no
uniform image theorem can hold with all pure source profiles retained.

## 12. A symmetric Max root refuting Relational Choice

This section supplies a new model-theoretic compatibility proof. The map's
proved records alone do not currently establish Max+¬Relational Choice.
The construction uses an EXTERNAL permutation action preserving actual
truth, not permutation arrows in the future category.

### 12.1 Root individuals, profiles, and symmetry

Take one isolated root o with individual domain

    E={i_n:n∈N} ⊔ {a_n^0,a_n^1:n∈N}.

Let G=∏_{n∈N}C_2 independently swap a_n^0 and a_n^1, fixing every i_n.
Use a C-complete family of forward-closed component models. For each
component object V, add root exits indexed by all assignments I:E→D_e(V),
with the usual postcomposition by component transports.

A root profile at a relational type is the component family of a pure term
T(c_1,...,c_k), where c_1,...,c_k are finitely many members of E and an exit I
interprets c_l by I(c_l). Profiles are identified when their entities agree
at every component exit. G acts by moving the parameters c_l. This is
well-defined because all assignments I occur. Every such profile has finite
support: any permutation fixing its finitely many parameters fixes it.

Inductively, at relational type σ=τ_1...τ_k t, use pairs (R,φ), where
R⊆D_{τ_1}(o)×...×D_{τ_k}(o) is an actual extension and φ is a profile of the
specified form. The lower type domains already carry G-actions. Let G act
on R by moving its tuples and on φ as just defined. Admit exactly the pairs
with finite support. Here finite support means that some finite subset of
E is fixed pointwise by a subgroup fixing the pair. All e-elements and all
admitted higher entities have such a support. For t, R is merely a truth
bit; G fixes that bit. All root sorts are nonempty.

The future category has no nonidentity root-to-root arrows. Transport along
an exit takes a root entity to its profile entity. Its further component
transports are the prescribed term transports. The external G-action
permutes exits by precomposing I with the corresponding permutation; it
is not added to the category as extra possible futures.

### 12.2 Full lambda and quantifier closure

At the root, application and literal identity are equivariant under G.
Quantification is equivariant because each root domain is G-invariant and
G acts bijectively on it. Consequently, by induction on terms, the value of
a parameterized term is supported by the finite union of the supports of
its parameters. Lambda abstraction has the extension defined by its actual
truth values and the component profile obtained by substituting the profile
terms of its parameters. This is a permitted pure term with finitely many
E-parameters, and the pair has finite support. Thus every lambda term is
admitted, including terms with arbitrary quantified subterms or higher-type
identity atoms.

Component evaluation is already a C-model evaluation, so the standard
coalescence argument proves H and Logical Equivalence. This yields a
C-model. Complete exits witness every C-consistent pure closed sentence;
equivalently every nontheorem pure identity is nonidentity at the root.
Hence the root satisfies Max.

### 12.3 A serial relation with no functional subrelation

Define U:eet to have bottom component profile and root extension

    U(i_n,a_n^0), U(i_n,a_n^1) for every n;
    U(a_n^ε,a_n^ε) for every n and ε∈{0,1};

with no other tuples. This extension is G-invariant, so U is admitted with
empty support. It is actually serial on E.

Suppose an admitted S:eet were a functional subrelation of U. Choose a
finite support F for S and an n for which neither a_n^0 nor a_n^1 belongs
to F. The transposition of this pair fixes F and fixes i_n, hence preserves
S's extension. Seriality of S requires S(i_n,a_n^ε) for one ε. The swap
then also gives S(i_n,a_n^{1-ε}), contradicting functionality since those
individuals are distinct. Therefore the (e,e) instance of Relational Choice
fails at this Max root.

The failure is actual and does not assume that a merely actual existential
or universal assertion is an identity with ⊤. It does not establish a
finite existential-identity disjunction failure. It does show that root
policies offering every actual relation extension cannot be universal for
Max-consistent pure theories: those policies validate Relational Choice
under external set-theoretic choice, whereas this Max model refutes it.

## 13. A symmetric retract realizing distinctness-preserving failure of Choice

The symmetric policy from §12 can be attached to a singleton pure-profile
source. This does not solve the arbitrary prescribed-target problem in
§10.3, but it shows that the absence of full actual relation extensions is
compatible with the retract mechanism.

### 13.1 Root category and external action

Use root 0 with individual domain {a}, and root 1 with the E and G of §12.
The root arrows are:

- id_0 and h_b:0→1 for every b∈E, with h_b(a)=b;
- one arrow j:1→0, collapsing all individuals to a;
- the permutations g∈G at root 1, and constants c_b:1→1 for b∈E.

Composition is composition of these maps. In particular jh_b=id_0,
h_bj=c_b, jg=j, gh_b=h_{g b}, gc_b=c_{g b}, and c_bc_d=c_b.

The EXTERNAL G-action fixes both root objects, id_0, and j; it moves h_b
and c_b to h_{g b}, c_{g b}; it conjugates the root permutation arrows. As
G is abelian, conjugation fixes every such arrow. Thus every root arrow has
finite external support (even though a permutation arrow can swap
infinitely many pairs). An h_b or c_b needs only the parameter b.

Attach C-complete forward-closed components with exits from root i indexed
by every map E_i→D_e(V), composing by those maps. The external action
reindexes exits and acts identically inside components. This is compatible
with composition; for example an exit I after h_b becomes the root-0 exit
with value I(b), unchanged by simultaneously replacing I by I∘g^{-1} and
b by gb.

### 13.2 Domains and closure

Root-0 component profiles are pure a-terms. Root-1 profiles are pure terms
with finitely many E-parameters. At each relational type, after the lower
domains and their external actions have been constructed, take all extension
families over root arrows together with an allowed component profile,
restricting to pairs having finite external G-support. The action on an
extension family simultaneously reindexes its root arrow and moves its
argument tuple by the lower-type external action. For proposition type it
merely reindexes the root truth bits. Profiles transform by moving their
individual parameters. Quotient profiles by equality of their full
component families.

Every root transport lands in the required root domain. Profile transport
is substitution of the relevant individual map: h_b substitutes b for a,
j collapses finitely many parameters to a, and permutations/constants give
finite new parameter lists. The transported extension family has support
contained in the union of a support of the entity and a support of the
arrow, by equivariance of transport. Component transports land in the
original component domains.

At every root object, G acts by bijections preserving actual application,
literal equality, and truth. Quantification is equivariant since each
chosen domain is G-invariant. Hence a parameterized lambda term has support
contained in the union of the finite supports of its parameters, while its
component profile is the appropriate finite substitution of their profiles.
This proves full lambda closure, including quantified and identity terms.
As before H and Logical Equivalence hold, and complete exits make BOTH root
objects Max points.

### 13.3 Choice fails at both roots

At root 1, admit the invariant actual relation U from §12, with zero
extension at every other root arrow and bottom component profile. The id_1
coordinate is fixed by external conjugation. Thus U has empty support.
It is serial but has no finite-supported functional subrelation by the
same pair-swap proof. Root 1 therefore refutes Relational Choice at (e,e).

There is also an actual failure at root 0, at (t,t). For every b∈E let q_b
be the root-0 proposition with bottom component profile and true root bit
exactly at h_b. These are pairwise distinct, have finite support {b}, and
satisfy g(q_b)=q_{gb}. Define a root-0 actual relation V:t t t by

    V(q_{i_n},q_{a_n^0}) and V(q_{i_n},q_{a_n^1}) for all n;
    V(p,p) for every p not among the q_{i_n};

and no other actual tuples. Give it zero extension at every other root
arrow and bottom component profile. This is G-invariant and thus admitted.
It is serial on the entire root proposition domain. A finite-supported
functional subrelation would have to choose one of q_{a_n^0},q_{a_n^1} for
q_{i_n}; a pair-swap outside its support fixes the input and exchanges the
two distinct possible outputs. Therefore no such subrelation exists.

### 13.4 Source atoms and the precise possibility conclusion

At root 0, let w have true root bit only at id_0 and bottom component
profile. It is invariant, admitted, and a true atom. Thus Actuality holds.
Both roots have infinitely many propositions and are non-Fregean; therefore
A_n=Fregean∧Exactly_n_e is false at every root arrow. The pure a-profile
argument from §9.4 shows that every A_n is nevertheless an atom at root 0.

For any source truth q and any h_b, its h_b-transport is possible at root 1
because jh_b=id_0. Hence root 0 satisfies ◇ne P for EVERY pure sentence P
true at root 1. In particular this construction jointly gives

    Max + E_1 + Actuality + {Atom(A_n):n≥1} + ¬RelChoice_(t,t)
          + ◇ne(¬RelChoice_(e,e)).

The two RC failures displayed are specified instances, so the corresponding
schematic Relational Choice principle is false. One should not treat a
schema as a single object-language sentence in a modal formula.

This source may have uncountably many propositions: arbitrary choices of
truth bits at the fixed-index arrows h_{i_n} have empty support. No
countability conclusion is asserted. This particular category also has
Strong Actuality: w_h_b is supported at the unique return j, hence remains
an atom at root 1; its component tails are bottom. Consequently it does not
realize ◇ne Atomlessness_t and is not a full SP model. Attaching additional
root targets would require a fresh joint support and transport audit.

## 14. Combining the symmetric target with the atomless pinned target

The unique-return limitation of §13 is removable. The following common
root category combines external finite permutation support with the finite
substitution support from §9. These are two distinct restrictions.

### 14.1 Category and domain policies

Keep E and the external abelian group G from §§12–13. Add bookkeeping
proposition markers d_0,d_1,... at root 1. Root 0 has the single individual
a and no proposition markers. The root arrows are:

- id_0 and h_b:0→1 for each b∈E;
- returns j_s:1→0, for every assignment s of the d_i to logical ⊤ or ⊥;
  all of them collapse E to a;
- endomorphisms of root 1 whose E-map is a member of G or a constant c_b,
  and whose d-map sends each d_i to some d_k, ⊤, or ⊥.

Composition is substitution, fixing logical constants. These maps are
closed under composition and j_s h_b=id_0. An external g∈G moves the
E-parameters and fixes all d_i and logical constants. It conjugates the
root category: permutation E-maps stay fixed since G is abelian, constant
maps and h_b acquire support {b}, and every j_s is fixed. Thus every root
arrow has finite external G-support, regardless of its d-substitution.

Component exits from root 1 include ALL assignments of E to component
individuals and of every d_i to component propositions. Root-0 exits are
pointed component objects as before. External G acts by reindexing E
assignments and fixes component entities.

At root 0, use all extension families with pure a-term component profiles
which have finite EXTERNAL G-support. At root 1, use extension families
with finite-parameter E,d profiles satisfying BOTH:

1. finite external G-support;
2. finite SUBSTITUTION support S⊆E∪{d_i}: root arrows with the same target
   that agree on S give the same extension coordinate.

A support S is enlarged to contain the finitely many parameters in a
profile presentation. Entities are full extension families plus component
profiles; supports and presentations are not extra entity coordinates.
Everything is defined by induction on argument types as before.

### 14.2 The two closure arguments are compatible

External support transports by adjoining a support of the arrow, using
transport equivariance. Substitution support transports by taking the
finitely many nonconstant images of its supported markers. For a return
j_s, the component profile becomes a pure a-term and root 0 imposes no
substitution-support condition. For a source entity transported along h_b,
the resulting family is substitution-supported by {b}: f h_b is determined
by the target of f and its image of b. Its external support is finite by
the previous rule. Thus every root transport lands in its required domain.

For root-1 entities, agreement of arrows on a substitution support gives
equality of ENTIRE transported entities. Agreement survives every further
root composite; component profiles also agree because every free profile
parameter belongs to the support. This supplies the quantified and identity
term clauses exactly as in §9. Independently, all root term operations are
externally G-equivariant because G acts bijectively and preserves actual
application, equality, and truth. A finite tuple of parameters therefore
gives both a finite substitution support and a finite external support for
its lambda value. At root 0 only the latter is required. Component profile
substitution is unchanged. Hence full lambda closure, H and Logical
Equivalence hold. The complete exits make both roots Max points.

### 14.3 The target is atomless and refutes Relational Choice

For each d_i, admit the splitter D_i from §9: its component profile is d_i,
and at a root arrow its truth bit is true exactly when d_i maps to ⊤
(generic marker images count as false). It has substitution support {d_i}
and EMPTY external G-support. A return j_s supplies the chosen bit s_i.

Given any nonzero target relation X, choose a root arrow or component exit
and extension tuple witnessing it, and d_i outside a finite substitution
support of X. Change only that marker's image to ⊤ versus ⊥, leaving the
E-map and all supported markers fixed. Both arrows/exits are allowed, have
the same target, and keep X's extension unchanged at the selected tuple.
The constant lift of D_i takes opposite values. Thus every nonzero X splits
into two nonzero disjoint parts. Root 1 is atomless at every relational type
and refutes Actuality.

For failure of RC_(e,e), define U's extension to be the invariant pair-choice
graph from §12 at EVERY root arrow landing at root 1, and empty at root
arrows landing at root 0. Give U bottom component profile. This family has
empty substitution support and empty external support. Its actual graph is
serial. Every admitted selector has finite external support, so the pair-
swap argument still refutes functionality. The pinned restriction does not
supply an otherwise forbidden selector.

### 14.4 The source retains its atoms and its own Choice failure

At root 0, w supported only at id_0 is again an admitted true atom, giving
Actuality. Its h_b-tail is supported at all the returns j_s and at no root
endomorphism; hence it is substitution-supported by the empty set and is
now split by a fresh D_i. There is no unique-return atomicity argument.
Both roots are non-Fregean. All root-0 propositions still have pure a-term
component profiles, so every A_n remains an atom there.

The q_b propositions supported only at h_b and the source relation V from
§13.3 are still admitted with their finite external supports and pure
bottom profiles. Their h-tails automatically satisfy the substitution
condition. Thus RC_(t,t) still fails at root 0.

Every return j_s satisfies j_s h_b=id_0. Consequently every pure target
truth P has ◇ne P at root 0. This single model therefore realizes

    Max + E_1 + Actuality + {Atom(A_n):n≥1} + ¬RC_(t,t),

    ◇ne(Atomlessness_t ∧ ¬Actuality ∧ ¬RC_(e,e)).

Any finite list of relational-type atomlessness assertions can be included
in the same target conjunction. The target has countably infinitely many
individuals, so each fixed AtLeast_m_e assertion can also be included.
No object-language infinity assertion is claimed without checking its
specific definition. No countability assertion about the source is made.

Since E_1 makes RC_(e,e) actually true at the source, this also gives a new
explicit negative test result:

    Max does NOT prove H(RC_(e,e)) ∨ H(¬RC_(e,e)).

Both disjuncts are false at root 0: the second by factivity, and the first
because ◇ne¬RC_(e,e) holds. Each H formula is an existential finite Boolean
identity formula with RC appearing as a quantified SUBTERM, as permitted
in the original disjunction problem. This eliminates another natural
candidate; it is not a failed disjunction property and not an SP model.
The finite-root pure-profile obstruction of §7 still applies.

## 15. Essential quotients: identity truth is recoverable, Henkin witnesses remain

This section addresses the sufficient criterion in the companion note
`/tmp/classicism-research/sp-essential-extension-20261022.md`: if the common
pure-a term algebra B is essential in the full term algebra of a genuine
Max model, that model satisfies SP. Here essential means every nonidentity
many-sorted term congruence identifies distinct elements of B.

Let A be a genuine Max term algebra, let θ be a congruence maximal among
those restricting to equality on B, and put Q=A/θ. Then B embeds in Q and
is essential there. Q has all term operations, including quantifiers and
identity-valued operations. No actual-truth interpretation is yet assumed.

### 15.1 An ultrafilter gives the correct literal identity at every type

Choose a Boolean truth ultrafilter U_B on B_t induced by any actual Max
model with its chosen individual. Extend U_B to a Boolean ultrafilter U on
Q_t. Such an extension exists because B_t is a Boolean subalgebra of Q_t.

**Claim.** For x,y of any one type in Q,

    eq_sigma(x,y) belongs to U  iff  x=y literally in Q.

For equal x,y, the C-identity eq_sigma(x,x)=⊤ survives the quotient. For
unequal x,y, essentiality provides distinct b,c∈B of some common type in
the congruence generated by (x,y). A finite polynomial chain witnesses that
membership. Every polynomial step satisfies the equationalized Leibniz
inequality

    eq_sigma(x,y) ≤ eq_tau(f(x),f(y)).

This is a C identity uniformly in the finitely many polynomial parameters,
so holds in A and survives in Q. Chaining these inequalities and using
transitivity of identity gives

    eq_sigma(x,y) ≤ eq_rho(b,c).

The latter proposition belongs to B_t and is false under U_B, because B's
ground identity diagram at a Max point is exactly its literal equality.
Upward closure of U therefore forces eq_sigma(x,y) outside U as well.
This proves the claim. Polynomial contexts may contain arbitrary quantified
subterms; ordinary identity substitution applies to all such contexts.

Thus the obvious equality obstruction to arbitrary algebra products is
absent in a B-essential quotient. U provides Boolean bivalence, correct
literal typed identity, and the surviving beta and logical-equivalence
identities. It also gives the one-sided quantifier clauses: truth of a
universal implies truth of each instance, and truth of an instance implies
truth of the existential. These follow from equationalized C logical laws.
The reverse existential clause, supplying an actual domain witness, remains
unproved.

### 15.2 A genuine C-model extension exists, but can add witnesses

Name every Q-element by a constant. Evaluate closed terms in Q and let
T_U contain exactly the closed sentences whose proposition values belong
to U. This is complete and C-consistent. To verify consistency, any finite
C-proof of contradiction from its members would give a C-theorem asserting
that their conjunction implies ⊥. The corresponding term is identically
⊤ in every C-model, uniformly in its finitely many named parameters; hence
that equational identity holds in A and in Q. The Boolean ultrafilter laws
then contradict membership of all those premises in U.

By ordinary completeness, T_U has a genuine C Henkin model R. All the
term-operation equations and all literal disequalities of Q occur in T_U,
by §15.1, so Q embeds in the full term algebra of R, preserving U's truth
on named propositions. Its pure B diagram is unchanged, so R satisfies Max.
R can contain additional entities needed as quantifier witnesses. Nothing
here shows Q itself is Henkin-closed or that B remains essential in R.

One can quotient R maximally while preserving B, obtaining another essential
algebra Q'. The restriction Q→Q' is injective: a nontrivial kernel on Q
would, by essentiality, identify two B-elements. Thus alternating Henkin
extensions and essential quotients gives embeddings between the essential
algebra stages. This observation alone does not make a limit a Henkin
model, because quotienting can destroy truth of the selected witnesses.

### 15.3 The witness-loss obstruction occurs in the original profile model

Let R be the original singleton pure-profile root, and project each entity
to its pure a-term component profile. This is a homomorphism of the FULL
term language onto B; its kernel preserves B, and the quotient is B itself,
which is automatically B-essential. The kernel is maximal among B-preserving
congruences, since any further nontrivial quotient of B identifies B-elements.

Restrict R's actual Boolean truth to B_t. Actuality is true in R, but no
actual true atom is denoted by any pure a-term U(a), by the previously proved
r.e.-Max obstruction. Let F(p) be the pure predicate expressing that p is
true and is an actual world proposition (equivalently a true Boolean atom).
Then under this restricted truth assignment,

    ∃p F(p) is true,       but F(U(a)) is false for EVERY pure a-term U(a).

All elements of B_t are such terms. Thus this particular essential quotient
with this natural truth ultrafilter fails the existential witness clause.
The pure proposition expressing Actuality survives the quotient, while all
its named witnesses are absent. A Henkin extension supplies new ones; the
profile quotient can remove them again. No naive alternating-chain argument
may claim convergence to Henkin closure merely from essentiality.

This example does not prove that B, or another essential quotient, has no
OTHER perfect truth ultrafilter. It isolates the remaining issue: selecting
truth and existential witnesses compatibly with the B-preserving quotient,
rather than recovering literal equality or the Boolean truth laws.

## 16. Full essentiality is equivalent to modal-ideal essentiality

Let A be the full term algebra of a genuine C model and B its embedded pure
a-term algebra at a Max point. This section identifies the full congruence
criterion with the proposition-level ideal criterion in the essential-
extension companion note, rather than merely comparing their conclusions.

### 16.1 A modal ideal induces a congruence at every type

Let I be a Boolean ideal of A_t closed under ◇. Define, at EVERY admitted
type σ including e,

    x ~_I y  iff  (x≠_σ y) belongs to I.

The equationalized logical laws for identity imply

    neq(x,x)=⊥,
    neq(x,y)=neq(y,x),
    neq(x,z)≤neq(x,y)∨neq(y,z),
    neq(F(x_1,...,x_k),F(y_1,...,y_k))≤∨_i neq(x_i,y_i)

for every term operation F, uniformly in any additional parameters. The
last inequality is ordinary substitution of identicals, converted to a
Boolean order identity. It includes operations with quantified subterms.
These identities prove that ~_I is an equivalence relation preserved by
every term operation, hence a many-sorted congruence.

At t, neq(p,⊥)=◇p. Thus if I contains any nonzero p, modal closure gives
p~_I⊥, so the congruence is nonidentity. If I avoids every nonzero element
of B_t, it restricts to equality on EVERY B-sort: distinct b,c∈B have
neq(b,c)∈B_t nonzero, by the genuine C identity semantics (equivalently the
common ground identity diagram). This proposition cannot belong to I.

### 16.2 Equivalence of the two essentiality conditions

If B is essential in A for full term congruences, §16.1 shows that every
nonzero ◇-closed Boolean ideal of A_t meets B_t nontrivially.

Conversely, let θ be a nonidentity full term congruence on A. Its zero
class I_θ={p∈A_t:p θ ⊥} is a Boolean ideal and is closed under ◇, since ◇
is a term operation and ◇⊥=⊥. Choose distinct x,y with x θ y. The nonzero
proposition neq(x,y) is θ-equivalent to neq(x,x)=⊥. Hence I_θ is nonzero.
If every such ideal meets B_t, some nonzero b∈B_t is θ-equivalent to ⊥,
so θ identifies two B-elements. This proves full essentiality.

Therefore, for genuine C term algebras,

    B is full-term essential in A
      iff every nonzero ◇-closed ideal of A_t meets B_t nontrivially.

Since a nonzero fixed point r=◇r generates the modal ideal {p:p≤r}, this
is also equivalent to the pure-profile density condition: every nonzero
possibility-fixed r has some nonzero b∈B_t below it. For the converse, any
nonzero modal ideal contains a nonzero fixed point ◇p.

### 16.3 The maximal quotient can be chosen propositionally

If θ is maximal among full congruences preserving B, its zero ideal I_θ
avoids nonzero B_t. We always have θ⊆~_{I_θ}: x θ y gives neq(x,y) θ⊥.
The latter congruence preserves B by §16.1, so maximality gives equality.
Thus every such maximal quotient is fully determined by its modal zero
ideal. Conversely a maximal ◇-closed ideal avoiding nonzero B_t induces
a maximal B-preserving congruence: a proper extension would have a larger
zero ideal, unless it had the same zero ideal; in the latter case it would
still be contained in the induced ~_I and hence could not properly extend it.

This is an algebraic reduction, not a Henkin-closure theorem. The original
profile projection R→B remains an example of such a maximal quotient whose
inherited truth assignment loses existential witnesses, as in §15.3.

## 17. Exact normalization to a strong-modal disjunction property

Write H(P)=Box_ne(P) and D(P)=not H(not P). The exact H/D theory of an SP
model is already established in the session notes
`sp-diagram-hat-audit.md` §§1–3 and `strong-possibility-degree.md` §2. Its
underlying Max-reflection implication is stated in the author-hosted July
2022 *Classicism* draft, §2.6, printed p.42; that version differs from the
May 2023 draft normally cited by the bundle. The calculations below audit
that result and extract a new equivalent form of the remaining disjunction
question. No literature-priority claim is made.

### 17.1 Finite pure witnesses for every Max-forced H statement

If M proves a closed pure P, choose the finitely many additional Max axioms
K_1,...,K_n used in one proof, and put K=their conjunction, with K=top when
n=0. Each K_i is a disequality. NI and the S4 laws prove in C that

    K_i=Diamond K_i,     hence K=Diamond K.

For the conjunction assertion, monotonicity gives Diamond K≤K_i for every
i, while reflexivity gives the reverse inequality K≤Diamond K. The
ordinary deduction theorem gives C proves K→P. Necessitating this genuine
C theorem gives the Boolean order identity K≤P. Since M proves K, it also
proves K≠bottom. Therefore the single CLOSED PURE term K witnesses

    H P  iff  exists r [r≠bottom and r=Diamond r and r≤P].       (17.1)

In particular,

    M proves P  iff  M proves H P.                            (17.2)

The reverse uses factivity. Neither direction permits ordinary Box
necessitation of optional Max axioms. The result also settles one small
part of the named-witness question: a Max-forced existential of the special
form H P always has a Max-provable pure closed witness. It does not supply
witnesses for an arbitrary existential sentence merely equivalent to H P.

The standard SP argument now gives, in every SP model and for every closed
pure P,

    H P is true  iff  M proves P;
    D P is true  iff  M+P is consistent.                      (17.3)

If M does not prove P, the SP instance D(not P) refutes H P; if M+P is
inconsistent, (17.2) applied to not P refutes D P. All assertions remain
conditional on an SP model existing.

### 17.2 Existential identity formulas are exactly H-stable

Let E=exists xbar theta(xbar), with theta any finite Boolean combination
of typed term identities. The terms may contain arbitrary quantifiers.
Then

    C proves E ↔ H E.                                       (17.4)

For a positive identity I, NI and Box≤H give I→H I. For a negative identity
not I, NI gives Diamond(not I)→not I, so not I itself witnesses H(not I).
Put theta into disjunctive normal form. Normality of H combines finitely
many necessary literals within a branch and lifts each branch to theta,
yielding theta→H theta. The C theorem theta(xbar)→E then gives
H theta(xbar)→H E. Existential elimination proves E→H E; factivity gives
the reverse. No Barcan principle or quantified truth-to-top conversion is
used.

Conversely (17.1) puts every H P in the existential-identity fragment:
r≤P is the equation r∧P=r. Thus the remaining SP consistency question can
be stated using ONLY one proposition witness and one disequality in each
branch.

### 17.3 The exact strong-modal disjunction criterion

The following are equivalent:

1. Pure SP is consistent.
2. M has the existential-identity disjunction property.
3. For every pair of closed pure P,Q, if M proves H P∨H Q, then M proves
   P or M proves Q.
4. For every pair of closed pure P,Q, if C proves H P∨H Q, then M proves
   P or M proves Q.

The equivalence of 1 and 2 is the previously established universal-core
criterion. For 2⇒3 use (17.1) to apply identity DP, then factivity. For
3⇒2 replace existential identity E,F by H E,H F using (17.4). Clearly
3⇒4. For 4⇒3 let K be a finite conjunction of Max axioms such that

    C proves K→(H P∨H Q).

Both K and not K imply their own H. For K this follows from the conjunction
of the disequality literals; for not K, a finite disjunction of positive
identities, use NI and normality. Under K, either H P or H Q implies,
respectively, H(K→P) or H(K→Q). Under not K, H(not K) implies both of
these. Consequently

    C proves H(K→P)∨H(K→Q).

Apply 4. Since M proves K, either resulting implication gives M proves P
or M proves Q. This proves 3.

Thus any failed DP can be normalized to a C THEOREM of the form

    exists r [r≠bottom and r=Diamond r and r≤P]
      or exists s [s≠bottom and s=Diamond s and s≤Q],

where neither P nor Q is a theorem of M. This is a narrower search target
than arbitrary mixed identity diagrams. Ordinary H-DP for C is false:
a contingent pure identity I gives C proves H I∨H(not I), while C proves
neither I nor not I. Criterion 4 explicitly uses M in its conclusion, so
Max's decision of I removes that example.

### 17.4 Iterating H and D creates no immediate contradiction

H is a normal S4 modality, so HH P↔H P and DD P↔D P are C theorems.
Their exact-theory readings agree with the established reflection:

    M proves H P iff M proves P;
    Cons(M+D P) iff Cons(M+P).

For the second equivalence, P→D P gives the easy implication. If M+P is
inconsistent, M proves not P and therefore H(not P), contradicting D P.
For mixed iterations, (17.3) gives precisely

    H(D P) is true in SP iff M proves D P;
    D(H P) is true in SP iff Cons(M+H P).

There is no proof here that M proves D P iff M proves P, or that
Cons(M+H P) iff Cons(M+P). Either unproved substitution would impose extra
modal collapse. The repeated-modality calculation therefore checks
compatibility; it does not settle the remaining mixed cases or establish
SP consistency.

## 18. Two final scope checks

### 18.1 The mixed supported root preserves all pure-profile atom laws

The source in §14 satisfies more than the displayed laws Atom(A_n). For
any relational type sigma, let B_sigma be the Boolean algebra of pure
one-individual terms T(a), modulo C(a)-provable identity. The independently
proved profile-atom criterion in `sp-henkin-minimal-20261022.md` §15 says:

    [T(a)] is an atom of B_sigma
      iff M+forall a Atom_sigma(T(a)) is consistent.

Its proof also shows that, whenever [T(a)] is such an atom, T(a) has EMPTY
actual extension in every M model, for every actual a. Otherwise the
finite pure profile yielding an actual tuple would give a consistent r.e.
extension of C that entails all Max axioms, contrary to the established
r.e.-Max obstruction.

Apply this fact at every root object of the §14 construction. Every root
coordinate of the source pure entity T(a) is empty, since all root objects
satisfy M and the transported a is an individual there. Its component
profile is the atom [T(a)]. For any source entity X, its component profile
is some pure [U(a)]. Hence [T] meets [U] as either zero or [T]. The actual
root coordinates of T meet X are all empty. Equality of all root
coordinates and all component profiles therefore gives T meet X=bottom
or T meet X=T. T itself is nonzero by its nonzero profile. Thus T is an
atom in the source Boolean algebra.

Consequently §14's single source simultaneously satisfies EVERY consistent
pure one-individual atom law, at EVERY relational type, together with its
stated Actuality and relational-choice failures and its target reflection
package. This strengthens that partial-model result, not the claim to an
SP model. Its finite root set still has the obstruction of §7.

### 18.2 The H-clopen special case remains unresolved

A necessary consequence of the criterion in §17.3 is that M decides every
closed pure P for which C proves both P↔H P and not P↔H(not P). Equivalently,
P and its complement both have existential Boolean-identity definitions.
This complementary-branch case is strictly a smaller target than the full
relative disjunction property; no reduction from all disjunctions to this
case has been proved.

The following easy fragments cannot supply a counterexample:

* Every finite Boolean combination of closed pure identities is decided
  by M. In particular M decides any pure formula C-equivalent to a finite
  Boolean combination of ordinary Box A and Diamond A terms.
* If C proves P→Box P, then C proves P↔(P=top), so M decides P.
* ND at type t and ordinary modal 5 are already refuted by M. As a direct
  finite-ground check choose p=E_1. The singleton extensional model shows
  C does not prove p=bottom; a fixed two-individual extensional model shows
  C does not prove Diamond p=top. Thus M proves p≠bottom and
  Diamond p≠top. ND_t at (p,bottom), or modal 5 at p, contradicts these.

The last exclusion is ALREADY DERIVED in the proved-only local engine:
`distinctness-necessary-t-implies-modal-five`, then
`modal-five-implies-modal-b`, then `modal-b-implies-pure-b-r`, then
`pure-b-and-pure-possibility-incompatible`. The direct argument is a
candidate elimination, not a new database consequence.

The familiar undecided examples E_1, relational choice, and the atomicity
packages considered here do not supply the required two persistence
implications; the retract models expose failures of the proposed H
persistence. The conditional genuine-model joint-embedding route, and an
abstract counterexample showing why positive equation reflection alone is
insufficient for that route, are independently worked out in
`sp-henkin-minimal-20261022.md` §§22–23. Those arguments have been
cross-audited, but the required C-specific embedding theorem has not been
proved. No explicit failed disjunction, and no general SP model, has been
obtained in this lane.
