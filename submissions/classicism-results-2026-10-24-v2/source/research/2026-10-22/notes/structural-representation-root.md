# Structural representation and individual configuration principles

Research notes, 22 October 2026. Original arguments developed in this research
chat; attribution for any proposed record is `misc`, not a cited paper. No
novelty claim, human check, or Lean verification is asserted. The database and
its published/human proofs have not been edited.

## 0. Framework and status

Write T for the fixed C plus **boxed** Plenitude, equivalently C + boxed ND +
Atomicity. Write T+FC for C + boxed Functional Choice. Types are those of the
bundle: e and t, with sigma->tau only for tau != e. A map into individuals is
always represented by a relational graph, not a forbidden e-valued function
type. All schemas and finite tuples are metalinguistic.

The proved-only Engine, queried with optional assumptions in its premise set,
confirms that T gives boxed ND/S5, BF, Actuality, Atomicity, Boolean Completeness,
Rigid Comprehension and Functionality, and No Pure Contingency. These are
recorded consequences, not discoveries in this note. Direct local sources:

* `results/c5-and-atomicity-imply-necessary-plenitude.yaml`, Classicism draft
  16 May 2023, section 2.3, p. 33.
* `results/c5-and-atomicity-imply-necessary-completeness.yaml`, Proposition
  2.6, pp. 25–26, using Proposition 2.5.
* `results/c5-and-actuality-imply-rigid-comprehension.yaml`, Proposition 2.10,
  pp. 29–30 and note 41.
* `results/c5-and-atomicity-imply-no-pure-contingency.yaml`, whose atom-swap
  proof is attributed separately to the sources recorded there.

Here `At(w)` means the type-t atom predicate. Every world has a unique true
atom; atoms, identities and algebraic entailments are noncontingent in T.
Rigid relations are precisely those whose pointwise truth values are
noncontingent. Whenever a proof invokes this simplification it uses T, not C
alone. `R~X` means current coextension, never identity.

Detailed companion notes, authored by research subagents in this chat:

* `.reproduction/classicism-research/structural-world-representation.md`: canonical
  slicing/decoding, atom factorization, internal Cantor–Bernstein, finite-arity
  transfer and the pseudo-finite countermodels.
* `.reproduction/classicism-research/structural-mixing-models.md`: choice as local-to-global
  extensional witnessing; full support-restricted Henkin constructions.
* `.reproduction/classicism-research/structural-algebraic-core.md`: partitions and complete
  subalgebras, nominal world models, complete Boolean maps and evaluations.

These paths identify work in progress, not external literature.

## 1. Canonical slicing, and the genuine strengthening

For R of type sigma-t define its slice at an atom w by

    R_w(x) := box(w -> R(x)).

This is a rigid property; at a world where w is true it is coextensive with R.
Every R is reconstructed by

    R(x) <-> exists w (At(w) and w and R_w(x)).

More generally every internally admitted rigid family F(w,x), restricted to
atom w, is decoded by this same existential formula, and slicing recovers F.
Thus asking for representation of admitted rigid world-indexed families adds
nothing to T. Neither this nor internal Boolean Completeness asserts that
every external family is admitted in a Henkin model.

Here is a genuinely additional axiom. At argument type sigma put

    EU_sigma := exists R^(sigma t) forall X^(sigma t)
                  (Rigid(X) -> diamond forall x (R(x) <-> X(x))).

It says that a single property's possible extensions include every rigid
extension. At e it is a natural unrestricted recombination principle for one
property of individuals. Its restriction to rigid X is essential: omitting
it makes the formula inconsistent by taking X = not R. It asks about
coextension; replacing coextension by identity also fails in nontrivial cases
because identities are rigid.

For a rigid X define its complete pattern cell

    c_X := forall x (R(x) <-> X(x)).

Then EU(R) simply says every c_X is possible. Equivalently the canonical
slice map w |-> R_w maps the atoms onto all rigid sigma-properties.

## 2. A diagonal prohibition, with exact type boundary

**Theorem.** T refutes EU_sigma whenever there is an internally represented
rigid injection from world atoms into objects of type sigma. In particular
T refutes EU_sigma at every relational argument type sigma != e.

Fix such an injection j and any proposed R. Define

    D(y) := exists w (At(w) and y=j(w)
                     and not box(w -> R(j(w)))).

This is rigid: atomhood, identity, and the boxed clause are noncontingent,
and BF transports the quantification. Injectivity gives, for any atom w,

    D(j(w)) <-> not box(w -> R(j(w))).

At a world where w is true, the atom's settling property gives

    box(w -> R(j(w))) <-> R(j(w)).

Consequently R and D disagree at j(w) there. Every world has a true atom,
so they never coextend. This refutes the required instance of EU.

For relational sigma = bar-rho-t, use j(p) := lambda bar-z . p. This map is
injective: all argument domains are inhabited, so equality of the two constant
relations gives p=q by application (and the available Functionality laws).
The empty argument tuple is sigma=t itself. Thus an all-type EU schema is
inconsistent. The individual-type restriction is mathematically substantive,
not a silent omission of difficult higher types.

## 3. Explicit full S5 models, even with boxed Functional Choice

For nonempty sets E,W, form the standard full constant-domain S5 model:
D_e=E, D_t=P(W), and D_(sigma tau) consists of all functions D_sigma -> D_tau.
Application is ordinary application, lambda is the interpreted function,
truth at w is membership in the proposition subset, and identity is actual
equality (hence its proposition is W or the empty set). This validates C;
all relational atoms are singleton world/argument pairs; identities give
boxed ND. Thus it satisfies T. In ZFC every total relation has the required
pointwise choice and all resulting operations are admitted, so boxed
Functional Choice holds at every world.

Rigid sigma-properties correspond exactly to subsets of D_sigma. A property
R is a matrix W x D_sigma -> 2. Hence in these full models

    EU_sigma iff there is a surjection W -> P(D_sigma).

In ZFC this is |W| >= 2^|D_sigma|. The cardinal characterization concerns these
full models; the internal slice characterization of section 1 is the version
valid in arbitrary Henkin models.

In particular, with E=N:

* W=N refutes EU_e by Cantor, while satisfying boxed Functional Choice and
  the quantified Axiom of Infinity at e.
* W=P(N) satisfies EU_e: take R(x) true at world A exactly when x belongs to A.
* W=P(P(N)) also satisfies EU_e, by any surjection onto P(N) (choice is
  available in this construction).

Thus EU_e is a genuine additional consistent commitment even over boxed
Functional Choice with actual infinitude of individuals. This is not just a
weak choice fragment already implied by the preferred choice package.

The entire schema of EU at finite individual arities is jointly consistent:
take W=P(E^{<omega}) and use membership on each tuple-length component. This
construction does not put a forbidden e-valued function type into the object
language.

## 4. Distinguishability is a separate commitment

For R^(et), let Sep(R) assert that any distinct world atoms w,v differ on
some instance R(x):

    forall w,v (At(w) and At(v) and w!=v ->
                 exists x ((w<=R(x)) xor (v<=R(x)))).

Put S_e := exists R Sep(R). This says one family of individual facts
distinguishes all worlds. Equivalently its slice map w |-> R_w is injective.
This is independent of surjective EU_e, even over boxed Functional Choice
and the quantified Axiom of Infinity at e.

In a full S5 model S_e holds iff W injects into P(E), hence in ZFC iff
|W| <= 2^|E|. For E=N:

* W=N: S_e true and EU_e false.
* W=P(N): both true, witnessed by the same membership matrix.
* W=P(P(N)): EU_e true and S_e false by Cantor.

These are strict model separations, not an inference from missing arrows.
Both principles are closed pure sentences, so their unboxed and boxed forms
are equivalent over T by the recorded No Pure Contingency theorem. This is
not an unrestricted use of necessitation under optional hypotheses.

**Algebraic equivalent definition.** S_e says that the proposition algebra
has an internally complete Boolean generating family indexed by individuals.
More explicitly, for its witnessing R, every rigid complete Boolean subalgebra
G of t containing all R(x) is the whole proposition algebra. Completeness here
quantifies only over admitted index properties. Proof: if w,v have identical
R-profiles, {p : w<=p iff v<=p} is a proper complete subalgebra containing the
generators. Conversely, separation makes each atom w the meet of its literals
R(x) or not R(x), chosen according to w's profile. A complete subalgebra
containing the generators therefore contains every atom and then their
admitted joins, including every proposition. The companion algebra note
checks the internal meets and rigidity in detail.

For rigid X the pattern cell c_X is either bottom or a single atom exactly
when Sep(R) holds. Thus a property simultaneously witnessing EU and Sep has
exactly one world for each complete rigid individual profile.

## 5. Exact configuration spaces and where Choice enters

Over T+FC, EU_e and S_e together imply that one R witnesses both. Let A be
the atoms and B the rigid et-properties. A separating predicate gives an
injection f:A->B; a universal predicate gives a surjection g:A->B. Functional
Choice at output type t supplies a section i:B->A of g, hence an injection.
Internal Cantor–Bernstein yields a bijection h:A->B. Its graph can be chosen
rigid; decode that rigid world-indexed family to obtain the desired R.

There is no reliance on external fullness or untyped set collection here.
For the Cantor–Bernstein construction use A0=A\i[B] and the intersection D
of all rigid A-subsets containing A0 and closed under i o f. Impredicative
comprehension supplies D; minimality gives D=A0 union i[f[D]]. The bijection
uses f on D and the unique inverse of i on A\D. The two branches are disjoint
and cover B by that displayed identity. This proof is fully expanded in the
world-representation companion note.

One should retain the Choice hypothesis when deriving a section of the
surjection; its omission is not justified by the above argument.

Exact configurations alone do not imply Choice. A concrete ZFC Henkin model
has E an infinite set of atoms, G=Sym(E), W the finite/cofinite subsets of E,
D_t the finitely supported subsets of W, and every admitted higher function
domain the finitely supported functions between the already constructed
domains. Standard parameter-equivariance verifies lambda/comprehension;
singleton world/tuple relations give Atomicity and identity is rigid. Thus
T holds. R(x)={w:x in w} is equivariant. Rigid et-properties are exactly the
finite/cofinite subsets of E, so R gives exact configurations. Choice from
all two-element subsets of E is impossible: a transposition outside any
finite support fixes the pair but moves a selected member. Intensional
Choice at e also fails: at a two-element world w require a selected member
of w; the same transposition fixes w and moves both eligible individuals.
The mixing-model note supplies the full hierarchy construction and checks.

## 6. Arity and infinitude guardrails

Write EU_k for the k-ary individual version. A rigid injection of tuples
E^j into E^k transfers EU_k to EU_j by pullback and extension by false off
the image. Thus EU_(k+1) implies EU_k by padding tuples with a fixed
individual. If a rigid pairing injection E^2->E exists, all finite arities
collapse and a single universal unary property can encode joint arbitrary
finite collections of finite-arity individual relations.

Do not silently replace that pairing premise by the Infinity Schema.
For every finite n>=2 the full model E=n,W=P(E^k) satisfies EU_k and fails
EU_(k+1). A nonprincipal many-sorted Henkin ultraproduct of these finite
models satisfies boxed Functional Choice and every Infinity-Schema instance
at e, while still EU_k and not EU_(k+1). Its e-domain remains internally
finite in the impredicative Frege sense; it fails the quantified Axiom of
Infinity. The companion note details why the ultraproduct is a Henkin model,
not externally full.

The stronger implication has now been proved and independently audited:
boxed Functional Choice plus the quantified Axiom of Infinity supplies a
rigid pairing injection E^2->E. The world-representation companion's Theorem 7
gives a typed proof of the usual infinite-cardinal-square argument. It uses
an admitted well-order, the least bad initial segment, the pair-order by
(maximum coordinate, first coordinate, second coordinate), and comparison
by the admitted union of partial initial-segment isomorphisms. Its internal
Frege-finiteness induction obligations are spelled out. Thus all positive
finite-arity EU principles are equivalent under this stronger Infinity
assumption; the pseudo-finite models explain why the schema cannot replace it.

## 7. Infinitary language: an exact useful simplification

This section extends the language; it is **not a theorem of fixed C**.
Let H_omega allow countable conjunction/disjunction with a common finite set
of free variables, countably branching well-founded introduction/elimination
proofs, and lambda-comprehension for these formulas. Let C_omega add Logical
Equivalence for H_omega theorems. The numeral cardinal terms C_n=Suc^n(0)
are already available in the finitary language.

Define N_omega(Z) := bigvee_(n<omega) Z=C_n. This is an admitted property,
contains 0, and is successor-closed. The impredicative definition of
FiniteCardinality therefore gives FiniteCardinality(Z) -> N_omega(Z).
Conversely every C_n is in every inductive property by its ordinary finite
derivation; disjunction elimination gives N_omega(Z) -> FiniteCardinality(Z).
This equivalence is a theorem of H_omega, so the corresponding lambda
properties are identical by Logical Equivalence. No optional hypothesis has
been improperly necessitated.

Consequently, in C_omega the Infinity Schema at e implies the quantified
Axiom of Infinity: the universal individual property has none of the
standard finite cardinalities, while N_omega exhausts FiniteCardinality.
The reverse implication is already finitary. This gives a simpler equivalent
definition in the extended language and explains exactly which Henkin
pseudo-finite phenomenon the infinitary resource removes.

Important semantic distinction: a countable formula using a common finite
parameter set need not give external countable completeness for arbitrary
unrelated parameter sequences. All full finite-support hierarchies above
remain closed under the former, by equivariance under the same finite
stabilizer. Allowing countably many independent parameters is stronger: their
supports need not have finite union. The countable-support construction in
the mixing note survives that stronger closure and still refutes general
Relational Choice. Thus infinitary conjunction by itself must not be treated
as a synonym for external fullness or unrestricted Choice.

## 8. Definition audit and assessment

Recommended transparent alternatives, each with its exact assumptions:

* In T, a relation is the decoded rigid family of its world slices; world
  slicing is definable, not an additional representation axiom.
* EU_e: every complete rigid individual pattern has a nonempty cell.
* S_e: every such cell is empty or a world atom; equivalently an individual-
  indexed family completely generates the internal proposition algebra.
* Exact configurations: those cells are precisely the world atoms, one each.
* In the explicitly extended C_omega, impredicative finite cardinality is
  the countable disjunction of the standard numeral cardinalities.

EU_e and S_e are candidate substantive commitments, not conclusions that
they are philosophically true. Their consistency and independence over the
strong choice package are model-backed. Their higher-type limitations and
the distinction between internal completeness and external powersets are
part of the results, not optional caveats. This lane does not establish that
Maximalist C has no attractive consistent strengthenings.

## 9. A much weaker, simple obstruction to Maximalism

The following equivalence is an original derivation in this chat, independently
audited by the world-representation subagent. It is over **C alone** and needs
neither BF, Atomicity, Plenitude, nor Choice.

Define Bivalent Retraction (BR) by

    exists E^(tt) [E(top)=top and E(bottom)=bottom
                   and forall p (E(p)=top or E(p)=bottom)].

Thus the two settled truth values form a retract of the propositions. There
is no requirement that E preserve actual truth. This is strictly weaker than
the parent's Bivalent Evaluation principle, whose additional truth condition
gives ND and Actuality.

**Theorem.** BR is equivalent over C to the convergence axiom .2:

    forall p (diamond box p -> box diamond p).

BR implies .2. Suppose both diamond box p and diamond box not-p. At the first
possible point, p=top, so E(p)=E(top)=top; at the second, p=bottom, so
E(p)=E(bottom)=bottom. The endpoint identities are necessary by NI. But at
the evaluation point E(p) is one of top,bottom, and that identity too is
necessary by NI. The two possibilities therefore contradict each other.
Negating diamond box not-p gives the desired box diamond p.

Conversely assume .2 and put E(p):=diamond box p. Applying .2 to box p, and
using 4 to pass from box p to box box p, gives E(p)->box E(p). Its negation
is box not-box p, which is persistent by 4 as well. Thus each E(p) is
necessarily true or necessarily false, exactly E(p)=top or E(p)=bottom.
The endpoint identities follow from the modal theorems at top and bottom.
This explicitly defined E witnesses BR.

**Maximalism refutes BR, already at one pure .2-instance.** Let P be the
closed pure sentence that there are two distinct individuals. A one-world
full model with two individuals validates box P; a one-world full model with
one individual validates box not-P. Consequently both pure sentences are
consistent with the fixed reference C. Maximalism's possibility form gives
diamond box P and diamond box not-P, which contradict .2 at P. The argument
preserves the reference-theory side condition exactly; it does not change C
to a stronger reference theory.

**Strictness and consistency.** The full two-world chain model with a
two-element root individual domain mapping onto a singleton at its terminal
world validates .2 (its S4 frame is directed), hence BR, while root ND fails
because the two individuals merge. Equally, the singleton-individual
two-world chain already has distinct root propositions that merge at the
terminal world. In either case BR can be seen directly as evaluation at the
terminal world, an admitted normal bivalent operation. Thus BR does not
smuggle in ND or the whole positive package.

This is formal support for a precise contrast: boxed Functional Choice
supplies a bivalent retraction, whereas Pure Maximalism rules out even that
weak resource. It is not a proof that finitary Maximalist C is inconsistent
without an additional principle, nor that the positive package is logically
valid in all C-models.

### Simpler equivalent definitions and the Gallin consequence

BR is equivalent to the existence of any nonconstant operation E:t→t whose
current values are all top or bottom. If E(a)=top and E(b)=bottom, then
F(p):=E((p∧a)∨(¬p∧b)) has the required endpoint values. The same pointwise
interpolation works at any relational input type τ. Conversely a BR witness
gives a nonconstant bivalent test on τ by evaluating an input relation at one
fixed tuple and then applying E. Hence .2 is exactly the possibility of a
nontrivial bivalent classification at any fixed relational type.

Pure Maximalism therefore makes every admitted bivalent predicate on each
relational type constant on its CURRENT domain. At e, the same conclusion
follows from Maximalism's possibility of there being just one individual:
two current arguments with different endpoint values could not merge, by NI.
For finite tuples, change one coordinate at a time. Consequently every
Gallin-rigid relation has empty or universal current extension, since Gallin
rigidity is exactly necessary bivalent range (Persistence of F and of ¬F).

This does NOT identify the relation-object with the bottom/top relation.
Functionality and BF are absent, and future domains can contain additional
arguments. It also does not refute ND_e at a singleton current domain. The
precise result is the failure of nontrivial current bivalent classification.

## 10. Full Choice as splitting of complete Boolean subalgebras

This is proved in `structural-algebraic-core.md` §16 and independently audited
by the world-representation and mixing-models lanes. All claims in this
section are over T=C+□Plenitude and concern admitted internal families.

For a rigid internally complete Boolean subalgebra A of the relational
Boolean algebra B_τ, a complete Boolean retraction is a complete unital
Boolean homomorphism H:τ→τ such that all Hp belong to A and Hq=q for q∈A.
Range equality and H²=H follow, so they need not be separate conditions.

**Theorem.** The schema that every such A retracts, at every relational type,
is equivalent to □Functional Choice. It is enough to require it for the
property types σt as σ ranges over all types.

Complete subalgebras correspond to admitted equivalence relations on the
atoms: their elements are exactly the unions of equivalence classes.
Complete endomorphisms are inverse-image maps of admitted atom maps. A
retraction onto the class-union subalgebra is therefore exactly a map that
chooses one representative per class and is constant on that class.
This proves the Choice-to-retraction direction.

For the converse, let S be an equivalence on arbitrary type σ, including e,
and rigidify its actual extension. Fix an atom a of t and embed the objects
of σ into atoms of B_{σt} by j(x):=λy(a∧y=x). Extend S to those atoms by
declaring j(x) equivalent to j(y) exactly when Sxy, with every other atom a
singleton class. Retraction supplies a transversal of this atom partition;
pullback along j is a transversal for S. Thus Transversal Choice holds at
every type. The recorded TC→Relational Choice implication and Plenitude
give Functional Choice, and T's No Pure Contingency boxes the closed pure
instances. This last step is not necessitation under an optional assumption.

The phrase “all complete Boolean inclusions split” abbreviates this theorem
only if inclusions into internally represented subalgebra fields are included.
It must not be restricted to maps between entire algebras B_ρ and B_τ.
Also preserve the direction: complete Boolean SURJECTIONS between
NONTRIVIAL algebras already split in T. Their dual atom maps are injective,
and an inverse on the image extended
by one default atom suffices. Splitting complete INCLUSIONS requires a
section of a surjective atom map, which is the Choice content.

### The propositional instance is strictly weaker

Ret_t means transversals only for admitted equivalence relations on world
atoms. It and Intensional Choice (IC) are independent, even with genuine
quantified Infinity at e:

* Nominal worlds W=J×2 under pair flips and permutations of pairs, with finite
  mate-closed supports and fixed E=ω, satisfy IC at every type. Generic orbit
  transport selects local witnesses. The world-pair partition has no
  supported transversal, so Ret_t fails, even for ordinary Boolean retractions.
* Fixed countable worlds and pair-flipped individuals with finite supports
  have a full pure-propositional hierarchy and satisfy Ret_t, but IC_e fails.
* Under all permutations of an infinite world set, finite supports, and
  fixed E=ω, both Ret_t and all IC hold while Relational Choice fails. Every
  supported world equivalence has a finite or cofinite transversal; choice
  of a member from every unordered two-world proposition still fails.

These are Henkin Gallin models in ordinary ZFC, with standard internal finite
cardinalities and quantified Infinity, not metatheoretic choice failures.
Detailed constructions and equivariance/comprehension checks are in
`structural-mixing-models.md` §§13,15–16 and the algebraic companion.

## 11. Removing redundant algebraic machinery from the definitions

Over T, H:t→t is a complete Boolean homomorphism iff it commutes with
negation and propositional universal quantification:

    H(¬p)=¬Hp,                 H(∀p Fp)=∀p H(Fp).

The second identity ranges over admitted F^{tt}; both are identities, not
merely actual equivalences. Taking F as the identity first gives
H⊥=∀p Hp≤H⊤=¬H⊥, hence endpoint preservation. A family with values p and q
gives binary-meet preservation. For any rigid family X, apply quantifier
commutation to ∀p(Xp→p); H fixes the bivalent Xp. This yields all admitted
meets. Conversely complete homomorphisms preserve range-family meets and
therefore every represented indexed quantifier. See algebraic §19.

Thus a world is equivalently a bivalent operation commuting with negation
and quantification; and Complete Retractions can be phrased as retractions
respecting those two operations. The much weaker BR in §9 has neither of
these preservation requirements.

## 12. Finite and even well-order-continuous retractions are weaker

The ordered nominal construction in mixing §§17–19 is an explicit model in
ordinary ZFC. Individuals are Q, G=Aut(Q,<), worlds are two fixed points,
and every relational domain contains all finitely supported functions.
It satisfies T, quantified Infinity_e, all Intensional Choice, and the
following all-type retraction assertion: every internally complete Boolean
subalgebra retracts by a Boolean homomorphism preserving every represented
family indexed by an internally well-ordered field. Nevertheless full
Relational/Functional Choice fails.

The proof is constructive at the model level. Finite supports have a least
support; an object's stabilizer is exactly the pointwise stabilizer of that
least support. Each stabilizer orbit is a finite configuration of ordered
points in intervals. Moving its points to the right past every extra finite
support gives an invariant tail ultrafilter. For each partition-class orbit,
choose one class externally and transport its stabilizer-invariant ultrafilter.
The resulting uniform family has one finite support. It defines a Boolean
retraction, with ultrafilter decisions replacing principal point decisions.

For a well-ordered index field supported by P, each G_P-orbit is admitted
and has an internal least point. Invariance fixes that point; transitivity
forces the orbit to be a singleton. Consequently every indexed member of
a supported family shares one finite support. A single tail then settles
all its members, proving preservation of that whole meet. This argument
does not assume an internal well-order is externally well-founded.

Choice already fails for the serial individual relation x<y. A selector
supported by S, evaluated at x above S, would select y>x fixed by G_{S∪{x}};
every such y is movable, a contradiction. All admitted natural-number
sequences of individuals have finite range, and every admitted injective
self-map of Q is surjective. Thus genuine Frege Infinity coexists with
internal Dedekind finiteness here. Countable Choice also fails for the
family requesting an n-element subset of Q for each standard Frege numeral
n: one finite selector support cannot contain subsets of unbounded size.

This identifies precisely why completeness matters. A finite-operation
retraction is equivalent to a uniformly represented ultrafilter on each
partition block; a complete retraction forces each ultrafilter to be
principal. The equivalence and its finite-fiber consequence are in algebraic
§20. No equivalence with the Boolean Prime Ideal Theorem is asserted.

## 13. Separate universality and separation need not share a witness

The following explicit T+Infinity_e countermodel, proved in algebraic §22
and independently audited by both other lanes, settles the Choice caveat
in §5. Let E=Q with G=Aut(Q,<). Let U be all finitely supported subsets of Q
(finite unions of rational intervals and points), and take worlds
W=U\{∅,Q}. Use the full finite-support hierarchy.

Membership R_S(x,w) iff x∈w separates worlds. Each nonconstant profile w has
a least essential breakpoint. Erase that breakpoint by extending the truth
value immediately to its right over the entire left part. The resulting
map f:W→U is equivariant and surjective: prepend a fresh smaller breakpoint
with the opposite left-tail truth value to any desired target profile.
Therefore R_EU(x,w) iff x∈f(w) is universal.

There is no admitted bijection W→U. For any finite support S with n points,
the fixed profiles in U are exactly the unions of its 2n+1 point/interval
orbits, numbering 2^(2n+1). The fixed worlds number two fewer. An S-supported
bijection would restrict to a bijection of these fixed sets, impossible.
Any common exact witness would give just such a bijection. Thus EU_e and
S_e can both hold without an exact witness, even with quantified Infinity.

This model also inherits all-type finite and internally well-ordered-family
preserving retractions: the tail-ultrafilter argument of §12 only needs
finitely supported worlds, not fixed worlds. IC_e fails here, so it is not
claimed. In the positive direction, full Choice in §5 can be weakened to
Ret_t: retract the subalgebra of equal-profile unions for the EU witness,
obtain a transversal/section of its world-to-profile map, and combine that
injection with the separating witness using internal Schroeder–Bernstein.

## 14. The configuration algebra exists before optional profile axioms

T itself constructs the rigid field U_σ of σ-properties and the internally
complete atomic Boolean algebra C_σ of rigid predicates on that field,
empty off the field. Its relative top is U_σ, not the whole ambient type.
Coordinate generators are g_x(Y):=Rigid(Y)∧Yx. This is the free internally
complete ATOMIC Boolean algebra on D_σ, for represented rigid algebra fields.
The proof evaluates generators at target atoms and forms the corresponding
rigid profiles; uniqueness follows from complete literal meets and atom
joins. No Choice or external powerset fullness is used. Relational carrier
fields suffice here; individual-valued maps require functional graphs.

For any fixed R, its canonical complete map Φ_R:C_σ→B_t sends g_x to Rx.
Then EU(R) means Φ_R is injective, S(R) means Φ_R is surjective, and exact
profiles mean Φ_R is an isomorphism. See algebraic §21. These are
fixed-witness equivalences and do not contradict the separate-witness
countermodel above.

## 15. Infinitary syntax: the parameter boundary is essential

The supported Gallin hierarchies admit arbitrary set-sized conjunctions
and disjunctions of formulas with one common finite free-variable set and
a common finite support for any named constants. Equivariance makes the
whole family invariant under the supports of that finite valuation; its
intersection/union and lambda abstractions are therefore admitted. Thus
these explicitly extended L_{∞,ω}-style semantics preserve the Choice and
external-fullness countermodels above. This is not a claim about arbitrary
Henkin submodels, infinite quantifier blocks, or infinitely many independent
object parameters.

If infinitary comprehension permits arbitrary families of object names
without a common support bound, the conclusion changes: arbitrary external
world subsets become joins of their named atoms, arbitrary external object
relations become disjunctions of tuple identities, and Plenitude represents
their unique-valued graphs. That stronger resource forces external fullness
of the relevant fields. The syntax/parameter rule must therefore be stated
whenever an infinitary extension is proposed. See world-representation §17.

There is nevertheless a positive fullness consequence for pure arithmetic,
at a Frege index type with distinct standard numerals (for example under
quantified Infinity of its underlying sort). In C_omega, every external
subset A of that standard Frege numeral field is
named by the parameter-free formula bigvee_(n in A)(x=C_n). Arbitrary
set-sized pure conjunctions iterate this effect through each finite
powerset level over that field. These objects have empty support in the
nominal examples, so arithmetic fullness is compatible with failure of
Choice on anonymous individuals. This is stronger than ordinary finitary
Henkin comprehension, without being external fullness of every object type.

## 16. Choice factors through ultrafilters in two different ways

All assertions here are over T and quantify over admitted rigid fields and
their admitted rigid subsets. See algebraic §§25–31 and mixing §§21–22 for
the complete typed arguments and independent audits.

Write UFC for uniform ultrafilter choice: a serial relation R(x,y) has a
represented family K_x of ultrafilters on the y-properties, each containing
its fiber R_x. Write MC for finite multiple choice: the fibers have a
represented family of nonempty internally finite subfibers. Write FineUF
for a fine ultrafilter on Fin(I) for every rigid field I, containing each
cone {A:i in A}. Then

    finite Boolean retractions at all relational types  <-> UFC;
    boxed Functional Choice  <-> UFC + MC;
    BPI_int  <-> filter extension  <-> UFC + FineUF.

BPI_int explicitly covers arbitrary rigidly represented Boolean algebra
fields and operation graphs, not only Boolean operations inherited from a
relational type. The equivalence to filter extension is proved by typed
quotient-class coding in one direction and ultrafilter limits of finite
Boolean valuation tables in the other. It uses no external quotient,
chosen representative, or unrepresented family.

The first factorization has independently separable factors. Ordered
nominal individuals Q give UFC but not MC: above a fresh x there is no
nonempty finite invariant set of y>x. Independent pair-flipped individuals
give MC but not UFC: each stabilizer orbit is finite, but choosing from all
two-element blocks is impossible. The latter model also gives FineUF, by
external fine ultrafilters on finite sets of its finite stabilizer orbits.
Thus FineUF alone does not give UFC or BPI_int.

The converse separation uses a published set-theoretic model through an
explicit typed interpretation. Howard and Tachtsis, *On the minimal cover
property in ZF* (2014), Remark 4, report a ZFA model with the exact
family-ultrafilter principle UFC but without BPI. Take the full hierarchy
inside that model, with two fixed worlds and an individual field containing
its bad Boolean algebra and its natural numbers. This gives T, all IC,
quantified Infinity, UFC, and failure of BPI_int and FineUF. The typed
interpretation is verified in algebraic §32; the underlying ZFA separation
is literature-dependent, not reconstructed here. The source's precise
printed page for Remark 4 has not been recovered.
[Primary article](https://www.sciencedirect.com/science/article/pii/S016686411400248X).

The ordered nominal models are specifically unavailable for that separation:
they satisfy BPI_int. One direct proof uses the extreme amenability of
Aut(Q,<) and of
its finite point stabilizers. The external compact Stone space of
ultrafilters extending a supported filter has a continuous action of that
stabilizer. A fixed ultrafilter has the same finite support and is therefore
admitted. This is a typed transfer of the established ordered-Mostowski
phenomenon; see [Blass, Partitions and Permutation Groups, §§2–3, pp.2–4](https://janos.cs.technion.ac.il/RESEARCH/AMS-Book-files/pdfs/11_Blass.pdf)
and the explicit transfer in algebraic §31.

Consequently the endpoint-world countermodel in §13 satisfies BPI_int and
FineUF as well as EU_e and S_e, while still having no exact witness.
Boolean prime ideal compactness cannot replace Ret_t in the witness-
combination theorem.

A further original consequence, audited by both other lanes, is

    UFC -> every internally infinite rigid field has a nonprincipal UF.

The proof is worth distinguishing from FineUF. If all ultrafilters on I
were principal, a nonprincipal U on P(I) would define its coordinate-limit
profile v. UFC selects an ultrafilter on each nonempty difference X△v;
their U-sum contains no singleton, a contradiction. Thus every ultrafilter
on P(I) is principal. UFC would then give ordinary choice on all nonempty
subfields of P(I), hence a well-order of P(I). Greedy filter extension along
that well-order extends the cofinite filter of the infinite field I to a
nonprincipal ultrafilter, again a contradiction. Internal finite induction
and represented partial assignments justify both steps. This gives
extension of every represented rigid N-indexed filter base, when N is
internally infinite and its initial segments are internally finite, but
still does not ensure every cone on Fin(I) is large. Moreover UFC is
equivalent to UNIFORM nonprincipal-ultrafilter choice for families of
internally infinite fields: ultrafilter sums uniformize the pointwise
existence theorem; the converse inflates fibers by an infinite field, with
a separate finite-output-field case. See algebraic §33.

The free-ultrafilter argument is independently checked mathematics in this
note, not a novelty claim. Algebraic §33 records an old Howard–Rubin table
entry listing a related implication as then unresolved, and gives the
particularly short ordinary-set-theoretic proof at omega as an additional
check. Current literature priority has not been established.

## 17. The exact scope of pattern compactness

For a specified R, let FI(R) mean that every rigid pattern can be matched
on every internally finite coordinate field. Let PC(R) mean that any rigid
pattern with all such finite matches is realized in full. Over T,

    EU(R)  <-> FI(R) + PC(R).

In full S5 semantics these respectively say that the profile image is the
whole cube, dense in the cube, and closed in the cube. The internally finite
quantifier matters: a nonprincipal ultraproduct of E_n=n and worlds all
proper subsets of E_n has boxed Functional Choice, the standard Infinity
Schema, separation, every standard finite independence instance, and PC,
yet no universal profile family. Its individual field is internally finite.

Universal PC is a much stronger and usually unsuitable condition. Over T
plus boxed Functional Choice,

    forall R PC(R)  <-> Fin(E) or Fin(world atoms).

The sufficient direction needs only finite choice. For the reverse, use
well-orders to match the internally finite predecessor positions of the
two infinite fields. Give each matching world the corresponding finite
coordinate prefix, and other worlds the empty profile. The whole field of
finite positions is finitely matched but absent. This construction is
fully internal, including the cross-type finite-order matching.

The Choice hypothesis cannot simply be removed. In the model with fixed
E=N and finitely supported unordered infinite worlds, every R has a finite
profile image, so every R is compact. Both fields are internally infinite;
Ret_t and all Intensional Choice also hold. Conversely EU_e plus genuine
individual Infinity already refutes universal PC without Choice: truncate
a universal relation to its finite current extensions. Every finite pattern
still occurs, while the full individual field never does.

Even restricting universal PC to separating finitely independent families
is too strong for infinite exact configurations under boxed Functional
Choice. Re-index the profiles bijectively onto all NONEMPTY profiles. The
new family separates and is finitely independent, but omits the empty
profile. Thus compactness is a property of the chosen coordinate family.
Detailed proofs, including the no-Choice truncation supplied by the parent
lane, are in world-representation §§16,18–19.

## 18. Cardinal comparison and its exact Choice boundary

Boxed Functional Choice gives the dichotomy EU_e or S_e: compare the world
field with the field of rigid individual properties by admitted injections.
An injection W->U supplies separation; an injection U->W supplies a
surjection W->U by inversion on its image and one default value. If both
exist, §5 combines them into an exact family. No external-powerset claim is
involved.

T alone does not give this dichotomy, even with Ret_t, all Intensional
Choice and genuine Infinity. In the fixed-E, unordered-world model just
used, every relation has finitely many profiles, so neither EU_e nor S_e
holds. Complete propositional retractions combine witnesses when supplied;
they do not produce either witness.

A precise full-Choice equivalent is injection-comparability of any TWO
admitted rigid fields. It is enough to compare subfields of the same
relational carrier. World-representation §21 gives a complete typed Hartogs
proof: code isomorphism classes of well-orders on subfields of A by their
rigid class predicates; the resulting field H_A is internally well-ordered
and cannot inject into A. Comparability forces A to inject into H_A, hence
to be well-ordered. In fact only these comparisons A versus H_A are needed.

Comparing profiles with the one fixed world field is weaker, even if every
coordinate subfield is allowed. A finite world field makes all these
comparisons hold in the ordered nominal model, where Choice still fails.
That same model supplies a concrete Hartogs obstruction: H_Q is the
standard natural-number field, and neither it nor Q admits an injection
into the other. Arbitrary pure infinitary arithmetic fullness does not
remove this object-domain obstruction.

## 19. Complete evaluation over C: a persistent-atom boundary

Write CE for a bivalent endpoint-preserving E:t->t that also preserves
negation and propositional universal quantification AS IDENTITIES, as in
§11. Over C alone,

    CE -> exists w(Atom(w) and box diamond w) -> BR.

The first implication uses w=forall p(Ep->p). Quantifier commutation and
bivalence give E(w)=top. NI prevents w from becoming bottom, and the
positive and negative E-values make w decide every current proposition.
Conversely, with BF_t the displayed persistent-atom condition gives CE
via E_w(p)=box(w->p). Under BF_t it is also equivalent to exists w box Atom(w).

The identity requirement in CE cannot be replaced silently by a current
biconditional for the SAME evaluator; §22 gives an existential replacement
theorem. BF cannot be dropped from the displayed persistent-atom converse. The full
two-arrow idempotent model has a persistent atom {k}, which becomes top
along k, but no CE: a target-domain quantifier can have a new counterexample
although every current instance is top. The full omega-chain has necessary
Atomicity, .2 and BF_t but no atom that stays possible forever, hence no CE.
The full two-world terminal chain does have CE while ND fails. These are
explicit action-semantic calculations in world-representation §22.

Pure Maximalism consequently entails

    forall w(Atom(w) -> diamond(w=bottom)).

This is possible vanishing of every current atom as an object, not merely
possible ordinary falsity. It follows from BR's .2 characterization and
the fixed-reference pure Maximalist instance in §9, not from any claim that
Maximalist C itself is inconsistent.

## 20. A single propositional formulation of the entire positive core

For E:t->t use the reduced complete-evaluator definition

    forall p [E(p)=top or E(p)=bottom];
    forall p [E(not p)=not E(p)];
    forall F:tt [E(forall p Fp)=forall p E(Fp)].

These are object identities. Endpoint preservation follows already from
the last two clauses: E(bottom)=forall p E(p)≤E(top)=not E(bottom), so
E(bottom)=bottom and E(top)=top. No Functionality or BF is used here.

**Over C, boxed Plenitude is equivalent to complete evaluators separating
distinct propositions.** Equivalently,

    forall p [p≠bottom -> exists E(CE(E) and E(p)=top)].

This is a definition improvement for T, not an additional strengthening and
not a Choice principle. Together with the recorded T+Relational Choice
equivalence, it also gives over C

    boxed Functional Choice <-> CED + Relational Choice.

The factors are independent, even against the C5 background: the supported
T models can fail RC, while §28's generic model has boxed RC and fails T.
The proof of the evaluator equivalence has three short independent steps.

1. A nonzero p has E(p)=top with E(bottom)=bottom. NI preserves both
   identities and prevents p from becoming bottom. Apply this to symmetric
   differences to obtain ND_t.
2. If every current Fp is necessary, but Q=forall p Fp is not necessary,
   choose E recognizing not-Q. Then E(Q)=bottom, while every E(Fp)=top and
   hence forall p E(Fp) is actually true. The quantifier identity contradicts
   this. Thus BF_t holds; no BF was silently used to infer necessity of the
   universal from its current instances.
3. Each CE determines the atom w=forall p(Ep->p), with E(p)=top iff w≤p.
   Thus every nonzero p contains an atom.

The proved recorded chain gives

    ND_t + BF_t -> box ND_t -> box ND_all -> BF_all;
    Atomicity_t + BF_all -> Atomicity_all;
    box ND_all + Atomicity_all -> box Plenitude.

This chain was checked with the proved-only Engine, keeping all assumptions
in the queried premise set. World-representation §26 identifies each owning
record and supplies the full argument. Conversely T supplies E_w for each
atom below a nonzero proposition. A CE is Boolean-homomorphic on its current
arguments by its atom characterization, so recognition of symmetric
differences is equivalent to separating arbitrary distinct propositions.

There is a simpler lower-level comparison. Bivalent endpoint-preserving
operations, without negation or quantifier preservation, recognize every
nonzero proposition exactly when ND_t holds. Under ND_t the single
operation E(p)=diamond p already does this. Thus:

    one bivalent retraction                       <-> .2;
    bivalent retractions recognize all nonzeros    <-> ND_t;
    complete evaluators separate propositions      <-> T.

The first existence claim is strictly weaker than the second: the terminal
two-world chain has CE but a proposition that can vanish. These equivalences
keep the scope of the preservation laws and the number of witnesses clear.

The middle line also has the separation formulation: BR evaluators separate
every distinct p,q iff ND_t. Under ND_t choose a nonzero Boolean difference
d of p and q; E_d(r)=diamond(d and r) fixes endpoints, is bivalent, and
separates them. A single possibility detector need not separate two nonzero
propositions, so that formulation uses the whole available evaluator family.

## 21. The exact local Barcan condition, and a full-action criterion

The BF hypothesis in §19 can be replaced by an exact local condition. Put

    LB_t(w):= forall F [(forall p box(w->Fp))
                         -> box(w->forall p Fp)].

Over C alone, CE holds exactly when there is an atom w with box diamond w
and LB_t(w). Its canonical evaluator is E_w(p)=box(w->p). The proof upgrades
the current quantifier equivalence to identity without global BF: if the
right universal Q is true, LB gives the boxed left side, and 4 plus necessary
universal instantiation gives box Q; a false Q has a current bottom-valued
instance which stays false by NI. Thus Q is bivalent. See world §24.

The full action models have a sharp categorical criterion. At an object A,
CE holds iff there is an arrow h:A->B which is epic and factors through
every outgoing arrow g:A->C. Persistent nonzeroness of the singleton {h}
says that each factorization kg=h exists. A full image-test intension
detects surjectivity of h's proposition transport, exactly epicness. For
the converse, each factor k of epic h is epic and transports propositions
onto the target domain, verifying the evaluator's quantifier identity at
every successor. This uses fullness and is not asserted for arbitrary
Henkin submodels.

Necessarily atomic {h}, by contrast, requires UNIQUE such factorizations.
Explicit finite categories show both separations: one has a necessarily
atomic proposition but no CE; another has CE but no necessarily atomic
proposition. A third has both while BF_t fails. In the second example CE
also fails at a successor, so bare C+CE does not imply box CE or box BR.

As a short corollary, a full one-object action model has CE exactly when
its monoid is a group. If epic h belongs to every principal left ideal,
write h=u h² and cancel to get u h=1; cancellation gives h u=1. Every monoid
element then has a left inverse and hence is a unit. The converse is
immediate. These finite and infinite semantic results are in world §23.

Finally, proposition quantification and ALL-type quantification must remain
distinct over bare C. The same persistent-atom/local-Barcan theorem applies
with LB_sigma for a specified argument type. In a full category, epic h
transports every relational type onto its target domain, but its individual
transport can fail to be onto. A terminal two-world chain whose individual
domain grows from one to two witnesses that separation: it has a complete
evaluator for every relational quantifier, but none commuting with every
individual quantifier. Over T the all-type extension is automatic.

## 22. Ordinary truth preservation suffices existentially

The evaluator formulation of T admits a simpler presentation. Define WCE(E)
by necessary bivalence of every E(p), and the CURRENT biconditionals

    E(not p) <-> not E(p);
    E(forall p Fp) <-> forall p E(Fp).

Over C, existence of WCE and existence of CE are equivalent; WCE-density,
or separation of propositions by WCEs, is therefore equivalent to T. This
does not identify a weak evaluator with a complete one. From WCE one builds
the associated atom w=forall p(Ep->p), proves persistence and LB_t(w), and
replaces E by the canonical CE E_w. The positive and negative recognition
sets agree at the current world. No Functionality is assumed in this step.

The negative law itself upgrades to identity because both sides are
bivalent. The quantified right side need not be bivalent, so the quantifier
law need not upgrade for the original E. World-representation §27 gives an
explicit finite-category WCE whose quantifier-preservation identity fails.
It also checks that endpoint preservation follows from the stated laws.

In the full action hierarchies, the same analysis has a useful exact local
calibration at evaluation object A:

    ND_t       iff every outgoing arrow from A is split monic;
    BF_t       iff every outgoing arrow from A is epic;
    T          iff every outgoing arrow from A is invertible;
    box ND_t   iff every outgoing arrow from A is invertible.

The proposition transport along g is inverse image under k |-> k g.
Its injectivity requires that this composition map cover id_A, precisely
a left inverse for g. Its surjectivity is precisely right cancellation of
g. Necessity of ND applies the split-monic condition to g's left inverse
at its target and makes g invertible. Conversely, if all root arrows are
invertible, every reachable arrow u is invertible since u=(ug)g^-1.
Full atomicity then supplies T. These are full-model characterizations,
not equivalences claimed for arbitrary Henkin structures; see world §28.

Even NECESSARY existence of CE does not replace density. The category
generated by a proper retract 0 --g--> C --k--> 0, with kg=id_0 but
gk≠id_C, has a zero object 0. At every object its unique arrow to 0 is epic
and uniquely factors through every outgoing arrow, giving CE and a
necessarily atomic proposition. At root 0 all outgoing arrows split monic,
so ND holds at every type, while g is not epic and BF_t fails. Its full
hierarchy therefore has ND_all, boxed CE and boxed Atomicity_all but not T.
This isolates density even after strengthening the surrounding assumptions.

## 23. Choice as extension of maps, with one canonical inclusion per type

Let CABool_int be the category of admitted NONTRIVIAL complete atomic Boolean
algebras on rigid represented fields, with complete admitted homomorphisms.
Allowing such fields, rather than whole type domains alone, is essential.
Atomic duality identifies its arrows with maps between its atom fields in
the reverse direction. This yields the exact hierarchy:

    T: all its objects are projective;
    T + IC_all: the proposition algebra B_t is injective;
    T + boxed Functional Choice: all its objects are injective.

The first assertion uses splitting of a surjective complete homomorphism:
its dual injection has a left inverse, obtained from the unique inverse on
the image and one default atom elsewhere. The second says that lifting a
map from the world field through a surjection is exactly world-indexed
choice. The third permits arbitrary represented index fields. In contrast,
with finite Boolean maps and arbitrary Boolean input algebras, injectivity
of complete atomic targets is exactly BPI_int. Algebraic-core §§34 and 37
give the graphs, typed relative powersets and both implications.

The retraction definitions can also be made canonical. For each output
type sigma let P_sigma^+ be its nonempty rigid properties and put

    M_sigma={(X,x): X in P_sigma^+ and Xx};
    j_sigma:P_int(P_sigma^+) -> P_int(M_sigma),
    j_sigma(B)(X,x) iff B(X).

This is the inverse-image embedding of the membership projection. A
complete retraction is exactly a choice function on all nonempty rigid
sigma-properties. A finite Boolean retraction is exactly an ultrafilter
choice on those properties. Consequently the all-type canonical family
of inclusions suffices for boxed FC and UFC respectively; no quantification
over arbitrary subalgebras is needed. The inclusion is pure and canonical,
while a retraction need not be. See algebraic-core §38.

There is also a meaningful intermediate continuity level. Retractions
preserving every internally well-ordered indexed meet give choice on any
output field admitting a well-ordered separating family of rigid predicates.
Their row ultrafilter decides each separating coordinate; meet preservation
makes the common agreement cell large, and separation makes it a singleton.
In particular this covers represented real numbers, via their natural-number
coordinates. The ordered-individual model satisfies these retractions and
still fails individual Choice. The separating-family condition alone does
not imply well-orderability; with these retractions it does. See mixing §26.

## 24. Simplicity of an axiom does not select a pure witness

Under T, every admitted permutation of the world atoms extends uniquely
to the logical type hierarchy, fixing individuals and acting by conjugacy
on higher types. Admitted individual permutations can be included too,
using graphs for maps into e. Pure terms are invariant under these logical
automorphisms, with the usual qualification that the actual world moves
when the world permutation moves it.

Thus there is no pure selected witness for EU_e: each value of a pure R:et
is fixed by all world permutations and hence is bivalent, so R has only one
profile. Nor, with at least two worlds, can a pure term select a complete
evaluator: its associated atom would be fixed by every atom transposition.
These statements concern parameter-free terms in the original signature;
they do not refute the corresponding existential axioms.

More generally a pure finite-arity individual relation depends only on the
tuple's equality pattern. Its coefficients are closed pure propositions;
the normal form need not decide those coefficients uniformly across models.
This excludes pure strict ordering and pure universal choice of individuals
when there are at least two individuals. Algebraic-core §§35–38 give the
precise automorphism constructions and normal form.

## 25. The companion Strong Possibility construction: audit scope

Two separate audit files address the parent research construction, without
editing its report. `parent-profile-atomicity-audit.md` supplies finite typed
truth-table elimination for a pure one-individual-variable formula on an
n-element Fregean domain. Uniform permutation symmetry and discharge produce
a C-theorem, so theoremhood-restricted necessitation is legitimate. The
result is an identity for the relevant finite-profile atom, including at
points where that atom is currently false but possible.

`parent-profile-root-closure-audit.md` checks the root extension/profile
product: profiles retain denotations, application is componentwise, and
lambda abstraction keeps the bound variable symbolic until component
evaluation. Target quantifiers use full component domains. This closes the
specific closure and atomicity obligations, conditional on the component
models and source completeness theorem already cited by the parent report.
It establishes no signature expansion and does not alter the reference
theory for H or Logical Equivalence. The explicit root Functionality failure
uses different profile components with the same actual extension.

## 26. The finer Boolean Prime Ideal factorization

The decomposition in §16 can be sharpened to

    BPI_int <-> FineUF + ACfin_all.

Here ACfin_all chooses from internally finite nonempty fibers; the fineness
principle is unchanged. To prove the nontrivial direction, take a rigid
serial relation R and a fine ultrafilter V on the finite subfields of the
represented pair field R itself. For a finite F⊆R, each covered row
{y:(x,y)∈F} is finite and nonempty. ACfin chooses c(F,x) in that row,
uniformly in the covered pairs (F,x). For each fixed x, one R-witness
shows that its coverage event is V-large; no uniform preliminary witnesses
are needed. Pushing V through c(-,x) yields an ultrafilter on each R_x,
uniformly. Thus UFC follows, and §16 gives BPI_int. Conversely UFC chooses
from finite fibers because every ultrafilter on a finite field is principal.

FineUF is itself equivalent to an indexed binary Rado selection principle.
The premise supplies a table g(F,i)∈{0,1} for i∈F and finite F⊆I; the
conclusion supplies h:I→{0,1} such that each finite restriction h|F agrees
with g(F',-) for some finite F'⊇F. Fineness takes the unique large value
at each coordinate. Conversely, tag requirement labels i together with
Boolean-event labels P and let g read P at the finite set of requirement
labels present. Finite agreement enforces the ultrafilter laws and every
fine cone. The local table is supplied data; omitting that premise changes
the principle. Algebraic-core §§40–41 give both full constructions.

The factors are strictly independent. FineUF without ACfin uses the explicit
pair-flip model. ACfin without FineUF follows from the literature-dependent
UFC-without-BPI model transfer of §16. The classical Rado-plus-finite-choice
factorization is also explicitly recalled in Howard–Tachtsis, Theorem 10,
proof (1); this internal derivation is not a historical novelty claim.

## 27. Uniform evaluations separate world choice from interworld choice

Over T let UCE_t assert a SINGLE admitted S:t→tt choosing a complete
evaluator S(p) recognizing every nonzero p. Then

    UCE_t <-> the world-atom field is internally well-orderable.

S chooses the generating atom below each nonzero p. Every admitted atom
subfield is the atom set of its join, so this is choice on all nonempty
world subfields. Conversely the least atom below p supplies S. This is
stronger than Ret_t, which gives separate choices for each partition, and
has a different direction of indexing from IC, which chooses objects in
families indexed by worlds.

The distinctions have direct countermodels. Unordered worlds with finite
supports give T+IC_all+Ret_t but not UCE_t. Fixed worlds N and independently
flippable individual pairs give T+UCE_t+Ret_t but fail IC_e. Thus uniform
complete evaluation and interworld Choice are independent over T.

Uniform complete evaluators on B_(sigma t) mean well-orderability of the
atom field Worlds×D_sigma. Their all-type schema is exactly boxed FC. At t,
UCE_t also equals a uniform operator choosing complete retractions for
all complete subalgebras; it suffices to choose them uniformly for the
four-element subalgebras {0,p,not p,1}. This quantifier order is stronger
than bare Ret_t. Algebraic-core §42 proves each formulation.

Two bridges are useful for the individual-profile question. EU_e+UCE_t
already gives individual-output Choice without IC: the least world for
each profile well-orders the profile field and hence the individual field.
Separately, EU_e+IC_e+FINITE Boolean Ret_t gives individual-output UFC.
An IC selector chooses one member of each nonempty world-profile; the
profile partition retraction supplies a uniform ultrafilter on each world
fiber, and pushing it through that selector gives an ultrafilter on the
corresponding individual field. Countable or well-ordered meet preservation
transfers too. A well-ordered separating family on E then makes these
ultrafilters principal. See mixing §28. None settles EU_e+IC_e alone.

## 28. Finite evaluation is strictly weaker, even with relational Choice

Let FBE(E) require bivalence and preservation of negation and binary meet.
Let FBED say every nonzero proposition is recognized by some FBE. Over C,

    T -> FBED -> ND_t;
    ND_t + Atomicity_t -> FBED.

All implications and both strict separations are verified. The canonical
evaluator of a persistent atom preserves finite operations without a Barcan
premise. Thus the finite full retract model of §22 has FBED but not T.
To separate ND_t from FBED, use the finite-coordinate supported hierarchy
over W=G=2^N, with translations and support subgroups fixing finitely many
coordinates. Its proposition algebra consists of clopen cylinders and is
atomless. A fresh coordinate flip fixes any proposed supported E but
interchanges p_n and not p_n, making bivalent negation preservation
impossible. Compactness of W makes every supported serial cover admit a
finite witness subcover, and finite priority pasting gives all IC. Thus
even C5+IC_all+quantified Infinity need not supply a single such evaluator.

The final audit strengthens this to boxed RC and boxed modalized RC.
For a relation supported by G_S, the G_S-action on pairs (world,input) is
free because translation on worlds is free. Choose an eligible output on
each orbit and transport it equivariantly; on an ineligible orbit choose
any default. Each fixed-input/output section is invariant under the open
subgroup fixing S and those arguments, hence is a clopen admitted truth set.
The whole selector graph is supported by S. This supplies graph choice,
including local RC, without a supported operation encoding a world's truth.
World §30 contains the independently audited full argument.

A simple atomless FBED model takes G=Aut(Q,<), supports objects by finitely
many rationals, and uses the nonprincipal Dedekind cuts of Q as worlds.
Supported propositions are finite unions of intervals with rational
boundaries. Right-germ evaluation at a rational q is supported, bivalent
and Boolean; these germs recognize every nonempty interval. No atom exists.
The model has C5 but fails IC_t. A supported selector of a proposition
positive at q's right germ yet false at each world cannot handle a cut
immediately right of q before its next support point. World §§30 and 32
give the full closure and nonselection proofs.

A stronger construction closes the remaining Choice loophole. Start with
an atomless complete Boolean algebra B and its full finite type hierarchy.
Take a countable M elementary in a sufficiently large H_theta, containing
all hierarchy domains and operations. The admitted objects are their
M-traces; worlds are M-generic ultrafilters on B∩M. Genericity makes each
M-coded join/meet agree with actual quantification over the admitted domain.
Elementarity both closes lambda abstraction and separates distinct admitted
functions. This is an ordinary-ZFC construction, not an assumption of a
transitive set model of ZFC.

Rowwise maximal antichains supply necessarily functional SUBRELATIONS, so
boxed Relational Choice, modalized Relational Choice and all IC hold.
Ordinary ultrafilters in M supply one admitted uniform family of finite
evaluators recognizing every nonzero proposition. Choice and BPI for rigid
typed codes also hold. Nevertheless every relational Boolean algebra is
atomless, and Plenitude and Functional Choice fail at (t,t) at every world.
The explicit relation is

    U(p,q) := (p and q=top) or (not p and q=bottom).

A representing operation X would code the generic world's truth ultrafilter
as an element V of M. But B^+ minus V is dense in an atomless B and belongs
M, contradicting that world's genericity. The graph U itself is already
necessarily functional. Relational graph selection and representation by
operations therefore remain distinct despite the displayed Choice package.

This exact truth-choice relation and its Boolean calculation already occur
in the bundle's `full-boolean-valued-atom-and-atomless` write-up, §6. That
record attributes the underlying full Boolean-valued construction to Bacon,
*Could the truths of mathematics have been different?*, online Appendix B.2,
pp.7–9 (PDF pp.41–43). The generic-world externalization and evaluator claims
are the additional arguments here; no novelty is asserted for the relation
or Boolean-valued method. Mixing §31 supplies the referee-detail construction,
independently audited by both other lanes. World §33 records the audit.

There is a simpler alternative if fully atomless ordinary Kripke worlds
are not required. The EXISTING full Boolean model B=2×A, evaluated at its
designated atom, already has C5, local Functional Choice and failure of
Atomicity. Full domains admit the same ultrafilter family and antichain
constructions, adding uniform FBED and boxed RC/IC. Completeness of B and
full lambda domains also allow arbitrary set-sized conjunction/disjunction
with common finite free variables; the designated atomic truth projection
preserves these meets and joins. Thus the general FBED/Choice versus T
separation survives the extension with the specified local introduction and
elimination rules. This does not add unrestricted infinitary distributivity
or all semantic infinitary validities as H-theorems: complete atomless
Boolean algebras need not be completely distributive. Logical Equivalence
retains the declared extended-H theoremhood condition. These additional
verdicts are proved in the notes; the existing record is not edited.

The fixed-universe generic construction initially handles finitary C and
M-coded infinitary families. A separate relative forcing-extension version
retains its fully atomless ordinary-world result for C_omega. Use the
complete Boolean algebra of countable partial functions omega_1→2 and a
countably closed full-support product supplying a generic world below every
nonzero Boolean value. No countable sequence of ground objects is added,
so countable formula/parameter codes and their denotations remain in the
ground full hierarchy. The truth lemma, antichain choices and finite
evaluators still apply. This relative variant makes no arbitrary set-sized
conjunction claim. World §34 distinguishes the two infinitary arguments.
