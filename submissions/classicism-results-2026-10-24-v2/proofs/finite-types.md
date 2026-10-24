# Actual finiteness throughout the type hierarchy

Original mathematical argument, direct source misc; unpaginated.

## 1. Exact statement

Work in the fixed finitary system C, with types e and t and arrows σ→τ only
when τ is relational. Write Fσ for the actual internal Frege finiteness of the
whole σ-domain:

    Fσ := Finite(λx^σ. ⊤).

Let F_all be the schema containing Fσ at each closed admitted type, and F_rel
its restriction to relational types. These are metalinguistic families of
sentences, not quantifiers over types inside C. Functionality is the full
schema asserting that two admitted operations with equal values at every input
are identical, for every allowed input/output pair.

Then:

1. C + Functionality + Fe + Ft proves every instance of F_all.
2. C + F_rel proves every instance of F_all; the converse is immediate.
3. Consequently, over C + Functionality, the two premises Fe and Ft are
   equivalent in strength to F_all, and also to F_rel.

Full Barcan is another sufficient background for item 1, because its instance
at an input type implies Functionality for every relational output type.
The single C5 premise K := □∀p q (p≠q→□(p≠q)) is sufficient as well: the
existing C theorem `bf_of_box_nd_t` supplies every required Barcan instance
from K. Thus C + K + Fe + Ft proves F_all and, in fact, □Fσ at every closed
type σ. This corollary uses internal
Frege finiteness directly, without first fixing any external finite cardinal.
Functionality or Barcan remains an explicit optional schema. No claim is made
that those schemas follow from Fe and Ft, or that they are necessary for a
particular finite model.

## 2. The finite-operation step

Suppose Fσ and Fτ, where τ is relational, and assume Functionality(σ,τ).
The internal finite-set calculus makes the field of whole-pair haecceities

    c_(x,y) := λu^σ v^τ. (u=x ∧ v=y)

finite when x and y range over the two whole domains. Distinct pairs have
distinct codes: equality of their predicates, applied to the first pair,
gives equality of both coordinates. This uses a relational code, not a new
tuple type or an e-valued operation.

Use the finite coordinate field of pair codes to distinguish operations f by
the current truth values of `f(x)=y`. If f and g have the same values of every
such test, fix any x and use y=f(x). The test holds of f, so g(x)=f(x).
Functionality now yields f=g. Thus this finite coordinate field separates the
whole admitted operation family. The internal finite-separating-family theorem
gives F(σ→τ).

Every predicate and code used here is a formula of the original language. The
proof counts the admitted operations and does not replace their domain by an
external full function set. It requires no choice, no C5, and no assumption that
partial applications of rigid relations are rigid.

## 3. Induction on the admitted type code

Simultaneously prove Fσ for closed type codes σ and Fρ for closed relational
type codes ρ. At e use Fe. At t use Ft. At an arrow σ→ρ, the two proper subtypes
are closed, so the induction hypotheses give their finiteness. The appropriate
Functionality instance and section 2 give finiteness of the arrow type.
Type-variable codes are excluded by the closedness condition.

This is a finite structural induction for each requested type. Its proof builds
an actual C derivation from the indicated schema instances. It does not require
an infinite conjunction, a simultaneous object-language type quantifier, or a
completed semantic hierarchy. The Barcan version uses its input-type instance
at each arrow step and the same induction.

Conversely, F_all includes its e and t instances. To recover F_all from F_rel
in bare C, it only remains to recover Fe. The relational schema includes
F(e→t). Associate each individual a with its admitted singleton predicate
`λx. x=a`. If the singleton predicates of a and b are identical, application at
a gives a=b. The finite-injection-domain theorem therefore gives Fe from
F(e→t), without choosing any inverse operation. Every other closed type is
already relational, proving item 2.

Under C5 each actual finiteness conclusion is necessary. If n is a Frege number
counting the universal σ-property, numberhood of n is necessary by the existing
Frege-number persistence theorem. The universal property is persistent, and the
C5 finite-count stability induction (`persistent_count_settled`) therefore
gives □(n(λx.⊤)). Necessitate only the closed logical implication from these
two facts to Fσ and apply K twice. This yields □Fσ without necessitating the
optional premise Fσ. Combining this argument with the type induction gives the
claimed necessary-finiteness schema.

## 4. Scope and remaining boundary

The conclusion is actual quantified Frege finiteness, not the external absence
of arbitrarily long lists of distinct objects. It is a uniform derivation
construction over the existing finite type grammar. It does not supply a
recursive Actuality or Gallin interpretation, a classification of finite
intensional models, or an effective arithmetic/model coding theorem. Those
claims require their additional constructions and remain separate.

The source wrappers are in `FiniteTypePropagation.lean`; their translations and
the structural assembly are in the companion Certificates and Schemas modules.
The propagation, necessary-finiteness and schema-comparison conclusions have
passing C certificates. The structural check is recorded in
`lean-formalization/checks/20261023T201558902470Z-f921a568.json`; the printed
principal proofs use only `propext` and `Quot.sound` in Lean's metatheory.

## 5. Finite premise support for an individual target

The full Functionality schema is convenient for stating the hierarchy theorem,
but each particular derivation uses a finite part of it. For a closed target
type, traverse its finite type tree. Include Fe for each e leaf, Ft for each t
leaf, and Functionality(σ,ρ) for each arrow node σ→ρ. Duplicates may be removed.
The induction in section 3 derives the target's finiteness from precisely these
premises. Thus the number of Functionality instances needed is at most the
number of arrow occurrences in the target. For the Barcan version, use BFσ at
each arrow node instead.

In particular, a type built entirely from t requires only Ft and the indicated
Functionality instances; Fe is unnecessary. This is a refinement of the
sufficient assumptions, not a claim that the listed assumptions are minimal.
No necessitation of an optional premise occurs. Taking the classical
contrapositive, under those same Functionality instances, an actually infinite
target type forces actual infinity at at least one base type appearing in its
tree. The claim concerns each finite type separately, not an object-language
infinite disjunction over types.

## 6. Exact finiteness criterion at each closed type

The converse arrow step needs no Functionality assumption. In C, for every
closed input type σ and closed relational output type ρ,

    F(σ→ρ) → Fσ ∧ Fρ.

Here are the required injections, expressed as relations so that none demands
an operation with output e. All closed types are inhabited in H. Fix an input
a:σ for the output injection: b:ρ is related to its constant operation
`λx^σ.b`. Two values related to the same operation are equal by applying that
identity at a. The finite-injection-domain theorem gives Fρ from F(σ→ρ).

For the input injection, flatten ρ as τ₁→…→τ_k→t, including k=0. Define
closed pure terms

    cρ(p) := λy₁…y_k.p,
    rρ(Y) := ∀y₁…y_k.Y[y₁…y_k].

H's vacuous-quantifier laws and nonemptiness give a theorem
`rρ(cρ(p)) ↔ p`. Logical Equivalence, with its original theoremhood side
condition, therefore gives the literal retraction identity `rρ(cρ(p))=p`
in C. In the nullary case both maps are the identity.

Relate x:σ to the admitted operation

    j_x := λz^σ.cρ(z=x).

If j_x=j_y, application at x and then application of rρ, followed by the two
retraction equations, give `(x=x)=(x=y)`. Identity substitution and reflexivity
give x=y. Thus the relation has nonempty disjoint fibres over every x; the
finite-injection-domain theorem gives Fσ from F(σ→ρ). Neither injection
requires Choice, extensionality, BF, C5, or a simultaneous choice of witnesses
throughout the hierarchy.

Together with section 2 this proves the exact local criterion

    Functionality(σ,ρ) → [F(σ→ρ) ↔ (Fσ ∧ Fρ)].

Induction on the finite type tree now yields a precise classification under
the Functionality instances at its arrow nodes:

- For e, finiteness is Fe.
- For a relational type containing no occurrence of e, finiteness is equivalent
  to Ft.
- For a relational type containing e, finiteness is equivalent to Fe ∧ Ft.

Every relational type has a t leaf, so these cases exhaust the closed grammar.
Classical negation gives the corresponding quantified Infinity criteria: the
e-free relational types are infinite exactly when t is infinite; the relational
types containing e are infinite exactly when e or t is infinite. Full BF or the
single C5 premise supplies all the needed Functionality instances. These are
criteria for internal Frege finiteness/Infinity; they do not assert an externally
finite domain or a full-function interpretation.

There is also a useful argument-deletion proof of the input implication. For
an inhabited type τ with witness a, send an operation f:σ→ρ to
`L(f):=λx^σ y^τ.f(x)`. Define `R(h):=λx^σ.h(x,a)`. Beta and eta give
`R(L(f))=f` literally, so L is injective without Functionality. The finite
relational-injection theorem therefore gives

    F(σ→τ→ρ) → F(σ→ρ).

Delete the finitely many arguments of the output type in this way. At each
step its closedness supplies the one required inhabitant. This gives
F(σ→t), and the singleton injection gives Fσ. No family of chosen inhabitants
or operation with output e is introduced.

There is a separate uniform Infinity consequence already over bare C. Since
every closed relational type ρ has a t leaf, downward finiteness gives
`Fρ → Ft`; classical contraposition gives `Infinity_t → Infinity_ρ`.
Consequently, as schemata over closed types,

    Infinity_t ↔ Infinity at every relational type,
    (Infinity_e ∧ Infinity_t) ↔ Infinity at every admitted type.

The reverse directions merely take the t and e instances. These uniform
statements need neither Functionality nor C5. “Infinity” here is the quantified
Frege axiom, the negation of actual internal finiteness. These are immediate
ordinary consequences of the certified downward theorem; no separate Lean
wrapper or new record is asserted for these formulations.

The `FiniteTypePropagation` Lean files address sections 1–4's upward propagation,
necessary-finiteness corollary, and all-type/relational-schema comparison.
The separate `FiniteTypeDescent` files implement the argument-deletion proof
and compute each type's exact finite-base requirements recursively, with
Functionality only in the sufficient direction. Both downward implications,
the exact recursive criterion and the explicit e-occurrence cases now have
passing C certificates: the schema check is recorded in the same
`20261023T201558902470Z-f921a568` manifest. All printed principal proofs use
only `propext` and `Quot.sound` in the metatheory. The finite-premise bound in
section 5 and the subsequent arithmetic/model corollaries remain ordinary
mathematical arguments, without separate Lean certificates.

## 7. Consequence for the numerical fields under C5

The already certified `C5Frege.infinity_iff_arithmeticI` identifies actual
quantified Infinity at each counting type σ with the existing ArithmeticIσ
condition. Therefore section 6 gives, under C5, for each closed relational ρ,

    ArithmeticIρ ↔ ArithmeticIt                    if ρ contains no e,
    ArithmeticIρ ↔ (ArithmeticIe ∨ ArithmeticIt)   if ρ contains e.

The same proof, using `C5Frege.finite_base_iff_numbers`, determines internal
finiteness of each type's numerical field from the corresponding base-type
criterion. This is a statement about noncollapse and finiteness of the
impredicatively defined internal number fields. It does not assert that their
members are externally standard, supply a selecting arithmetic operation, or
identify their full first-order consequence theory. This composite arithmetic corollary remains an ordinary mathematical proof
rather than a separate all-type Lean certificate; section 6's finiteness
classification itself is now certified as recorded above.

## 8. Sharpness: full constant-domain Boolean-valued models

All four combinations of base-type finiteness occur even under C5. The following
explicit model construction witnesses this; it is ordinary mathematics in the
usual classical set-theoretic metatheory, not a Lean model certificate.

Choose nonempty sets I and W and an evaluation world w₀∈W. Define

    D_e = I,       D_t = P(W),
    D_(σ→ρ) = all set-functions D_σ → D_ρ.

The last clause applies only to the admitted arrows with relational output.
Truth at w is membership of w in a proposition. Boolean operations on
propositions are the set operations. Universal quantification at σ is
intersection over D_σ, and existential quantification is union. Typed identity
has value W for literally equal entities and ∅ otherwise. Application is
ordinary function application; lambda abstraction denotes the function given
by its body. All domains are the same at every world.

The ordinary H clauses hold: each world has classical truth, the quantifiers
range over nonempty domains, identity is substitutive, and beta and eta hold
for functions. An H-theorem of equivalence is true at every world under every
assignment. Its two sides therefore denote the same subset of W, so their
lambda abstractions denote literally equal functions. This verifies C's
Logical Equivalence with its theoremhood restriction. Literal equality is
world-invariant, so boxed ND, and hence C5, holds. Functionality holds directly
for the full function domains. No arrow with output e is introduced.

At any type σ, the internal Frege numbers are exactly the orbit of zero under
standard finite iteration of successor. One inclusion is ordinary induction.
For the other, the full property domain on cardinalities contains the predicate
whose current extension is exactly that orbit (take values W and ∅). This
predicate is inductive and excludes every entity outside the orbit, so the
impredicative numberhood definition includes no additional entity. A standard
induction on the numeral shows that it counts exactly the properties whose
extension at the evaluation world has that many members. Therefore Fσ holds
exactly when the set D_σ is externally finite in this particular full model.
This argument is confined to this construction; it is not imposed on arbitrary
Henkin models.

Consequently Fe holds iff I is finite, and Ft holds iff P(W), equivalently W,
is finite. Taking I and W independently to be a singleton or the ordinary
natural numbers realizes respectively the four pairs

    (Fe,Ft), (Fe,¬Ft), (¬Fe,Ft), (¬Fe,¬Ft).

Their hierarchy-wide patterns are:

| I | W | e | e-free relational types | e-containing relational types |
| --- | --- | --- | --- | --- |
| Singleton | Singleton | Finite | Finite | Finite |
| Singleton | Natural numbers | Finite | Infinite | Infinite |
| Natural numbers | Singleton | Infinite | Finite | Infinite |
| Natural numbers | Natural numbers | Infinite | Infinite | Infinite |

Here “finite” and “infinite” in the last three columns mean the internal Frege
conditions. The domain-size argument above establishes these verdicts in the
specified full models. Section 7 determines the ArithmeticI verdicts from the
same table because every model satisfies C5.

These model witnesses show that the two base conditions in the e-containing
case cannot be dropped, even over C5. Together with sections 6–7, they realize
each resulting finiteness and arithmetic-noncollapse pattern throughout the
admitted hierarchy. They do not assert that every C5 model has full function
domains or standard internal numbers.

## 9. Two-stage diagram model with expanding individuals

The Functionality premise in the upward theorem cannot simply be deleted.
Here is a direct two-stage model of C with Fe and Ft true but F(e→t) false.
This is an ordinary model argument in classical set theory, not a Lean model
certificate or a claim about the literature. It adds a separate sharpness
result to the four C5 models above.

Use stages r≤s. At every type σ give sets Dσ(r), Dσ(s) and a restriction map
Rσ:Dσ(r)→Dσ(s). These maps are metatheoretic data. At the two base types put

    De(r)={a},       De(s)=ℕ,       Re(a)=0,
    Dt(r)={0,1}²,    Dt(s)={0,1},   Rt(b,c)=c.

Truth at r is the first coordinate; truth at s is the Boolean value. For an
admitted arrow σ→ρ, define D(σ→ρ)(s) to be the full function set from Dσ(s)
to Dρ(s). Define D(σ→ρ)(r) to consist of pairs (fr,fs) such that

    fr:Dσ(r)→Dρ(r),   fs:Dσ(s)→Dρ(s),
    Rρ(fr(x)) = fs(Rσ(x))  for every x∈Dσ(r).

Its restriction sends (fr,fs) to fs. Application evaluates the corresponding
component. Lambda abstraction supplies the two component functions denoted by
its body. Arrows with output e are not formed. All domains are nonempty:
the base domains are nonempty, and each relational output has a compatible
bottom element, which supplies a constant bottom operation at every arrow.

Boolean operations at r act on both coordinates, and at s act on its one
Boolean value. Identity at σ has denotation

    eqσ,r(x,y) = (1[x=y], 1[Rσ(x)=Rσ(y)]),
    eqσ,s(u,v) = 1[u=v].

For P=(Pr,Ps) of type σ→t at r, universal quantification has value

    (1[for every x∈Dσ(r), first(Pr(x))=1],
     1[for every y∈Dσ(s), Ps(y)=1]).

At s it has the ordinary universal truth value over Dσ(s). Existential
quantification is defined dually. These operations commute with restriction:
for quantification, its second coordinate is exactly the quantifier at s
applied to Ps; for identity and the Boolean operations this follows directly
from the displayed definitions. Structural induction therefore gives natural
term evaluation, so lambda abstraction is admitted. Beta and eta hold
componentwise. Each stage validates classical logic, the actual-domain
quantifier laws, substitutive identity and nonemptiness. The modality defined
by identity with top has its usual meaning over the remaining stages: at r,
box(b,c)=(b∧c,c), and at s it is the identity. Thus necessitation preserves
global validity as well.

An H-theorem of equivalence is true at both stages under every assignment.
Its two sides therefore have identical truth coordinates. Their lambda
abstractions agree on every argument at both components, hence are literally
equal as pairs. This verifies C's Logical Equivalence rule with its original
H-theoremhood restriction. It does not apply that rule to equivalence merely
under the assumptions Fe and Ft. The same argument verifies the repository's
`Subst` presentation of C directly: by induction on derivations, the two
logical-premise derivations give equivalence at both stages under every
assignment, hence equality of proposition denotations. Plugging equal
denotations into a typed term context preserves equality, including under
lambda binders. The side hypotheses of the third premise play no role in
this equality argument. Together these clauses verify a model of C.

It remains to verify that the displayed cardinalities give the *internal*
Frege verdicts. Every subset A⊆Dσ(r) is an actual extension of an admitted
property: take its s-component constantly false and its r-component

    x ↦ (1[x∈A],0).

The naturality equation is then automatic. At s all unary properties are
available outright. At either stage, apply this observation at the cardinality
type to the standard finite-successor orbit of zero. Its characteristic
extension is inductive at that stage and excludes every entity outside the
orbit. Conversely ordinary finite iteration belongs to every internally
inductive property. Hence internal numberhood at each stage is exactly the
standard successor orbit there. Induction on a standard numeral shows that
its actual counts are the usual finite extension sizes. It follows that Fσ
at either stage holds exactly when that stage's set Dσ is externally finite.
No such identification is asserted for arbitrary C models.

Consequently Fe and Ft hold at r, since De(r) has one member and Dt(r) has
four. But D(e→t)(r) is infinite. For each n≥1 choose the terminal predicate
fs to be the characteristic function of {n}, and set fr(a)=(0,0). Since
fs(0)=0, these are admitted pairs. Different n give distinct predicate
objects. Thus F(e→t) is false at r, while the source and output domains are
both internally finite.

In fact every e-containing relational type is infinite at r in this model,
while every e-free relational type is finite. For the latter claim, both stages'
t-only domains stay finite by the recursive construction. For the former,
each occurrence of e has an immediate parent arrow e→ρ. For each n≥1 its
terminal operation can take top at n and bottom elsewhere, with the current
value at a set to bottom. These are infinitely many compatible operations,
since bottom and top at every relational terminal type are distinct and
restriction preserves them. Infinity then propagates from that arrow to its
ancestors by contraposition of the bare-C descent theorem. Thus Fe and Ft alone
do not determine finiteness elsewhere in the hierarchy.

Functionality also fails directly. Take the everywhere-false terminal
predicate and the terminal characteristic function of {1}, with fr(a)=(0,0)
in both pairs. The two operation objects have literally identical values on
every actual r-stage individual, yet are distinct because their terminal
components differ. This supplies the required countermodel to upward
finiteness without Functionality. It does not claim that Functionality is
necessary in every individual finite model. The model is not C5: the distinct
root propositions (0,1) and (1,1) become equal at s, so ND already fails at r.

The same model separates finite bases from finite numerical fields without C5.
Over e, the standard numeral objects at r remain pairwise distinct: restriction
to s sends each to its usual numeral over ℕ, where every finite size is realized.
The root's internal numbers are exactly this orbit, as proved above, and
successor is injective on it. Thus IStar_e and ArithmeticI_e hold at r, although
Fe holds and actual quantified Infinity_e is false. In particular the internal
number field over e is infinite while the actual individual domain is a
singleton. This supplies a direct C countermodel to dropping C5 from the
Infinity–ArithmeticI equivalence and from finite-base preservation for number
fields. These are ordinary consequences of this model construction, without
separate Lean certificates.

A finite variant clarifies the other direction. Replace De(s)=ℕ by {0,1},
keeping De(r)={a} and Re(a)=0. Both base domains are now finite at both stages.
Recursively, each function domain is a full finite function set or a subset of
a product of two such finite sets, so every admitted type is externally finite
at both stages. The actual-extension argument above then proves internal
finiteness at every type. Nevertheless Functionality still fails: the
haecceity of a and the constant-true predicate have identical current values
at a, but their terminal components differ at1. Concretely D(e→t)(r) has
eight members: choose any of four terminal predicates and either first truth
coordinate for the value at a; the second coordinate is forced by its value
at0. Thus even the all-type internal-finiteness schema does not imply
Functionality over C. The infinite variant refutes propagation without extra
regularity; the finite variant refutes the converse inference from finiteness
to Functionality.

## 10. Formalization routes and their exact scope

The resumed formalization uses the repository's full intensional action-model
construction for the two-stage category. Its individual action is the displayed
singleton-to-terminal inclusion. The existing semantic numeral theorems already
connect external finite domains to failure of actual quantified Infinity, and
extensionally full infinite domains to its truth. Consequently the countermodel
verdicts do not depend on completing a separate standardness theorem first.
The arithmetic verdict has an equally short route: terminal quantified Infinity
implies the Peano condition by a certified C rule; the entrance arrow therefore
witnesses ArithmeticI at the root. A second certified C rule yields an internally
infinite number field there.

An alternate family realizes the four C5 base patterns in section 8. For any
nonempty set I and group G, take the one-object category with arrows G and the
constant individual action I, then form the full intensional model. Every arrow
is invertible, so necessary distinctness holds at every type. The individual
domain is I and the propositional domain is the power set of the arrows, up to
the harmless singleton tuple coordinates. Taking I to be a singleton or the
natural numbers, and G to be trivial or the permutation group of the natural
numbers, independently realizes the four internal Infinity verdicts. This is
an alternative construction, not an unproved identification with the literal
Boolean-valued presentation of section 8.

The separate standard-orbit argument is stronger than the Infinity bridge:
in an extensionally full model, every subset of the cardinality domain is the
actual extension of an admitted test. In particular the orbit of zero under
successor is such an extension; it is inductive, and ordinary finite iteration
lies in every inductive extension. Thus the quoted internal number predicate
denotes exactly that orbit. Distinct numerals may still collapse. This argument
does not justify standardness in arbitrary Henkin models.

The arbitrary-model reflection draft instead inducts over the existing ATerm
and AForm grammar, with quantifiers over admitted inner cardinality objects and
the actual quoted arithmetic operations. It uses neither fullness nor external
standardness. Reflection of this evaluator is separate from instantiating
cross-base Synch transfer, and from constructing object-C derivations uniformly
from formula codes. The current verification ledger records the compiler status
of these formalizations; prose arguments and draft source alone are not Lean
certificates.

### 10.1. The remaining cross-base bridge, stated at the inner domains

Fix a C-model A, an evaluation arrow h into a stage W, and counting types σ
and τ. Suppose the actual quoted noncollapse conditions hold at W for both
bases. Interpret Synch at W by the quoted impredicative synchronized-successor
definition. Its arguments are admitted inner cardinality objects, not arbitrary
external functions and not external natural numbers. Write R(x,y) for its
current truth value. Soundness applied to the existing certified Synch and
arithmetic-vocabulary lemmas gives the following facts at this same stage:

* zero is R-related to zero, and successor preserves R;
* R-related arguments are internal numbers; every internal number on either
  side has an R-related admitted argument on the other side;
* the two noncollapse premises make equality, Sum and Prod agree on related
  arguments.

These suffice for the exact first-order transfer theorem. Take assignments η
and θ to the k free number variables with R(η(i),θ(i)) for each i. Structural
induction on an ATerm relates its two values. Model closure supplies inner
representatives of the quoted zero and successor values, and injectivity of
the inner inclusion makes the choice of representative immaterial. The nat,
sum, prod and equality cases of an AForm then follow from the three displayed
facts. Negation, disjunction and conjunction preserve equivalence directly.

For the guarded universal case, suppose the σ-side formula holds for every
σ-number. Given a τ-number y, the onto clause gives an admitted σ-number x
with R(x,y). Extend η and θ by x and y and apply the induction hypothesis to
the body. This proves the τ-side universal statement. Conversely, totality
supplies y from each σ-number x and the same induction hypothesis proves the
σ-side statement. No external enumeration, standardness assumption or full
predicate domain enters this step. The accepted arbitrary-model reflection
theorem identifies both evaluations with the actual AForm.toTerm formulas.
For sentences the assignment condition is empty.

This is an ordinary semantic proof from the certified leaf rules and their
soundness. It locates the remaining Lean work precisely: instantiate the leaf
translations with the semantic R and package this induction in the semantic
library. It is not yet a checked uniform builder of object-C derivations, nor
does semantic preservation by itself supply such a builder without an additional
completeness argument. It also does not discharge the separate effective
coding, full higher-type interpretation or Max-arithmetic claims.

### 10.2. Current formalization boundary

The main finiteness C rules and structural type-schema proofs have passed.
The later semantic modules for arbitrary-model arithmetic reflection, the
two-stage model's domain verdicts and finite variant, the four C5 groupoid
witnesses, the abstract counting frame, and the three quoted Frege C rules
have also passed at their recorded source hashes.

The concrete two-stage infinite-number-field endpoint and the connection from
the quoted number predicate to the full model's successor orbit remain ordinary
proved arguments with **unverified Lean endpoints**. Their latest bounded checks
timed out without identifying a proof-command error. The sources were split
into support and endpoint modules for a later diagnostic check; that split has
not been compiled. The exact outcomes and resource hold are in the
[verification ledger](../source/research/2026-10-22/lean-formalization/verification-updates/infinity_arithmetic_profiles.json)
and [contribution summary](../source/research/2026-10-22/lean-formalization/arithmetic-contribution-summary.md).
The cross-base semantic-library instantiation in §10.1 and uniform object-C
proof construction remain distinct from this endpoint certification work.
