# The unrestricted analytical shadow of pure Maximalism

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. The exact unrestricted statement

Let A be any sentence of second-order arithmetic, with arbitrary finite
projective complexity. Its translation A^e uses the Frege numerical core
N_e, current numerical membership, and coextensional set equality. Put

    U = C + I_e + {P^e : P∈TrueΠ⁰₁},

where TrueΠ⁰₁ is the external set of all standard-true first-order Π₁
arithmetic sentences. Then

    Max(C) ⊢ A^e    iff    U ⊢ A^e.                               (1)

I_e is numerical noncollapse, not quantified individual Infinity. Pure
Max remains the finitary schema with reference theory C in its
metalinguistic side condition. All types remain relational: an arrow
ending in e is never introduced.

The lower inclusion is [Frege arithmetic](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md)
§18.4 and §37.1: Max proves I_e and every true Π⁰₁ sentence. The cited §37 establishes the first-order arithmetic comparison. The construction below directly preserves the analytical interpretation. The direct construction preserves **exactly the source
numbers and their admitted sets**, so it works for every A.

## 2. The source hierarchy and its available comprehension

Suppose U does not prove A^e. Completeness supplies a model M of
U+¬A^e. Apply the current quotient of Frege §35 and
[relational coding](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-coding-recursion-20261022.md)
§§29 and 33, with numerical individuals. The result E is an extensional
two-valued relational Henkin hierarchy whose individual domain B is
M's current N_e. It has the inherited Peano arithmetic and induction for
every admitted property with parameters at arbitrary fixed finite types.

Its predicate sort et contains exactly M's current subsets of N_e,
identified extensionally. In both directions, numerical membership and
set quantification are preserved by the quotient definition. Thus

    E ⊨ ¬A,     and E ⊨ P for every P∈TrueΠ⁰₁.                    (2)

The hierarchy admits guarded comprehension for every formula in
finitely many of its sorts, with parameters. It is not assumed full
over external subsets, externally ω-standard, or a model of ZF.

We use only the following consequences of this comprehension and
induction: arithmetical sets and relations; primitive recursion on B
relative to any admitted numerical oracle; and characteristic predicates
defined using parameters in finitely many higher sorts. Recursion with
numerical values can be proved by numerical codes for finite histories,
induction, and comprehension of the unique compatible histories. No
operation with result type e is required: its graph is enough.

## 3. Numerically coded component algebras

Fix a proposed finite Max proof π of A^e. Change its finitely many Max
axioms to their equivalent Possibility presentation. They are
◇φ₁,...,◇φ_k, where each φ_i is closed, pure, and C-consistent.

The original typed proof calculus has an effective finite-proof
presentation, with its genuine H-certificates for Logical Equivalence
and finite conversion certificates. Therefore Con(C+φ_i) is a true
Π⁰₁ sentence and holds in E. Use the ordinary countable typed Henkin
construction **inside E's numerical/set part**, as follows.

For each numerical code s of a finite list of added sentences and each
next sentence ψ, the assertion that C+φ_i+s+ψ is consistent is an
arithmetical formula. Arithmetical comprehension forms its truth set J.
A primitive recursion relative to J builds a finite decision list at
each stage, appending fresh witness implications and choosing the
consistent side of the next decision. The fresh-constant lemma and
Con(C+φ_i) prove consistency at every stage by numerical induction.
Comprehension forms the complete witnessed deductively closed theory
Γ_i from these lists.

Take the least numerical code of a closed term in each Γ_i-identity
class. Least-number reasoning applies with Γ_i as a parameter. For
each fixed original type τ this gives a definable numerical carrier
D_i(τ)⊆B. Application, term substitution, lambda interpretation under
finite assignments, and truth all have numerical graphs obtained by
comprehension from Γ_i. Application outputs are unique least codes.
The witnessed-term truth lemma is verified by external structural
induction on each standard formula, using these coded component data.
These are the countable BBK C+φ_i
algebras of the original completeness proof, not ordinary extensional
function models.

The direct completeness source is Bacon–Dorr, *Classicism*, 1 July 2022
author-hosted draft, §3.1, Theorem 3.2 and footnote 64, pp.44–45;
[source](https://andrew-bacon.github.io/papers/Classicism.pdf). The
numerical implementation is the same one audited in relational coding
§37.1–37.3, now with comprehension and numerical recursion replacing
set-theoretic Separation and Replacement. All stored data are numerical
sets or numerical relations. No sequence of higher-type choices is
being selected. Construction, consistency and deductive closure use
numerical induction inside E. Component carriers can contain internally
nonstandard term codes; the external truth lemma for each standard
formula still follows from their coded substitution and witness clauses.
No uniform truth predicate for the source E's own arithmetic, or truth
lemma over arbitrary nonstandard syntax, is asserted or needed.

Choose the least individual code a_i in D_i(e). There are only the
externally finite number k of components. For every relational type,
its bottom component code supplies a distinguished object.

## 4. Explicit root carriers: definable finite tuples

There is no need to encode arbitrary products as single higher objects.
Use finite tuple interpretations of sorts. For each original type τ,
define an external finite list L_τ of E sorts and a validity predicate
V_τ on that list. A root τ-object is a tuple satisfying V_τ.

At e put L_e=[e], V_e(x)≡(x=x), so the root's individual domain is B.
Send each root individual to the fixed a_i in component i.

Flatten a relational type as τ=σ₁...σ_l t, allowing l=0. Concatenate
the already defined lists L_σ₁,...,L_σ_l into J_τ. Let P_τ be the E
relation sort taking that finite list of arguments and returning t;
when the list is empty P_τ=t. Put

    L_τ = [P_τ, e,...,e]               (k numerical fields).

Write its tuples as (F,d₁,...,d_k). They are valid precisely when

    d_i∈D_i(τ) for every i,
    F is false whenever any of its argument tuples is invalid.      (3)

Every list is finite and every sort used is an admitted E sort: P_τ
always ends in t. The recursion is well-founded because each σ_j is
a proper subtype of τ. These are definable subsets of finite products
in the semantics, not product objects that must exist in E. A root
quantifier is translated into finitely many E quantifiers with guard
V_τ. Equality of root tuples is coordinatewise E equality.

No further quotient or representative choice is present. E is already
extensional, so equality of supported profiles is their pointwise
equality on valid argument tuples. Condition (3) makes that equality
literal even outside the represented domains.

For a fixed finite proof, the recursively generated lists, profile
sorts, validity formulas, and interpretation formulas use only finitely
many E sorts. Include all proof subtypes, expanded definitions,
H-certificates and the arithmetic/set bridges below at the outset.

## 5. Interpretation of application and the C fragment

Application to a valid argument tuple slices the supported current
profile. Its i-th numerical coordinate is obtained by the unique coded
component application graph, using a_i for an individual argument and
its i-th component field otherwise. The slice exists by E comprehension
and stays supported. Numerical outputs are specified by their unique
graphs, not by an inadmissible e→e operation.

For a lambda abstraction, form the profile defined by its interpreted
current body and conjoin the guards on its displayed arguments. Its
component fields are the corresponding coded component lambda values
under the projected parameter assignment. All exist; each is uniquely
specified. Beta holds by slicing and component beta. Eta holds because
slicing and reconstructing a supported profile gives that very E
profile, and component eta gives the same least component codes.

The current Boolean values are ordinary E truth values. Current root
identity is coordinatewise tuple equality; component equality is the
component's equality object. A quantifier has current profile given by
guarded quantification over all valid root tuples; its i-th coordinate
is the component quantifier over **all** D_i(σ). It is not restricted
to projections of root individuals. These clauses are all formulas in
finitely many E sorts, so comprehension supplies their profiles.

The free-current soundness verification is consequently the same as
Frege §37.5. H holds under these local truth, identity, application and
quantifier clauses. For Logical Equivalence, use the actual H-proof:
the lambda profiles agree on every valid tuple, and each component C
algebra identifies the component lambda values. Support gives equality
of whole root tuples. An equivalence depending on an optional premise
is never substituted for H-theoremhood. No Functionality principle is
imposed on component objects or arbitrary root objects.

Finally, φ_i is true in its i-th component, so its root proposition
differs from root bottom in that coordinate. Thus the root satisfies
◇φ_i. Purity ensures that no nonlogical constants need a new compatible
interpretation. We have built a definable root validating the finite
C fragment and every Max axiom used by π.

## 6. Root numbers without higher-type recursion

For n∈B and a valid root property Q at et, let Card_n(Q) say that Q's
current subset of B is enumerated without repetitions by a numerical
finite-list code of length n. Equivalently, use a coded finite bijection
from the strict initial segment below n. This is a formula of E with
Q's profile as parameter. Its elementary finite-cardinality laws follow
by numerical induction, including when n is internally nonstandard.

In component i, numerical recursion through its coded successor graph
defines the unique code c_i(n) of its n-th Frege numeral. Define b(n)
directly to be the root ν_e tuple with fields

    current profile: Q ↦ V_et(Q) ∧ Card_n(Q),
    component fields: c₁(n),...,c_k(n).                            (4)

Comprehension forms each displayed profile and the graph of b uniformly
in n. No recursion taking higher-type values is used. The empty-list
case and the add/remove-one finite-list law give

    b(0)=0_e,             b(n+1)=Suc_e(b(n)).                       (5)

These are whole root-tuple identities: the current profiles agree by
the cardinality laws and the component fields agree by the numerical
recursions. Removal of a root individual removes exactly that member
of its current numerical extension, regardless of the constant
individual projections in the components.

Comprehension gives a root numerical property with current extension
exactly {b(n):n∈B}, by its defining existential formula and arbitrary
bottom component fields. It contains zero and is successor-closed by
(5), so the impredicative root N_e lies in that range. Conversely every
zero-containing successor-closed root property contains every b(n),
by E's numerical induction with that property's profile as a parameter.
Thus the range of b is exactly root N_e.

For each n the current individual property [0,n) is admitted, using
its E profile and bottom component fields. It has cardinality n and
no different cardinality by finite pigeonhole. These properties
distinguish b(m) and b(n). Therefore b is a bijection between B and
root N_e, preserving zero and successor.

The current ternary graphs of E addition and multiplication, transferred
along b, are also admitted profiles by comprehension. The ordinary
Frege Sum/Prod recursion and uniqueness argument identifies the root
graphs with these graphs, exactly as in Frege §37.6. Its induction and
graph witnesses are all available here; it uses no replacement of a
family of root objects. Hence b preserves numerical arithmetic.

## 7. Exact preservation of the real part

For a valid root predicate Q at ν_e t, comprehension in E forms

    X_Q(n) ⇔ Q(b(n)) is currently true.                            (6)

The expression can be expanded by the unique tuple graph (4), so its
apparently functional notation needs no new operation. Its parameters
occupy only finitely many E sorts. Thus X_Q belongs to the **original**
E numerical predicate domain; the root creates no additional reals.

Conversely, for every admitted E numerical predicate X, comprehension
forms the supported root profile

    F_X(q) ⇔ ∃n∈B [X(n) ∧ q=b(n)].                                (7)

Give it bottom component fields. Equations (6)–(7) show that its pullback
is exactly X. Thus no old real is lost. Different root intensions with
the same numerical extension do not matter: analytical set equality
is coextensional, and all set occurrences use numerical membership.

An induction on the fixed syntax of any second-order arithmetic formula
D therefore gives, with corresponding numerical and set parameters,

    root ⊨ D^e    iff    E ⊨ D.                                   (8)

At number quantifiers use b's bijectivity; at set quantifiers use
(6) and (7); at atomic formulas use arithmetic preservation and
membership. There is no restriction on the number of alternations.

## 8. Conclude the theorem and keep its scope exact

By (2) and (8), the constructed root falsifies A^e. By §5 it validates
every axiom and inference used by the proposed finite proof π. This
contradiction proves Max(C)⊢A^e implies U⊢A^e. Together with the lower
inclusion it proves (1).

**Finite-proof sharpening.** If a particular finite Max proof π of A^e
uses, after conversion to the Possibility presentation, precisely the
extra axioms ◇φ₁,...,◇φ_k, then

    C+I_e+{Con(C+φ_i)^e : 1≤i≤k} ⊢ A^e.                           (9)

Indeed, starting with any countermodel to the displayed finite-premise
theory, the construction uses only those consistency assertions to
obtain the components; it preserves the whole source real part without
requiring any further true Π⁰₁ assumption. Completeness gives (9).
For a Max proof these finitely many assertions are standard-true. This
does not supply an effective decision procedure for which sentences
are C-consistent.

This is a finite-proof construction over arbitrary source Henkin models.
Its externally finite tuple expansions and its numerical recursion are
essential: neither a countable product of arbitrary higher domains nor
a set coding every finite type was used. The component algebra truth
lemma is the only imported completeness construction. The source
quotient, guarded tuple coding, explicit numeral map and exact real-part
preservation are described above.

The proof does not make Max effective or its models externally standard.
It does not establish any necessity-of-analysis principle. It does not
extend the unrestricted equivalence to F∞+TrueΠ⁰₁: the earlier equality
with the boxed-Choice package used Π¹₄ conservation, whose unrestricted
version has a separate Choice obstruction. A comparison with a stronger
package must therefore retain its independently proved scope.

The direct argument removes the external McLarty/Shoenfield dependency
from this Max analytical-shadow theorem. Those theorems retain their
role in the separate positive-package conservation result. Repository
validation checks structure, not proof soundness. The independent review
of the direct construction is recorded in
[unrestricted-review.txt](../evidence/proof-reviews.json).

## 9. Boxed Plenitude preserves all current analysis

The same real-part check sharpens the separate boxed-Plenitude
conservation result. Put

    B∞ = C+□Plenitude+Infinity_e+Infinity_t,

with both quantified Infinity axioms. For every second-order arithmetic
sentence A,

    B∞ ⊢ A^e    iff    C+I_e ⊢ A^e.                               (10)

Use the direct internal S5 construction of relational coding §33 over
the same E, without adding any components or invoking constructibility.
It takes worlds and individuals to be B, with type translation
h(e)=e, h(t)=et and h(αβ)=h(α)h(β). Its guarded lambda definitions verify
C and boxed Plenitude. Its singleton-world injections verify quantified
Infinity at e and t (indeed the construction verifies every required
boxed Infinity instance). These are the already proved clauses of
§§33.2–33.4; no Functional Choice is used.

Section 33.5 supplies its E-definable bijection q_e from B to the Frege
numbers at every world, preserving arithmetic. Its value q_e(n) is the
whole intension counting current n-element individual properties. Fix
a world w. For every admitted S5 numerical predicate Q, comprehension
in E gives the original numerical predicate

    X_Q(n) ⇔ Q(q_e(n))(w).

Conversely, for every original E numerical predicate X, the E formula

    Q_X(y)(v) ⇔ ∃n∈B [X(n) ∧ y=q_e(n)]

defines an admitted numerical predicate at the S5 translated type. Its
definition is independent of the world argument v, and its pullback
along q_e is X at every world. All types are admitted: q_e has relational
output, and Q_X ends in the world-predicate type et. No evaluator or
additional operation is being assumed in the source C model.

Thus at each fixed w the S5 numerical-set domain has exactly E's
extensions. The same structural induction as §7 preserves every
second-order arithmetic sentence. Starting from a C+I_e countermodel
to A yields a B∞ countermodel to A, proving (10). The converse follows
from Infinity_e⇒I_e.

The construction also preserves all added true Π⁰₁ axioms. Equivalently,
finite arithmetic antecedents can be carried through the unrestricted
conservation theorem. Consequently the completed analytical comparison is

    Th_analysis(Max(C))
      = Th_analysis(C+I_e+TrueΠ⁰₁)
      = Th_analysis(B∞+TrueΠ⁰₁).                                 (11)

This addendum concerns boxed Plenitude and current extensional analysis.
It asserts no corresponding unrestricted equality for boxed Functional
Choice, whose selection strength has a separate analytical separator.

## 10. A concrete analytical sentence independent of Max

Let S be the constructible-countable-collection sentence in
[explicit-separation.md](analytical-choice-separation.md), §4: for every real A,
if every finite constructible aleph of L[A] is countable, then their
limit is countable, expressed by the displayed countable-code Choice
instance. That note proves F∞⊢S and imports the classical Feferman–Lévy
countermodel theorem with its exact source caveats.

Assume **Con(ZFC+TrueΠ⁰₁)**. Then both U+S and U+¬S are consistent.
For the positive side, a ground model of ZFC+TrueΠ⁰₁ satisfies S by
countable Choice; its internal full Gallin interpretation yields U+S.
For the negative side, the Feferman–Lévy symmetric-model construction
gives a ZF model falsifying S, already at A=∅, while preserving the
ground model's own natural numbers and arithmetic. Its internal full
Gallin interpretation yields U+¬S. The imported forcing/symmetric-model
relative-consistency interpretation preserves each fixed arithmetic
sentence, so all the external TrueΠ⁰₁ axioms can be retained by the
finite-proof version of that transfer.

Neither argument infers standard ω from consistency: the ground model
can have nonstandard numbers. An appropriate transitive ground model
would also suffice, but is a stronger convenient semantic assumption.
Bare Con(ZFC) is not being substituted for the stated assumption about
ZFC plus all true Π⁰₁ arithmetic sentences.

Apply (1) to S and to ¬S. Under that relative-consistency assumption,

    Max(C) ⊬ S,       Max(C) ⊬ ¬S,       whereas F∞ ⊢ S.           (12)

Thus this is an explicit ordinary analytical consequence of boxed
Functional Choice that Max does not prove, even though Max decides
every first-order Π₁ sentence correctly. The same reasoning applies
to the fixed A=∅ instance. These are relative nonderivability claims,
not an assertion that every set-theoretic model has standard arithmetic
or that Max decides the remaining analytical sentences.
