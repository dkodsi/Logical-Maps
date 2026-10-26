# Field operations, supremum functionals, and modal collapse

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Exact vocabulary and the finite possibility used

Use the pinned upstream definition of a real number structure in
[upstream/background.md, Analysis](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/background.md), at the revision
recorded in [ACCESS.md](../UPSTREAM.md). A structure at type τ has a domain
predicate F, an order relation, addition and multiplication **graphs**,
zero, one, and its least inductive number predicate. Its current field is
Dedekind complete for every admitted bounded nonempty subproperty. An
operation representative of addition is an admitted operation
`A:τ→τ→τ` with

    ∀x,y∈F, Add(x,y,A(x,y));

and similarly for multiplication. Its correctness is asserted only on
the current field. Throughout the operation results τ is relational,
so these operation types are admitted; no e-valued operation is used.

Write `z,u` for the field's zero and one, to distinguish them from logical
bottom and top. Say that a current pair a,b is **protected** if
`□(a≠b)`. This is a condition on that pair, not a new global named axiom.

For each fixed type τ, let cτ be its finite carrier size in the full
one-world singleton-individual C model:

    c_e=1;       c_t=2;       c_(αβ)=(c_β)^(c_α).

The pure sentence `AtMost_cτ(τ)` says that every cτ+1 τ-objects include
an equal pair. It is C-consistent in that finite model. Pure Maximalism
therefore gives `◇AtMost_cτ(τ)`. This is the finite bound proved and
sharpened independently in [stable-domain-bound.md](finite-type-capacities.md).
Only this one pure possibility instance is used in each fixed-type
obstruction below. Field parameters are not added to the Maximalism schema.

## 2. With addition and multiplication, a field either embeds or collapses

**Theorem 2.1 (C).** Suppose a current nontrivial field on F has genuine
addition and multiplication representatives A and M. For any distinct
current a,b∈F,

    □(a=b ↔ z=u).                                      (1)

For every current x∈F,

    □(z=u → x=z).                                      (2)

Neither an inverse operation nor a negation operation is required.

**Proof.** For a≠b, choose from the current field axioms c,d,r∈F with

    A(b,c)=z;       A(a,c)=d;       d≠z;
    M(d,r)=u;       M(z,r)=z.

Here c is the additive inverse of b, d is a−b, and r is an inverse of
d. These are individual existential witnesses supplied by the current
relational field laws. They are not simultaneous choice operations.
Every displayed equality is an identity of actual objects, and so is
necessary by NI. At any possibility where a=b, congruence for A gives
d=z, and congruence for M gives u=z. This proves the forward half of
(1).

For any current x, the actual identities `M(x,u)=x` and `M(x,z)=z`
are necessary. Thus z=u implies x=z at every possibility. Applying
this to a and b gives the reverse half of (1), as well as (2). ∎

This is the familiar fact that a unital homomorphism from a field is
injective or trivial, proved here by finitely many actual identities.
It does not assume that the whole field, its domain predicate, or its
field laws persist. In particular (2) is

    ∀x∈F, □(z=u → x=z),

not an unlicensed boxed universal over future members of F.

**Corollary 2.2.** For such a current field, the following are equivalent:

* `□(z≠u)`;
* every pair of distinct current field elements remains distinct;
* some pair of distinct current field elements remains distinct.

The first implication and the implication from any protected pair use
(1); the middle assertion includes z,u.

**Corollary 2.3.** If the field has more than cτ current elements, Pure
Maximalism forces `◇(z=u)`. Consequently it forbids such a field with
both operation representatives and a protected pair.

Choose cτ+1 distinct current field elements. At the pure possibility
`AtMost_cτ(τ)`, at least one pair is equal. The finitely many instances
of (1) make z=u there. This is a finitary argument with current
parameters: it requires neither current standardness nor a boxed
universal field law. A complete ordered field has the required finite
list by its ordinary characteristic-zero arithmetic.

## 3. For a real field, addition alone already gives the obstruction

The preceding argument applies to arbitrary fields. Divisibility makes
the conclusion stronger for real fields.

**Lemma 3.1 (C, finite group calculation).** Fix an external positive
integer m and put q=m!. Let G be a current group at a relational type τ,
with identity z and a genuine ambient representative A of its group
operation. If a current x∈G has a q-th group root y∈G, then

    □(AtMost_m(τ) → x=z).                           (3)

In additive notation, a q-th root means `[q]y=x`, where `[k]y` is the
finite term obtained by k repetitions of A starting from z. Commutativity
is unnecessary for this lemma.

**Proof.** Consider the m+1 terms

    [0]y, [1]y, …, [m]y.

AtMost_m makes some `[i]y=[j]y`, i<j. For each of the finitely many
pairs, choose a current group inverse v_i of `[i]y`. The ordinary
current group identities give

    A(v_i,[i]y)=z;       A(v_i,[j]y)=[j−i]y.

NI makes them necessary. At that possible collision, congruence therefore
gives `[d]y=z`, where d=j−i and 1≤d≤m. Since d divides q, ordinary
current group calculation also gives the identity

```text
[q]y = [q/d]([d]y).
```

This identity, `[q]y=x`, and `[q/d]z=z` are necessary by NI. Substitution
at the collision yields x=z. There are only finitely many possible
pairs i,j, so these finitely many conditional deductions prove (3). ∎

**Theorem 3.2.** Suppose Pure Maximalism holds and a current group at τ
is cτ!-divisible and has an ambient group-operation representative.
Then every fixed finite list of its current elements can possibly
coincide with its identity. In particular no distinct current pair is
protected.

For each element in the finite list, choose its cτ!-th root and apply
Lemma 3.1. The finite conjunction of the resulting boxed implications,
together with `◇AtMost_cτ(τ)`, gives the stated simultaneous collapse.
This is not a claim of `◇∀x∈G(x=z)` over possibly new future members.

**Corollary 3.3.** A current complete ordered real field with an addition
representative cannot contain a protected pair under Pure Maximalism.

Its additive group is q-divisible for each fixed positive integer q:
the current relational field laws give division by the nonzero numeral
q. No multiplication or inverse **operation** is required for this
existential fact. Apply Theorem 3.2 with q=cτ!. Completeness itself is
not needed; a characteristic-zero field's additive group suffices.

Thus, at type t, only halving is needed: c_t=2, so q=2. Three possible
iterates of a half give the obstruction. The proof identifies a concrete
arithmetic requirement and avoids an appeal to an infinite future field.

## 4. A supremum representative with a protected pair implies ND

Suppose a current ordered field contains a<b with `□(a≠b)`. Assume an
admitted operation

    Sup : (τt) → τ

returns the field's least upper bound for every currently nonempty,
bounded subproperty of F. No correctness outside that domain is required.

**Theorem 4.1 (C).** These premises imply all-type ND.

**Proof.** For any proposition p, form the admitted property

    C_p(x) := x=a ∨ (p ∧ x=b),

and put `E(p):=Sup(C_p)`. Each C_p is currently a nonempty subproperty
of F bounded above by b. If p is currently true, the current least upper
bound law gives `E(p)=b`. Also `E(⊥)=a`, since C_⊥ is the singleton a.

These two identities are necessary by NI. Since a and b are necessarily
distinct, application congruence gives `□(p≠⊥)` whenever p is currently
true. In C, `p≠⊥` is `◇p`. Thus

    p → □◇p.

This is axiom B. The recorded C implication B⇒ND, using NI, supplies
all-type ND. No assumption that Sup or the field remains a supremum
structure is made. ∎

The entire argument uses Sup only on singleton sets and two-point sets.
Equivalently, an operation realizing the current two-valued truth choice
between protected labels is already strong enough. This isolates the
representation demand without restating Analytic Necessitism.

**Corollary 4.2.** Pure Maximalism forbids such a supremum representative
on a current real field with a protected pair. ND would make every
distinct current field pair necessary, contradicting the fixed-type
stable-size bound and the field's cτ+1 distinct current elements.

Any protected pair in an ordered field can be oriented as a<b currently,
so the theorem does not depend on whether the protected pair is its
zero and one.

## 5. A Max model with a standard operational continuum

The protection premise cannot be removed. Use the free-current Max root
constructed and verified in [current-analysis.md](current-analysis-under-max.md),
with root individuals ℕ and one countable Henkin C component M_i for
each C-consistent closed pure sentence. For every relational type α,
its root objects have an arbitrary current extension and a coordinate
in each M_i. Pure Maximalism follows from the corresponding component
witnesses, exactly as in that note.

Take τ=et and select the following current subdomain of D_τ:

    F := {(A,(⊥_τ^{M_i})_i) : A⊆ℕ}.

All members have the same component coordinates, but their current
extensions range over every subset of ℕ. Consequently |F| is continuum.
Choose an external bijection between F and the standard real numbers,
with the all-empty tuple corresponding to real zero if desired. Give F
the usual ordered-field structure through that bijection. Full current
extensions represent its field predicate, order, arithmetic graphs, and
the natural-number subset. Every external subset of F is represented,
so this is a current complete ordered field with the full standard
first- and second-order analytical interpretation.

**Common-coordinate realization lemma.** Every external scalar-valued
function from any finite product of root type domains into F has a
genuine admitted ambient operation representative.

To prove the lemma, let h be such a function. Define the operation's
current extension so that its output at each input has precisely the
subset of ℕ which is the first coordinate of h(input). At component i,
choose the constant operation with value `⊥_τ^{M_i}`; it exists by
ordinary lambda abstraction. Application then returns exactly h(input):
both its current profile and every component coordinate agree. This
uses the full current factors already present in the Max construction,
not full operation domains in its arbitrary Henkin components.

Apply this lemma to real addition, multiplication, negation, inverse
(with value zero at zero), and any ordinary real-valued function. The
same lemma gives a supremum functional on the whole root domain D_(τt):
take the real supremum of the property's current F-extension when that
extension is nonempty and bounded, and take zero otherwise. Its actual
output identities are exact, and its component coordinates are constant
bottom, as required.

Thus one Max model simultaneously has genuine representatives for all
these current scalar operations and functionals. Every pair of distinct
members of F can coalesce: their equality proposition has false current
coordinate and true component coordinates. It differs from bottom, so
its possibility is true. The field's zero and one are distinct currently
but can coincide. No protected pair exists in F.

This is not merely an unspecified possibility that the operations might
be compatible. It is an explicit model construction, in the same ordinary
external ZFC metatheory used for current-analysis.md.

## 6. Isomorphic current real fields can have different operation closure

The witness can stay at the **same type et** and change just one field
element. In §5 choose real zero to be `⊥_et`, and write u∈F for real
one. Logical `⊤_et` is outside F, since its component coordinates are top
rather than bottom. Swap u and `⊤_et` by a current permutation graph,
and transport the field graphs along that permutation. The new field has
domain

    F' = (F − {u}) ∪ {⊤_et},

zero `⊥_et` and one `⊤_et`. It is currently isomorphic to F as a complete
ordered field, with the same full standard analytical interpretation.
The graph transport and preservation of completeness are detailed below.

The new field contains the protected pair `⊥_et,⊤_et`. Corollary 3.3
therefore forbids an addition representative for F', and Theorem 4.1
forbids a supremum representative. The original F has both, and all the
other scalar representatives constructed in §5.

Extend the inverse swap from F' to F to a current function from the whole
D_et into F, with default value `⊥_et` outside F'. The common-coordinate
realization lemma supplies an ambient operation

    h : et → et

realizing this function, so its restriction to F' is a field isomorphism
onto F. Its inverse cannot have an ambient representative. Indeed
`h(⊥_et)=⊥_et` and `h(⊤_et)=u` are distinct members of F and can coincide.
If an operation g were their inverse, the current identities

    g(h(⊥_et))=⊥_et;       g(h(⊤_et))=⊤_et

would be necessary by NI, contradicting that possible coincidence and
the necessary distinctness of logical bottom and top. This is a concrete
one-way operational coding of the ordinary continuum, without changing
the carrier type. The whole-carrier real field on D_t from
[current-analysis.md](current-analysis-under-max.md) gives another such example.

Consequently ambient operation realization is not invariant under
current graph isomorphism. This is a genuine distinction from ordinary
current mathematical truths: both fields satisfy the same complete
standard analysis, but only one admits the displayed analytic operations.
No claim is made that Max forces an anchored real structure at every
fixed type. These real structures are provided by the explicit model,
and the general obstructions are conditional on the stated current
structure and protected pair.

There is, however, a useful uniform normalization when a current real
structure at a relational type τ is given. Its field can be moved, by a
current bijection **graph**, so that its zero is `⊥_τ` and its one is
`⊤_τ`. First swap its zero with bottom; then swap the transported one
with top. The second swap fixes bottom, since the transported one differs
from bottom. For any two parameters a,b, the graph

    (x=a ∧ y=b) ∨ (x=b ∧ y=a) ∨
      (x≠a ∧ x≠b ∧ y=x)

is a current permutation, including when a=b. Composition of the two
graphs is admitted by ordinary abstraction. No swap **operation** is
assumed. Push the field domain and its graphs along this current
permutation. For every admitted subproperty of the transported field,
its pullback is an admitted subproperty of the original field; transport
its least upper bound back along the graph. Hence the new field remains
complete for all admitted subproperties. No modal comprehension or
rigidity premise is needed.

The new field has the protected pair `⊥_τ,⊤_τ`. Consequently, at every
fixed relational type τ,

    Max + existence of a current real structure at τ
      ⇒ not every current real structure at τ has an addition representative;

and likewise for supremum representatives. The existence premise is
essential to this formulation; no assertion about field existence at
every type is being smuggled into Max. These are concrete failures of
uniform graph realization. Plenitude supplies the corresponding
representatives by totalizing the current unique graphs with a default
zero, so these examples are applications of known representation strength,
not proposed new independent axioms.

## 7. Scope and the most useful formulations

The results separate three demands which should not be conflated:

* **Current analytical truth:** compatible with pure Max, even full
  standard second-order analysis.
* **Current scalar operations:** also compatible with pure Max; §5
  includes arithmetic operations and a supremum functional.
* **Those operations with a protected pair:** addition on a real field
  conflicts with the finite possibility supplied by Max; a supremum
  functional already implies ND.

For ordinary fields, the clean structural lemma is the collapse
dichotomy (1): with addition and multiplication represented, preserving
one distinction preserves every current field distinction. For real
fields, the stronger and simpler negative test needs only their divisible
additive group. For analysis, the two-point supremum calculation isolates
the additional strength of an ambient functional particularly directly.

These are statements about operation representatives and exact object
identities. The field graphs and their ordinary current proofs remain
available throughout. None of the arguments proves Maximalism
inconsistent, promotes a current field law to a necessary universal,
or assumes standardness in the finitary obstruction proofs.
