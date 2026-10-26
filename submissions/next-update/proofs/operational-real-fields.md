# A stable operational real field without global ND

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Definitions and source scope

Use C in its fixed finitary relational type system. All operation outputs
below are relational types. The real-field, RigidStr, and RepPower_k
definitions are the pinned upstream definitions in
[the Analysis vocabulary](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/background.md),
with provenance in [ACCESS.md](../UPSTREAM.md).
In particular rigidity means persistence plus the database's modal
inextensibility condition; it does not mean that no previously nonmember
can transport to a member.

The underlying construction is the full two-object chain, with infinitely
many fixed individuals, from the full-action family:
[model record](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/full-two-object-chain.yaml),
[family and individual parameter](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/groups/full-action-models.yaml).
The record defaults to singleton individuals; we explicitly use its
fixed-infinite variant with individual set ℕ. The source construction is
Bacon and Dorr, *Classicism*, §3.5, pp. 58–61, with the fullness convention
in Appendix D. The field interpretation and the separation proved here
are new deductions; no recorded verdict for another variant is silently
imported.

The previously proved two-point supremum argument is in
[field-operations.md, §4](field-operations-under-max.md).
It says that a supremum operation over all ambient subproperties of an
ordered field with one protected distinct pair implies B, hence ND.
We give an explicit obstruction in the new model as well.

## 2. The full typed two-object model

There are objects r and s, with one nonidentity arrow r→s. Individuals
at both objects are ℕ, and that arrow fixes every individual. For every
relational type, flattened as `α=α₁…α_k t`, define recursively

    D_α^s = P(D_α₁^s × … × D_α_k^s);
    D_α^r = P(D_α₁^r × … × D_α_k^r) × D_α^s.

At t this gives `D_t^s={0,1}` and `D_t^r={0,1}×{0,1}`. Let π be
the second-coordinate projection at relational types and the identity
on individuals. Application slices the current relation extension and
applies the terminal relation to the projected arguments. Thus

    π(f(x)) = π(f)(π(x)).

The r-coordinate of a quantifier ranges over its whole root carrier;
its s-coordinate ranges over the whole terminal carrier. A lambda
abstraction pairs its current extension with the terminal interpretation
of its body under the projected parameter assignment. Equality is
literal object identity at each object. At r, `a=b` consequently has
coordinates `(a=b, π(a)=π(b))`.

These are full action-model domains at **every** admitted type. They
validate H, β, and η coordinatewise. For Logical Equivalence, use its
actual H-proof certificate: equivalent bodies have equal current
extensions and equal terminal abstractions, so the resulting root
objects are identical. This does not apply Logical Equivalence to
field-dependent equivalences. The arbitrary powerset factors supply
every abstraction just described and every relation used below.

Global ND fails at r. The two propositions `(1,0)` and `(0,0)` are
different at r but have the same terminal image. Their possible identity
therefore holds. This is a failure of propositional ND, not an issue
about unverified higher types.

### The exact rigidity test in this model

For a relation Y of any finite arity, let Y_r be its current extension
and Y_s its terminal extension. On tuples, π acts coordinatewise. Then

    Rigid(Y) at r  iff  Y_s = π[Y_r].                (R)

Persistence is exactly the inclusion `π[Y_r]⊆Y_s`. For inextensibility,
suppose a test relation Z necessarily covers each current Y-tuple.
This says `Y_r⊆Z_r` and `π[Y_r]⊆Z_s`. Such tests imply `Y≤Z` exactly
when `Y_s⊆π[Y_r]`: if a terminal Y-tuple were outside that image,
fullness would supply a test with root extension Y_r and terminal
extension π[Y_r], violating inextensibility. At s, every relation is
rigid because there is no further nonidentity arrow. These observations
prove both directions of (R), including the leading boxes in the
database's definition.

The relevant condition is an **image** condition, not the generally
stronger preimage condition `Y_r=π⁻¹[Y_s]`.

## 3. A necessarily complete rigid real field

Put `τ:=et`. Then

    D_τ^r=P(ℕ)×P(ℕ);             D_τ^s=P(ℕ).

Choose an external bijection `r↦A_r` from the standard reals to P(ℕ),
arranged so that `A_0=∅` and `A_1=ℕ`. Write

    r̂ := (A_r,A_r),       F_r := {r̂ : r∈ℝ},
    F_s := {A_r : r∈ℝ}=D_τ^s.

These extensions define an admitted field-domain predicate F. Projection
is a bijection from F_r to F_s. The field's zero and one at r are
literally `⊥_et` and `⊤_et`, hence are necessarily distinct. More
generally, distinct members r̂,ŝ remain distinct after projection, so
every current field distinction is necessary.

Interpret order, addition graph, multiplication graph, and the field's
natural-number predicate at r by their standard real extensions on F_r,
and at s by the corresponding extensions on the A_r. For instance,

    Add_r(r̂,ŝ,t̂) iff r+s=t;
    Add_s(A_r,A_s,A_t) iff r+s=t.

All these graph relations hold only of field arguments at each object.
Each terminal extension is exactly the image of its root extension.
By (R), F and all the displayed relations are rigid.

At r, every external subset of F_r is the current extension of an
admitted subproperty, by fullness. At s, the same is true of F_s.
Both ordered fields are therefore Dedekind complete for all admitted
subproperties, with their ordinary external real suprema. The least
inductive subproperty is the standard natural-number subset at each
object: that subset itself is admitted, and external finite induction
gives the converse inclusion. Thus the pinned Real and RigidStr
conditions hold at r and s:

    □Real_τ(ℜ)  and  □RigidStr(ℜ).

No element of the terminal field lacks a unique current field lift.
It is nevertheless possible for a nonfield root object `(A,B)` with
A≠B to transport to a member B of F_s. This is compatible with
rigidity under (R); it must not be confused with growth of the field's
represented real values.

### Necessary arithmetic-operation representatives

For every external scalar function `h:ℝ^n→ℝ`, define an admitted
operation H with output type et as follows. Its root relation profile
on field inputs is

    H_r(r̂₁,…,r̂_n,k) iff k∈A_(h(r₁,…,r_n)),

and is false if any input is outside F_r. Its terminal relation is

    H_s(A_r₁,…,A_r_n,k) iff k∈A_(h(r₁,…,r_n)).

At every root field input the application H(r̂₁,…,r̂_n) has both
coordinates equal to A_h. It is therefore the whole object h(r₁,…,r_n)^,
not merely a coextension of it. Terminal correctness holds on every
terminal field input as well.

In particular addition, multiplication, negation, and reciprocal
(normalized to zero at zero) have representatives correct necessarily
on the field. The representatives themselves are rigid relations by
(R), since every terminal input tuple lifts to a root field tuple.
Every external finite-arity scalar map has the same property. This
includes much more than the two basic field operations, while global
ND still fails as shown in §2.

## 4. Represented powers and a restricted supremum functional

For each finite arity k and each external set `S⊆ℝ^k`, define the
canonical relation C_S by

    (C_S)_r = {(r̂₁,…,r̂_k) : (r₁,…,r_k)∈S};
    (C_S)_s = {(A_r₁,…,A_r_k) : (r₁,…,r_k)∈S}.

Every C_S is rigid by (R), and it is supported on the field at each
object. Distinct C_S have distinct terminal images, so they are
necessarily distinct. Let P_k be the admitted property whose current
extension consists exactly of these canonical relations and whose
terminal extension is the whole terminal k-ary relation carrier.
Again (R) makes P_k rigid.

At r, every current ambient relation has some extension S when
restricted to F_r; its canonical C_S is in P_k and agrees there. At s,
every relation is already the projection of exactly one canonical C_S.
Consequently the **exact pinned** represented-power condition holds
necessarily:

    □RepPower_k(P_k,F),        for every fixed finite k.

This checks its support, member-rigidity, family-rigidity, and boxed
coverage clauses, rather than merely asserting that many subsets exist.

There is an admitted supremum operation U which is correct on P_1
necessarily. On a current canonical C_S, give its current output the
profile A_sup(S) when S is nonempty and bounded, and A_0 otherwise.
At the terminal point, define the same external supremum function on
all subsets of the terminal field, with the same default. Values at
noncanonical root inputs can have arbitrary current profile. At each
canonical input the two output coordinates match exactly, so U returns
the designated real object. It is correct at all terminal inputs in
its indicated domain as well.

Thus represented powers and a genuine supremum functional **on those
representatives** coexist with failure of global ND. This is a precise
representation restriction, not a change to the current completeness
axiom, which already quantified over every current subproperty.

## 5. No supremum operation on all ambient subproperties

Choose root predicates Y_0,Y_1 of type τt with

    (Y_0)_r={0̂};             (Y_1)_r={0̂,1̂};
    (Y_0)_s=∅;               (Y_1)_s=∅.

Both are current nonempty bounded subproperties of F, but their
terminal images are identical. They therefore can be identical. If an
ambient operation Sup returned the current least upper bound for every
such property, it would satisfy

    Sup(Y_0)=0̂;             Sup(Y_1)=1̂.

NI makes both identities necessary. Their identical terminal inputs
would then have the necessarily different outputs 0̂ and 1̂, a
contradiction. This proves directly that no such Sup exists.

The general theorem that Sup plus a protected pair implies ND gives
the same conclusion; the two predicates display the actual failed
uniformization in this model. They need not remain nonempty at s. The
obstruction is that an ambient operation remains an operation even
outside the domain on which its correctness was initially required.

Likewise there is no ambient normalization operation which sends every
current subproperty of F to its canonical member of P_1. Such an
operation would send Y_0 and Y_1 to C_{\{0\}} and C_{\{0,1\}}, which
have different terminal images. Conversely, the relational graph of
this normalization exists and is currently total and unique: (R) makes
a rigid relation supported on F uniquely determined by its current
extension. The distinction is exactly between a complete represented
power and an operation selecting its representatives from every ambient
description.

**Separation theorem.** In the ordinary external ZFC metatheory, the
full typed C model just constructed simultaneously satisfies

* a necessarily complete rigid real structure at et;
* necessarily correct rigid representatives of its scalar arithmetic,
  and indeed of every external finite-arity scalar map;
* represented powers P_k satisfying □RepPower_k at every finite arity;
* a necessarily correct supremum operation on P_1;
* failure of global ND and failure of a supremum representative on all
  current bounded nonempty subproperties.

This is a genuine separation between the two representation demands.
It does not suggest treating the stronger two-point supremum principle,
already known to imply ND, as a new independent axiom.

## 6. Exact conditions for representing field isomorphisms

Here the setting is any **full action model** of C, not only the
two-object example. Suppose current nontrivial fields F and G have
ambient representatives of addition and multiplication. Their carrier
types may differ and are relational, as required already by those
ambient arithmetic operations' output types.
Let h be a current field-isomorphism graph from F onto G, with its usual
zero and one preservation. Write z_F,u_F,z_G,u_G for their units.

**Theorem 6.1.** A current ambient operation realizes h if and only if

    □(z_F=u_F → z_G=u_G).                           (I)

**Necessity, already in C.** A representative H satisfies the actual
identities `H(z_F)=z_G` and `H(u_F)=u_G`. NI and application congruence
give (I). This implication does not need fullness.

**Sufficiency, using fullness.** The collapse dichotomy from
[field-operations.md, §2](field-operations-under-max.md)
shows that (I) preserves every possible collision of old field inputs.
Precisely, at an arrow a out of the current object, if two current
F-elements x,x' have equal images x_a=x'_a, either x=x' already or
z_F and u_F have coalesced there. In the latter case (I) coalesces
z_G,u_G, so all transported current G-elements, including h(x) and
h(x'), are equal there. Hence

    x_a=x'_a  →  h(x)_a=h(x')_a.                    (K)

Write G's relational type as `β₁…β_l t`. Define an operation intension
at every arrow a, on arguments v and the remaining output tuple b̄,
by

    H_a(v,b̄) iff ∃x∈F_current
                   [v=x_a ∧ h(x)_a(b̄)].

The existential here describes an external set-theoretic construction
of a full intension, not an additional object-language quantifier over
past objects. Fullness admits that intension. The following component
check makes explicit why this is valid in a general action category,
including categories with parallel arrows or returns.

Let the current object be o. If `a:o→v` and `b:v→w`, transport of an
intension is precomposition on its arrow coordinate, so

    (a·H)_b(v',b̄) = H_(b∘a)(v',b̄).

This is a single intension specified on all arrows out of o, not an
independent choice of an operation at each future object. In particular
its iterated transports satisfy `b·(a·H)=(b∘a)·H` by associativity.
For a current x∈F, the b-component of applying the transported operation
to its transported argument is therefore

    ((a·H)(a·x))_b(b̄)
      iff ∃x'∈F_current
            [(b∘a)·x=(b∘a)·x' ∧ ((b∘a)·h(x'))_id(b̄)]
      iff ((b∘a)·h(x))_id(b̄),

where the reverse implication uses x'=x and the forward implication
uses (K) at the composite arrow b∘a. The tuple b̄ ranges over the **whole**
output-argument carrier at w, including tuples which are not transported
from o or v. Thus equality holds at every future arrow and every future
argument tuple, giving the whole identity

    (a·H)(a·x)=a·h(x).

Taking a to be the identity proves H(x)=h(x) at o. No compatibility is
required between the truth extensions at unrelated arrows: full action
intensions are arbitrary such extensions, with transport subsequently
defined by the displayed precomposition rule. At a future input which
is not an image of an old F-element, the defining relation may be false;
it can acquire witnesses after further transport without violating any
action-model obligation. We assert correctness on the transported old
graph, not on an unspecified extension of h to new field elements.
This proves sufficiency. ∎

When both carrier types are relational, the inverse graph is also
representable exactly when the reverse of (I) holds. Consequently both
directions have ambient representatives exactly when

    □(z_F=u_F ↔ z_G=u_G).

In particular every current isomorphism between two protected
operational fields has representatives in both directions in full
action models, even where global ND fails. A protected source can map
operationally into a collapsing target; the inverse direction cannot.
The sufficiency assertion is **not** extended to arbitrary Henkin
models, where the constructed intension may be absent.

## 7. A one-way isomorphism between two operational real fields

The two-object model also contains the common-terminal-coordinate field

    G_r := {(A_r,∅):r∈ℝ}.

Give G_r the current standard real graphs. Its arithmetic operations
have current output profiles A_(r+s), A_(rs), etc., and constant empty
terminal operation values. Their outputs match both coordinates, so
these are genuine ambient representatives on G_r. Full current subsets
make G_r a current complete real field. Unlike F, this field is not
asserted to remain nontrivial or complete after projection: all of its
current values coalesce to ∅ there.

The current field isomorphism

    h(r̂)=(A_r,∅)

has an ambient representative. Define its current output profile to
be A_r on r̂ and its terminal operation to be constantly empty. Its
inverse cannot be represented: h(0̂) and h(1̂) have equal terminal
images, whereas 0̂ and 1̂ are necessarily distinct. The two inverse
value identities would contradict NI and application congruence.

Thus even two current complete real fields which **both** have genuine
addition and multiplication can be isomorphic only in one operational
direction. The difference is exactly the unit-collapse condition in
Theorem 6.1, not a disagreement about their ordinary current algebra or
analysis. The protected copy F supplies the principal stronger result:
stable, necessary field algebra and represented higher-order structure
need not impose global ND or uniform choice of ambient representatives.

## 8. Necessary quantified Infinity at e and t

The two-object example has only four current propositions, so it is not
the appropriate final witness when the two quantified Infinity axioms
are required. Replace its category by the ordered set ℕ: there is one
arrow n→m exactly when n≤m. Keep the individual carrier ℕ at every
object, with every arrow fixing individuals. For each relational type
`α=α₁…α_k t`, use the full action domains

    D_α^n = ∏_(m≥n) P(D_α₁^m × … × D_α_k^m).

This is a recursion on types, not on worlds: all the argument-type
domains on the right have already been constructed. Transport n→m is
restriction to the tail beginning at m. Application at n is defined
at every future coordinate l by applying the relation's l-component
to the l-transports of its arguments. Quantification at each l ranges
over all of D_σ^l. Lambda uses the entire family of these extensions.
These are the full action-model definitions, so abstraction, all-type
quantification, βη, and the fixed C Logical Equivalence rule are
available exactly as in §2. There is no restriction to a chosen family
of field objects or predicates.

For an admitted relation Y at n, rigidity is now characterized by

    for every n≤m≤l,   Y_l = image_(m→l)(Y_m).       (Rω)

Indeed persistence gives the forward image inclusion at every m→l.
At m, fullness supplies the test relation whose extension at each
future l is exactly image_(m→l)(Y_m). This is the least intension
necessarily containing each current Y-member, so weak inextensibility
gives the reverse inclusion. Taking this argument at every m≥n gives
the leading box in inextensibility. Conversely (Rω) implies both
persistence and every such inextensibility instance. In particular
it suffices to verify the image equality for the concrete fields and
families at every pair of worlds; no preimage condition is asserted.

### 8.1. The same standard continuum at every world

At τ=et, an element of D_τ^n is a sequence `(B_m)_(m≥n)` of subsets
of ℕ. For each real r let r̂_n be the **constant** sequence with value
A_r, using the bijection from §3. Put

    F_n={r̂_n:r∈ℝ}.

For n≤m the transport of r̂_n is r̂_m, and every F_m element has a
unique F_n lift. Define the field-domain intension and the order,
addition, multiplication, and field-natural-number intensions by their
standard real extensions on these constant sequences at every world.
For each relation, its later extension is exactly the image of its
earlier extension. Thus (Rω) proves their rigidity. Zero and one are
the all-empty and all-ℕ sequences, literally ⊥_et and ⊤_et, and all
distinct real values remain distinct under every tail restriction.

Every subset of F_n is the current extension of an admitted predicate:
put that subset at coordinate n and choose any extensions elsewhere.
The current complete ordered field is therefore standard ℝ at every
n, and its least inductive subproperty is the standard natural numbers
by the same admitted-orbit argument as before. Consequently □Real and
□RigidStr hold, with their full higher-order completeness clauses.

For each external scalar h:ℝ^k→ℝ, define H at each coordinate m by

    H_m(r̂_(1,m),…,r̂_(k,m),i)
        iff i∈A_(h(r₁,…,r_k)),

and make that relation false off the constant-sequence field inputs.
Its extension at any later coordinate is the image of its earlier
extension, so H is rigid by (Rω). Applied to field arguments at n,
the resulting et-object has **every** future coordinate equal to
A_h. Hence it is literally the designated constant-sequence output,
not only correct at n. This proves the necessarily correct scalar
operation claims, including addition and multiplication.

For S⊆ℝ^k, let C_(S,n) be the intension whose extension at every
m≥n is the standard S-relation on F_m. Transport takes C_(S,n) to
C_(S,m), preserving and reflecting S. Let P_(k,n) consist of these
canonical relations. Relations C_S and the family P_k satisfy (Rω);
support and all-stage coverage give □RepPower_k exactly as in §4.
At coordinate m, a supremum operation on P_1 returns the profile
A_sup(S) at a canonical input C_(S,m), with the same zero default.
Every future coordinate agrees, so it is a genuine operation correct
necessarily on the represented power. No arbitrary ambient predicate
is silently identified with its canonical representative.

### 8.2. Both quantified Infinity axioms, necessarily

At every n, D_e^n=ℕ and

    D_t^n=P({m∈ℕ:m≥n})

are infinite. External infinitude alone would not prove the quantified
axioms in an arbitrary Henkin model, so the following fullness argument
is required here.

Fix n and either counting type σ=e or σ=t. Let z_j be the current
value of the standard j-th Frege numeral. At the current coordinate,
induction on the external integer j shows that z_j holds of a property
exactly when its current extension has j elements: zero is emptiness,
and the Frege successor clause removes one current member. A full
current predicate having extension exactly `{z_j:j∈ℕ}` is admitted.
It contains zero and is closed under successor, so the impredicative
FiniteCardinality definition contains no objects outside this standard
orbit. Conversely each z_j belongs by finite iteration of the defining
closure clauses. Thus the current numerical field is exactly that
orbit, and none of its members holds of the universal property of the
infinite D_σ^n. This is the **quantified** Axiom of Infinity at σ,
not merely its standard finite lower-bound schema.

The argument applies at every n. Therefore the model satisfies

    □AxiomOfInfinity_e ∧ □AxiomOfInfinity_t.

The exact axioms are the records
[axiom-of-infinity-e](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/principles/axiom-of-infinity-e.yaml)
and [axiom-of-infinity-t](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/principles/axiom-of-infinity-t.yaml).
No Potential Infinity rule or schema is substituted for them.

### 8.3. ND and uniform supremum selection still fail

At any n the propositions whose true coordinates are {n} and ∅ are
currently distinct but become identical after restriction to n+1.
Hence propositional ND fails at every world.

At n choose predicates Y_0,Y_1 whose current extensions on F_n are
{0̂_n} and {0̂_n,1̂_n}, and whose extensions at **every** m>n are empty.
They are currently bounded nonempty subproperties and become the same
whole predicate at n+1. Their required supremum outputs, by contrast,
would be the protected constant sequences 0̂_n and 1̂_n. NI and
application congruence therefore exclude an ambient supremum operation
on all current bounded nonempty subproperties, just as in §5. The same
pair excludes an operation normalizing every ambient subproperty to
its canonical representative. These failures also hold at every n.

**Strengthened separation theorem.** The full typed ω-chain model
satisfies necessary quantified Infinity at e and t together with every
positive clause of the separation theorem in §5. At every world it
refutes propositional ND, unrestricted supremum representation, and
uniform normalization to its complete represented powers. Thus these
failures persist even with an always infinite propositional domain and
a necessarily complete, rigid, operational real continuum.
