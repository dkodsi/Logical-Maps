# Maximalism forbids reversible pairing, even when pairing itself exists

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Reversible pairing has no finite protected quotient

Fix a relational type τ. Let D be a current domain of τ-objects, and
suppose a,b∈D satisfy □(a≠b). Suppose admitted ambient operations

    Pair:τ→τ→τ,       Left,Right:τ→τ

satisfy, for every current x,y∈D,

    Pair(x,y)∈D,
    Left(Pair(x,y))=x,       Right(Pair(x,y))=y.       (P)

The outputs in (P) are **object identities**. Correctness merely up to
current coextension is a different demand. No condition is imposed on
Left or Right away from the displayed pair codes.

**Theorem 1.1.** C + pure Max excludes this package.

Let c_τ be the externally finite bound from
[stable-domain-bound.md](finite-type-capacities.md):

    c_e=1, c_t=2, c_(αρ)=c_ρ^(c_α).

Max supplies ◇AtMost_(c_τ)(τ), so there cannot be c_τ+1 pairwise
necessarily distinct current τ-objects. Choose an external finite k
with 2^k>c_τ. Encode binary strings of length k by starting with a and
successively appending a or b using Pair. Closure in (P) puts every
result in D. For example, appending bit ε forms Pair(previous,a_ε),
where a_0=a and a_1=b.

Distinct strings differ at some position. A fixed finite composite
Right∘Left^j extracts that position from their codes, using finitely
many identities from (P). Those actual identities are necessary by NI.
If the codes could become identical, applying this same composite at
that possibility would identify a and b, contradicting □(a≠b).
Thus the 2^k codes are pairwise necessarily distinct, contradiction. ∎

Only a finite set of codes and their projection equations is used in
each fixed type-instance. The proof does not box the current universal
laws (P), use an infinitary conjunction, or assume that D stays a domain
of the same cardinality at future points. It is independent of the
compactness step in the general finite-quotient theorem.

In particular, take D to be the whole type, with a=⊥_τ and b=⊤_τ.
These are necessarily distinct already in C. Pure Max therefore refutes

    ∃Pair Left Right ∀x y:
      Left(Pair(x,y))=x ∧ Right(Pair(x,y))=y

at **every fixed relational type**. In categorical language, the
operational square of that carrier cannot be a retract of the carrier.
This is an obstruction to reversible data coding, not to a particular
formula for the code.

### The immediate canonical numerical consequence

At every counting type σ, C proves that its pure zero and one numerals
are necessarily distinct: zero holds of the empty property, one does
not, and this is a C theorem. Therefore Max excludes a pairing operation
on N_σ with numerical outputs and two coordinate operations satisfying
(P) on N_σ. No I_σ premise, PN equivalence, induction over nonstandard
numbers, or prior predecessor theorem is needed. Any usual pairing and
unpairing package satisfying those exact numerical equations is covered.

## 2. A bijective arithmetic pairing exists, but neither decoder does

Use the ordinary external standard semiring ℕ, with its zero and one.
Write the usual Cantor bijection as

    C(i,j)=(i+j)(i+j+1)/2+j.

Define another bijection P:ℕ²→ℕ. Write m=2i+ε and n=2j+δ, with
ε,δ∈{0,1}. Set

    P(m,n)=2C(i,j)+1                    if (ε,δ)=(1,1);
    P(m,n)=2(3C(i,j)+r)                 otherwise,

where r=0,1,2 for the cases (0,0),(0,1),(1,0), respectively.
Odd outputs encode exactly the odd/odd input pairs. For an even output
2q, Euclidean division q=3c+r recovers the other parity case, and the
inverse Cantor bijection recovers i,j. Hence P is a total bijection,
with ordinary computable—and primitive recursive—coordinate decoders.
In particular,

    P(0,0)=0,       P(0,1)=2,       P(1,0)=4,       P(1,1)=1.

Parity q:ℕ→F₂ preserves the semiring operations and satisfies

    q(P(m,n))=q(m)q(n).

Thus the expanded algebra (ℕ,+,×,P,0,1) has a two-element quotient
separating zero and one. Apply the constructive direction of the
[finite-quotient theorem, §3](finite-collapse.md) at et.
It gives a full-current pure-Max model containing distinct encoded
objects n̂, actual ambient +, × and P with their exact ordinary values,
and □(0̂≠1̂). Pair outputs stay in the encoded ℕ-domain.

Use that construction's **exact-parity** realization: two distinct
encoded naturals are necessarily distinct exactly when their parities
differ; same-parity objects have identical component coordinates and
can coalesce. Consequently neither inverse coordinate is representable:

* A right decoder would satisfy Right(0̂)=0̂ and Right(2̂)=1̂.
  The inputs can coincide, whereas the outputs cannot.
* A left decoder would satisfy Left(0̂)=0̂ and Left(4̂)=1̂.
  The same contradiction applies.

In each case NI protects the two value identities and application
congruence gives the contradiction. Every current inverse graph exists:
P is a current bijection, and the full current relation domains admit
its coordinate graphs. The failure of **each** decoder is established
for this specified exact-parity model; it is not inferred from an
incorrect claim that every finite quotient of the natural semiring is
a field. The universal conclusion of §1 is that **both** cannot exist
together in any Max model with a protected pair.

This distinguishes three levels: a current bijection graph, an admitted
operation implementing that bijection, and operations decoding its
coordinates. Here the first two hold while each part of the third fails.

## 3. The pairing demand is consistent and does not imply global ND

The ω-chain model from
[operational-real-field-separation.md, §8](operational-real-fields.md#8-necessary-quantified-infinity-at-e-and-t)
gives an especially explicit positive witness. It has individuals ℕ
fixed by every arrow and, at et, all sequences `(A_m)_(m≥n)` of subsets
of ℕ. Define coordinatewise

    Pair(A,B)_m={2i:i∈A_m} ∪ {2i+1:i∈B_m};
    Left(Z)_m={i:2i∈Z_m};
    Right(Z)_m={i:2i+1∈Z_m}.

These formulas define full admitted operation intensions: at coordinate
m, use the current extensions of the input et-objects there; at later
coordinates use their transported extensions. Tail restriction commutes
with all three constructions. Hence all three identities

    Left(Pair(A,B))=A,     Right(Pair(A,B))=B,
    Pair(Left(Z),Right(Z))=Z

hold as **whole objects**, necessarily, on the entire et carrier.
Bottom and top are a protected pair. The model nevertheless refutes
propositional ND at every world and satisfies necessary quantified
Infinity at both e and t. Thus the pairing principle is not another
formulation of global ND, Plenitude, or uniform ambient Sup.

For a positive witness to **C5 + Atomicity** plus both quantified Infinity
axioms, use the same even/odd-coordinate operations in the full standard
S5/Gallin interpretation with individual set E=ℕ and world set W=ℕ.
An et-object is a subset of E×W; splitting its E-coordinate defines these
operations pointwise at every world. Literal identity is rigid, and each
relational Boolean algebra is a full powerset of argument tuples and
worlds, so C5 and Atomicity hold. Full current predicates select the standard Frege
numeral orbit, and both E and P(W) are infinite, giving the quantified
Infinity axioms at e and t. The standard full auxiliary construction
and this orbit check are documented in
[the Gallin audit, §§4 and 6](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/audit-standard-number-models-gallin-20261022.md).
No new completeness assertion for full standard semantics is used.

## 4. Literal dummy-argument padding preserves representation

One must not overstate the type-dependence critique. A genuine split
change of representation preserves operation realizability already in
C. Suppose admitted i:σ→τ and r:τ→σ satisfy r(i(x))=x on a current
σ-domain D, where the output types are relational. If f is an n-ary
operation on D, then its operation on the image is

    f'(y₁,…,y_n)=i(f(r(y₁),…,r(y_n))).

Conversely a representative g on the image transfers back by

    f(x₁,…,x_n)=r(g(i(x₁),…,i(x_n))).

The retraction identities give the required **whole** output equalities
in both directions. NI makes the identities r(i(x))=x necessary for
each current x. Therefore possible collisions, and thus protected pairs,
are also preserved and reflected by this representation change.

In particular, literal dummy-argument padding

    i(x)=λz^ρ.x,       r(y)=y(d)

has the required retraction by β, for any fixed d:ρ. It creates no new
obstruction and removes none on its image. When an independent encoding
in a larger type admits an algebra forbidden in a smaller type, it must
use the extra representational capacity; it is not merely this split
padding of the old encoding. This caveat strengthens the comparison by
excluding a misleading version of the objection.

## 5. Assessment

The strongest consequence here is **not** that one unusual algebra has
no convenient coding. It is that Max disallows the elementary reversible
pairing interface on every fixed carrier with a protected pair, even
when its actual domain is infinite, its arithmetic operations exist,
and a bijective pairing operation itself exists. The finite proof uses
only ordinary projection identities. It therefore identifies a cost
independent of field characteristics, numerical notation, or a chosen
recursion formalism.

This is substantial evidence against Max if actual ambient operations
are expected to support ordinary reversible mathematical constructions.
It does not establish inconsistency of Max, and a defender can accept
the distinction between relational graphs and operations or use separate
higher types for fixed-depth tuples. Nor does it show that all changes
of representation are problematic: §4 proves a natural invariance class
inside C itself. The exact defect is that elementary current bijections
need not admit their ordinary operational decoding interfaces.

## Sources

* This note, §§1–5, direct source `misc`, unpaginated.
* [Exact finite bound](finite-type-capacities.md), §§1–3.
* [Finite-quotient classification](finite-collapse.md), §§1–3,
  especially its exact distinction-pattern construction.
* [Stable operational continuum](operational-real-fields.md), §8,
  for the complete typed ω-chain model and its quantified Infinity proof.
* [Gallin audit](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/audit-standard-number-models-gallin-20261022.md),
  §§4 and 6, for the positive full auxiliary interpretation and standard orbit.
