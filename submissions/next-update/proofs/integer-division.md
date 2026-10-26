# Maximalism selects which primes admit exact integer division

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Setting and the earlier theorem used

Work over the fixed relational Classicism C with pure Maximalism. Let τ
be a relational type. An operational copy of the **standard integer ring**
has distinct current objects z_n for every external n∈Z, with admitted
addition and multiplication giving their ordinary integer values. Suppose
zero and one are protected:

    □(z_0 ≠ z_1).

This is an external algebraic specification, not a claim that every
internal model of the integer axioms is externally standard. It is also
not a statement about the canonical Frege cardinalities.

Write c_τ for the size of τ in the full one-world singleton-individual
model: c_e=1, c_t=2, c_(αβ)=c_β^(c_α). The
[finite-quotient classification](finite-collapse.md) proves:

- Every such operational algebra in a Max model has an external quotient
  of size at most c_τ preserving its protected distinctions and respecting
  all additional prescribed operation values.
- Conversely, any compatible quotient yields an operational copy in
  some Max model, at any non-base relational type τ. Additional
  partial-operation prescriptions are allowed.

Every nontrivial quotient of the integer ring with a finite carrier is
Z/mZ for some external integer 2≤m≤c_τ. Indeed a unital map from Z has
kernel an ideal mZ, and its image is all of that quotient. Protected zero
and one exclude m=1. This elementary observation makes the general
classification very explicit.

## 2. Exact classification of partial division operations

For a fixed external positive integer d, an **exact d-division operation**
is an admitted H_d:τ→τ satisfying only

    H_d(z_(dn)) = z_n                 for every n∈Z.

No value on an integer not divisible by d is prescribed. In particular
this is not floor division, rounding, or a silently totalized integer
quotient with default zero.

Let D be any external set of positive integers. At any non-base relational
τ, the following are equivalent:

1. Some pure-Max model contains a protected operational integer ring with
   an exact d-division operation for every d∈D, simultaneously.
2. There is an integer m with 2≤m≤c_τ and gcd(d,m)=1 for every d∈D.
3. There is a prime p≤c_τ dividing none of the members of D.

**Necessity.** Apply the quotient theorem to the ring and all prescribed
division values. It gives Z/mZ, preserving zero and one, and compatible
division tables. For a fixed d the table has

    H_d(d·[n]) = [n].

Thus multiplication by d on Z/mZ is injective. If g=gcd(d,m)>1, the
different elements [0] and [m/g] both map to [0], a contradiction.
Consequently gcd(d,m)=1. This reasoning uses only prescribed values;
H_d need not map any other original input into the integer domain.
Every prime factor p of m now satisfies (3).

**Sufficiency.** Given m as in (2), the finite quotient table

    h_d([x]) = d^(-1)·[x]

is well-defined because d is a unit modulo m. It respects every prescribed
exact-division value. Quotient lifting therefore supplies the ring and
all H_d simultaneously in one Max model. Alternatively, totalize the
integer-valued operation on nonmultiples by the least nonnegative residue
of d^(-1)x modulo m, and apply the ordinary total-algebra version of the
lifting theorem. The values on multiples remain exactly x/d.
Condition (3) supplies (2) by taking m=p. ∎

The necessary condition is valid in every Max model, including at base
type t. The converse is an existence theorem for a Max model at τ≠t,
not a claim that all compatible operations occur in every Henkin model.

## 3. Prime preferences determined by logical type

At et, c_et=2. Therefore:

- In every protected operational integer et-copy under Max, exact
  division by any **even** positive integer is impossible.
- There is a single Max model containing such an integer copy and exact
  division by **every odd** positive integer simultaneously.

In particular division by three, five, seven, and every other odd
positive integer can coexist, while division by two cannot.

At tt, c_tt=4. The possible prime witnesses are two and three. There
are Max models admitting exact division by two, and models admitting
exact division by three, but none admitting both on one protected
operational integer tt-copy. Exact division by every positive integer
coprime to the selected prime can be realized simultaneously.

At ttt, c_ttt=16. Choosing reduction modulo five gives a Max model in
which exact division by two and by three coexist. Demanding exact
division by all primes at most sixteen is impossible there.

More generally, at every fixed relational type τ, among the finitely
many primes p≤c_τ at least one exact p-division operation must be
missing. The bound comes entirely from the syntax of the carrier type
and the pure possibility of the minimal extensional model.

This is a structural asymmetry, not a selection made by ordinary integer
arithmetic. The current integer ring, its equations, and the meaning of
exact division stay the same when its logical encoding changes.

## 4. One localization test packages the same division classification

For a set S of primes, let Z[S^(-1)] be the subring of Q obtained by
allowing precisely products of primes from S in denominators. A protected
operational copy of this ring is compatible with Max at non-base τ
exactly when some prime p≤c_τ lies outside S.

For necessity, a nontrivial finite quotient has a maximal ideal; the
corresponding finite field has characteristic p≤c_τ. Every s∈S is a unit
in the ring and remains a unit in a nontrivial quotient, so s≠p.
For sufficiency reduce into F_p, using the inverses of the allowed
denominators, then apply quotient lifting.

Thus at et, Z[1/3] is operationally compatible with protected zero and
one, while Z[1/2] is not. Both are elementary localizations of the same
integer ring. This is a corollary of the general criterion, not a second
independent discovery.

## 5. Rounding and order operations fail at every fixed type

The obstruction is stronger for familiar total operations. At **every**
relational type, Max forbids a protected operational integer ring together
with either of the following operations:

    F(n) = floor(n/d), for any fixed external integer d≥2;
    P(n) = max(n,0).

To prove this, any finite quotient from §1 would be Z/mZ, m≥2. A
represented operation must respect congruence modulo that same m.

For floor division, if m≥d, the congruent inputs 0,m have outputs
0,floor(m/d), with 1≤floor(m/d)<m. If m<d, the congruent inputs d−m,d
have outputs 0,1. Both cases violate congruence preservation.

For positive part, the congruent inputs −1,m−1 have outputs 0,m−1,
which are different modulo m. This proves both exclusions. In particular
binary maximum and minimum on the integer domain cannot have operation
representatives either: specialize maximum at zero; for minimum use
P(n)=−min(−n,0). Negation is already available as multiplication by −1.

These examples concern an integer ring that Max can operationally
represent at every non-base relational type. They are not consequences
of the surrounding ring already being impossible. The new results also
do not say that the corresponding graphs are absent: ordinary relational
definitions are available. Plenitude realizes any admitted total unique
graph after appropriate totalization outside its intended domain, so
C5+Atomicity has none of these representation obstructions when supplied
with the relevant current graphs.

## 6. Assessment

The exact-division theorem gives the sharpest *arbitrariness* objection
in this note: Max distinguishes primes according to a logical encoding
bound rather than an algebraic property of exact division. The rounding
and positive-part results give the stronger *mathematical obstruction*:
extremely basic operations are unavailable regardless of the chosen fixed
relational type. Neither establishes inconsistency of Max, and neither
prevents doing arithmetic with relational graphs.

All novelty claims here are relative to the previous local notes. The
finite quotient theorem and its model construction are retained as inputs;
the new work is the exact simultaneous-division classification and the
all-type total-operation consequences proved above.
