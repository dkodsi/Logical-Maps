# Rigid Power fails at the next property type

Original mathematical argument, direct source misc; unpaginated.

## 2. Facts and notation from the exact model

Every individual domain is N. At B the coloured set E is the even numbers;
at C it is {0,1}. Arrows are the already specified globally surjective maps:
rank cannot decrease, arrows out of B or C preserve colour, and arrows out
of A have no colour restriction. In particular, the entrance i:A->B is the
identity on N. Composition is written in ordinary functional order below.

For an entity x and an arrow h, write h*x for transport. For a relation F,
write F_h for its extension at h. An admitted entity is pinned by a finite
set S of individuals: arrows with the same source and target agreeing on S
transport that entity identically. Every entity has such an S. Profiles
which satisfy finite pinning and the target-symmetry condition are admitted
in these symmetric ideally-full domains.

We use three established facts of the exact construction:

1. Every colour-compatible finite prescription extends to an allowed
   globally surjective map. At A there is no colour restriction.
2. Every type transport is surjective. Consequently the universal relation
   at any relational type has an exact-image profile and is rigid.
3. If F is weakly rigid at A, then it has an exact-image profile:
   `F_h = {h*x : x in F_id}` (with tuples in general). This is the proved
   finite-pinning/root-factorization argument, not an additional premise.

An exact-image profile is rigid at every world. We also use the defining
test for weak inextensibility: if each actual member necessarily satisfies
an admitted test Z, then the whole profile entails Z.

## 3. Unary relations that lose their labels at C

For each n in N define a unary entity d_n at B by

    (d_n)_h = {h(n)}       if h:B->B,
    (d_n)_h = N            if h:B->C.

This is an admitted entity. It is pinned by {n}: agreeing on n makes the
whole transported profile identical. Its symmetry condition is immediate:
a target symmetry sends the singleton {h(n)} to its corresponding singleton,
and sends N to N. No additional arrow or domain element is postulated.

The following are equalities of entire entities, not just their present
extensions:

    h*d_n = d_(h(n))       for h:B->B;
    h*d_n = top_r at C     for h:B->C.

For the first, test both sides at every further B- or C-target arrow. For
the second, every further target is C and every extension is N. The d_n
are distinct at B because their identity extensions are the distinct
singletons {n}. Each d_n is not even weakly rigid: its sole current member
n necessarily satisfies the individual haecceity of n, whereas at C the
whole infinite extension of d_n is not contained in that transported
singleton. This refutes weak inextensibility.

## 4. A genuinely rigid infinite family at B

Define L, of relation type s=(et)t, at B by

    L_h = {d_n : n in E}       if h:B->B,
    L_h = {top_r at C}         if h:B->C.

The profile is pinned by the empty set: it depends on the target, not on
the incoming arrow. It satisfies the target-symmetry condition, since
symmetries at B preserve E and transport d_n to d_(g(n)); at C they fix
top_r. Thus L is an admitted family.

First L is weakly rigid at B. Weak persistence follows from the two
transport identities above and colour preservation. For weak
inextensibility, let Z be any admitted family such that every actual
L-member necessarily satisfies Z, and let finite N pin Z.

For a B-target arrow h and an arbitrary d_n in L_h, choose an even
m outside N. Finite interpolation supplies an allowed j:B->B agreeing
with h on N and sending m to n. The test assumption gives
`d_n = j*d_m in Z_j`; pinning gives `Z_j = Z_h`, so d_n belongs to Z_h.
For a C-target arrow h, the single member top_r equals h*d_0, and the
same test assumption directly puts it in Z_h. These exhaust all possible
targets, proving L entails Z.

For full rigidity, every B-endomorphism transports L to L itself. Every
B->C arrow transports L to the haecceity of top_r at C. The latter has
an exact-image profile, since top_r transports to top_r along every
C-endomorphism, and hence is rigid. Thus every future transport of L is
weakly rigid: **L is rigid at B**.

There is no conflict with the unary classification. L has infinitely many
members of type et, all nonrigid, and its union need not be rigid. The
rigid-family union lemma requires its members to be rigid.

## 5. No weakly rigid root family lifts L

Suppose, for a contradiction, that Z of type s is weakly rigid at A and
`i*Z = L`. Choose a finite pinning set N for Z and an even n outside N.
By the exact-image theorem at A, d_n in L has the form `i*x` for some
actual member x of Z. Choose a finite pinning set S for x, enlarged to
include N.

Choose distinct fresh odd numbers for the finitely many points of S\N,
all outside N. Prescribe a root endomorphism u to fix N and send each
point of S\N to its assigned odd number. Extend the prescription to an
allowed surjection u:A->A. Thus u is injective on S, fixes N, and

    u(S) intersect E = N intersect E.

Since u fixes N, pinning gives `u*Z = Z`. Weak persistence of Z implies
that u*x is again an actual member of Z. Transporting it along i gives
an actual member of L, so

    i*(u*x) = d_c

for some even c.

We claim c belongs to u(S). If it did not, choose an even d different
from c. Finite interpolation gives a B-endomorphism g fixing u(S)
pointwise and sending c to d. The two arrows `g i u` and `i u` agree on
S, so pinning of x gives

    d_d = g*d_c = (g i u)*x = (i u)*x = d_c.

This contradicts the distinct identity extensions of d_d and d_c.
Therefore c belongs to u(S), and the displayed colour identity implies
`c in N intersect E`.

Now prescribe v on u(S) by `v(u(s)) = s` for s in S. This is well-defined
because u is injective on S. It is colour-compatible: the only coloured
points in u(S) are members of N, on which both u and this inverse are
the identity. Extend it to an allowed surjection v:B->B. In particular,
v fixes N and hence fixes c.

The arrows `v i u` and i agree on S. Pinning of x and the transport
identities for d therefore give

    d_n = i*x = (v i u)*x = v*d_c = d_(v(c)) = d_c.

Injectivity of n->d_n gives n=c, contradicting n outside N and c in N.
This proves that **L has no weakly rigid root lift**, and in particular
no rigid root lift.

This argument uses finite support only to move the support of one chosen
member x while fixing the support of the family Z. It never bounds the
number of members of either family.

## 6. The explicit failure of RP at (et)t

Let G=top_s at A, the universal family of unary relations. By all-type
surjectivity, G is rigid. Its rigid-power property is the admitted
object-language relation

    Q(Y) := Rigid(Y) and Y <= G,             of type st.

At B, i*G is universal and the rigid family L satisfies this predicate.
Thus L belongs to Q_i.

If Q were weakly rigid at A, the exact-image theorem there would give
an actual Q-member Z with `i*Z=L`. But an actual Q-member is a rigid
family Z, hence weakly rigid, contradicting section 5. Therefore Q is
not weakly rigid and so not rigid. The rigid G witnesses the failure
of **RP_s**, exactly at the requested next property type.

In particular this model cannot satisfy the full RP schema. By the
ordinary C lowering proof `RP_(tau t) => RP_tau` in the earlier note
section 17, failure also propagates along every further iteration of
the property-type constructor above s. No claim is made about every
other admitted relational type.
