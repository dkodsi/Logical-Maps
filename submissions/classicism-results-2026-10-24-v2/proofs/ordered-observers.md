# Boolean separation without quantifier separation

Original mathematical argument, direct source misc; unpaginated.

1. RESULT AND EXACT OPERATOR CLASSES

Bool*(O) requires identity between the composite operations preserving
top, bottom, negation, conjunction and disjunction. For example,

  (lambda p,q. O(p AND q)) = (lambda p,q. Op AND Oq).

Q*_sigma(O) is the composite identity

  (lambda F:sigma t. O(forall x:sigma Fx))
    = (lambda F:sigma t. forall x:sigma O(Fx)).

For fixed X put S_X := forall p,q [p=q IFF forall O(X(O)->O(p IFF q))].
Write S_B for X=Bool* and S_BQe for X=Bool* AND Q*_e. Existential
commutation follows from the universal law and the Boolean identities.
All claims below also give the corresponding pointwise-identity versions.

There is a C model, evaluated at its ordered object A, satisfying

  C5 + BOX BF(all types) + BOX Atomlessness + BOX S_B + NOT S_BQe.   (1)

The failure includes the displayed composite-operation qualification.

At its other object B, full Boolean/quantifier separation holds for every
finite list of types. Hence the model also witnesses failure of persistence
of that stronger separation within an everywhere atomless C5 model.

The substantive distinction in (1) is not a failure of BF, of Boolean
separation, or of their necessary versions. Quantifier preservation imposes
an additional demand on which Boolean tests can be admitted.

2. CONSTRUCTION AND MODEL-THEORETIC BACKGROUND

Use the symmetric ideally-full construction of Dorr, Definitions 15-18,
p.8, with its C soundness theorem, Proposition 20. These definitions and
their use are recorded in groups/symmetric-ideally-full.yaml and
writeups/symmetric-old-new-individuals.md. Specify the base as follows.

Objects A and B are two copies of Q. Every bijection between each ordered
pair of these underlying sets is an arrow. Composition is composition of
functions. Both ideals consist of the finite sets. At A the designated
symmetry group is G_A=Aut(Q,<); at B it is the trivial group. All signature
constants, if included, have the top interpretation.

The base is a small groupoid of sets; its designated groups are subgroups
of the respective loop groups, and finite ideals are stable under these
bijections. It therefore supplies the data for the cited symmetric
ideally-full construction. Individuals are the underlying sets. A
relational intension consists of tuples (abar,h), with arguments at the
target of h, is symmetric under simultaneous transport by a target
symmetry, and is pinned by a finite subset of the source. Pinning means
that its membership at parallel h,h' agrees whenever h,h' agree on that
finite set, with the same target arguments supplied.

In particular propositions at W are finitely pinned sets of outgoing
arrows satisfying

  h in p iff g h in p  (g in G_target(h)).

The higher domains are exactly the symmetric finitely pinned intensions,
not arbitrarily enlarged function spaces. Sections 3 and 5 verify those
conditions for the operators used here.

Every arrow is invertible, so its action at every type is a bijection.
Thus C5 and necessary BF at every type hold. In particular, at an object V,
for any admitted F:sigma t, its quantified proposition is respectively
the intersection or union of F(a) over current a in D_sigma(V). This follows
from bijective transport, and does not assert arbitrary Boolean completeness
of the restricted proposition domain.

Atomlessness holds at both objects. Given nonempty p pinned by S, choose
h in p and distinct a,b outside S. If h ends at A, interchange the names
a,b if necessary so h(a)<h(b), and intersect p with

  r={k ending at A: k(a)<k(b)}.

This r is symmetric and finitely pinned. It contains h but not h composed
with the transposition of a,b. The latter arrow still belongs to p because
it agrees with h on S. Thus p AND r is a nonempty proper part of p. If h
ends at B, use the same construction with any fixed external ordering of B;
there is no target symmetry restriction there. This works at either source
object and proves BOX Atomlessness, hence absence of Actuality throughout.

3. BOOLEAN SEPARATION FROM EXTREME AMENABILITY

The external theorem used here is that Aut(Q,<), with pointwise-convergence
topology, is extremely amenable: each continuous action on a nonempty
compact Hausdorff space has a fixed point. Its finite point stabilizers
are finite products of copies of Aut(Q,<), one on each interval cut out
by the fixed points. They too are extremely amenable. For the finite-product
step, take the compact nonempty fixed-point set of one factor and repeat
with the commuting remaining factors. The trivial group at B has the same
fixed-point property.

Here is the admitted-operator argument, including the pinning obligation.
It applies to any model of this form in which every finite point stabilizer
of every designated symmetry group is extremely amenable.

Fix a source W and nonzero proposition r at W, pinned by finite S. Let
H=G_W,(S) be the pointwise stabilizer of S. H fixes r under proposition
transport. Let A_V be the Boolean algebra of admitted propositions at V.
The induced action of each symmetry subgroup on Stone(A_V) is continuous:
each proposition is fixed by an open finite point stabilizer, so its clopen
set of ultrafilters has an open stabilizer. These clopens form a basis.

The nonempty clopen [r] in Stone(A_W) is H-invariant. Extreme amenability
therefore provides an H-invariant ultrafilter U containing r.

For each target V, consider all injections f:S->V and the action of G_V
on them by postcomposition. For each orbit choose a representative f and
an ultrafilter U_f on A_V invariant under the stabilizer G_V,(f(S)). Such
an ultrafilter exists by extreme amenability of that stabilizer. For the
orbit of the inclusion S->W use the U just obtained. Extend the choices
equivariantly by U_(g f)=g_* U_f, where

  p in g_* U iff rho_t(g^-1)(p) in U.

This is well defined because U_f is invariant under the stabilizer of f.
These are choices in the ordinary ZFC metatheory, not asserted object-level
choice functions.

Define the intension E at type tt by

  (p,h) belongs to E iff p belongs to U_(h|S),

for h:W->V and p in D_t(V). Parallel arrows agreeing on S give the same
ultrafilter, so S pins E. If g is a target symmetry, equivariance gives

  p in U_(h|S) iff rho_t(g)(p) in U_((g h)|S).

Thus E is symmetric and belongs to the admitted tt domain.

At any future h:W->V, for current input p at V, its output proposition is

  (rho_tt(h) E)(p)
    = {k:V->Z : rho_t(k)(p) belongs to U_((k h)|S)}.

At each k this is evaluation by a Boolean ultrafilter after Boolean
transport. Consequently the displayed operation preserves every Boolean
connective and both constants as identity propositions. This holds for
all inputs at every future h, establishing the composite identities Bool*.
At the identity of W, E(r) is true since r belongs to U; E(bottom) is false.

Given unequal p,q take their nonzero Boolean symmetric difference r. The
constructed E has E(r) true, hence distinguishes p and q. This proves S_B
at every object and therefore BOX S_B in the specified two-object model.
In particular the ultrafilter construction yields admitted intensional
operators; external ultrafilters alone would not have sufficed.

4. QUANTIFIER SEPARATION FAILS AT A

Let d be all arrows A->B. It is an admitted nonzero proposition, pinned
by the empty set. Suppose E satisfies the Boolean and existential composite identities,
and E(d) is true. Let finite S pin E.

For every g in G_A fixing S, pinning gives rho_tt(g)E=E. Symmetry of
every output proposition gives v(rho_t(g)z)=v(z), where v is truth at A.
Application coherence therefore gives

  v(E(rho_t(g)p))=v(Ep).                                      (2)

For each n in B define the admitted property P_n by the intension

  (x,h) belongs to P_n iff target(h)=B and x=n.

This is pinned by the empty set. Its A-target part is empty and its
B-target part has trivial symmetry, so it is symmetric. For current x in A,

  P_n(x)={h:A->B : h(x)=n},
  exists x P_n(x)=d.

Commutation with exists_e and E(d) therefore yield some x_n in A such that
E(P_n(x_n)) is true. For a fixed n it is unique: if x!=y, the propositions
P_n(x) and P_n(y) are disjoint, and Boolean preservation precludes accepting
both. Different n give different x_n for the same reason.

Transport satisfies rho_t(g)P_n(x)=P_n(g(x)). Equation (2) and uniqueness
therefore make x_n fixed by every member of G_A fixing S. In Aut(Q,<) the
only such fixed points are the points of S: any rational outside S can be
moved within its interval by an order automorphism fixing S. Hence every
x_n belongs to S. Distinct n then inject the infinite B into the finite S,
a contradiction. Equivalently take |S|+1 distinct labels; no infinitary
object formula is used.

Thus every such E rejects d, just as it rejects bottom. Every full Boolean
operator commuting with forall_e also commutes with exists_e, and so fails
to distinguish d from bottom. In the input-biconditional formulation,
all such operators accept (d IFF bottom)=NOT d although d!=bottom. S_BQe
fails. This proof uses no involutions in the designated group and no
Actuality or endpoint-valued evaluator.

5. FULL QUANTIFIER SEPARATION AT B

An explicit construction suffices here. Choose arrows k_V:V->T_V for each
object V such that

  k_V G_V k_V^-1 is contained in G_(T_V).

Define a tt intension E at source W by

  (p,h) belongs to E iff k_target(h) belongs to p.

It is pinned by the empty set. The subgroup condition makes it symmetric:
membership of k_V in rho_t(g)p is membership of k_V g in p, which equals
membership of k_V by symmetry at T_V. At future h:W->V its output on p is

  {a:V->Z : k_Z a belongs to p}.

This inverse-image map preserves Boolean operations and, by the groupoid
quantifier formulas in section 2, every admitted quantified intersection
and union. The laws hold at every future input, so the full composite
identities hold.

Now W=B. For any desired arrow b:B->T choose k_B=b and k_A=id_A. The
subgroup condition holds because G_B is trivial. The resulting observer
accepts p at B exactly when b belongs to p. Any difference between p and q
has such a witness b, giving full Boolean/quantifier separation at B, for
each finite type list. Section 4 shows it is not necessary there.

SOURCES

New application, operator constructions and obstruction: misc, sections 1-6
of this note, unpaginated. Model framework: Cian Dorr, Boolean Completeness
does not imply Rigid Comprehension, draft of 30 July 2026, Definitions 15-18,
p.8; Proposition 20, as recorded in the local construction write-ups.
These locators do not attribute the present ordered/unrestricted-role model
or its observer verdicts to that draft.

External fixed-point theorem: A. S. Kechris, V. G. Pestov, S. Todorcevic,
Fraisse Limits, Ramsey Theory, and Topological Dynamics of Automorphism
Groups, arXiv:math/0305241v4, Theorem 6.5 (Pestov), printed p.30; definition
of extreme amenability in section 0(A), p.1. Directly checked online:
https://arxiv.org/pdf/math/0305241v4 .
