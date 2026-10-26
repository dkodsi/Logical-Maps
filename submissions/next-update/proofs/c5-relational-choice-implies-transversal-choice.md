# C5 and Relational Choice imply Transversal Choice

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Direct
source: `misc`, this note, unpaginated. No compilation or database edit.

## 1. The proved C5 consequence

The argument below proves the restricted theorem


$$
\boxed{C5+\mathrm{RC}_{(\sigma t),\sigma}
       \ \Longrightarrow\ \mathrm{TC}_{\sigma}.}
$$


The all-type consequence is C5+RC⇒TC. The C5 premise is essential to the
proof presently given; it is not being inferred from RC. The root research
agent and a separate construction agent independently reviewed §§2–4 and
accepted the ordinary proof. This is neither a Lean certificate nor a
claim of novelty in the literature.

The construction has two distinct ingredients. RC supplies a property-valued
operation that extends strict partial transversals and adds an actual point
whenever an actual cell is missed. C5 lets a canonical-chain construction
use only rigid families, whose material unions are genuine algebraic joins.
No BC or Zorn is assumed.

## 2. Strict local sections and an admitted progressive operation

Fix an actual equivalence R on σ and put ρ=σt. Use the admitted uniform
equivalence Q_R and saturation S from Appendix A below. In particular Q_R agrees actually with R, and C proves the literal
closure identities for S. Let


$$
P(B):=\bigl(\lambda A^\rho.\,B\land S(B\land A)\bigr)
       =\bigl(\lambda A^\rho.\,B\land A\bigr).
$$


This is a single identity of admitted operations. It implies the
output-equality locality predicate of the bridge. Conversely, C5
Functionality turns all those output equalities into P(B). In particular
P(0), and each singleton is in P.

Use the unconditional strict-local normalization


$$
N(D)(x):=Dx\land\forall y\,[(Dy\land Q_R(x,y))\to y=x].
$$


The uniform H proof of uniqueness and Logical Equivalence prove P(N(D))
for every D. If D has an actual singleton extension, N(D)≈D actually.

Write Full(B):=∀x S(B)(x). The relation


$$
U(B,a):=\mathrm{Full}(B)\lor\neg S(B)(a)
$$


is actually serial. The standing types are nonempty; when Full(B) fails,
ordinary quantifier duality supplies a missed point. RC at (ρ,σ) therefore
gives an actual functional subrelation K⊆U, total at every B. Put


$$
K_B:=\lambda x.K(B,x),\qquad
f(B):=B\lor\bigl(N(K_B)\land\neg S(B)\bigr).
\tag{1}
$$


This is an admitted operation ρ→ρ, even when σ=e. No individual-valued
operation is introduced, and f is not identified with a selected property
code by extensionality.

**Progress and locality.** For every B, B≤f(B) is a literal Boolean identity.
If P(B), put D=N(K_B)∧¬SB. Locality is hereditary, so D is local. Moreover
SD≤¬SB: the complement of an S-fixed property is S-fixed, by the uniform
equivalence properties of Q_R. Thus B and D have disjoint saturation
ceilings. Expanding


$$
(B\lor D)\land S((B\lor D)\land A)
$$


into four terms kills the two cross terms; the diagonal terms are B∧A and
D∧A. Consequently f(B) is local. C5 Functionality packages the output
identities as P(f(B)). This is finite Boolean algebra with the literal
saturation identities.

**Actual strictness.** If Full(B) fails, let a be the unique actual K-output
at B. Then ¬SB(a), and K_B has actual extension {a}. Hence N(K_B)(a), so
f(B)(a), whereas ¬B(a) since B≤SB. Therefore f(B)≠B. This proof uses only
actual functionality and containment of K. Neither is boxed.

It remains to prove that f has a fixed point in P. At such a point actual
strictness gives Full(B), and locality gives a transversal of R.

## 3. The C5 crisp fragment and its chain suprema

Use C5 only in this section and its sequel. Identity propositions at every
type are endpoint-valued: NI handles true identities and ND handles false
identities. C5 also supplies BF, CBF, and Functionality at the relevant
types. Consequently a formula constructed from identities by Boolean
connectives and object quantifiers is rigid. Parameters may be arbitrary
admitted entities, including f and K; there is no requirement that the
truth of K(B,a) itself be rigid.

For any family code X:ρt define crisp membership


$$
\widehat X(B):=\Box(XB)=(XB=\top).
$$


Its values are endpoints under C5. We also call a family rigid when all its
membership values are endpoints. Rigid families are closed under Boolean
combinations and quantification over admitted indices. In particular a
formula entirely in identities represents a rigid family. If X is rigid,
then X and its crisp version have the same values.

The order B≤D is the identity B∨D=D. Thus P, the order, strict order,
equality of f-values, and Boolean combinations and quantifications of those
predicates belong to this crisp fragment.

**Rigid-chain join lemma.** Let X be an admitted rigid family whose current
members lie in P and are comparable in ≤. Then


$$
J_X(x):=\exists B\,[XB\land Bx]
\tag{2}
$$


is their genuine algebraic least upper bound and belongs to P.

For a current X-member B the coefficient XB is Top, so B≤J_X. If Z bounds
every current X-member, then for every B the property XB∧B is ≤Z: its
coefficient is either Bottom, or Top with B≤Z. BF at the index type moves
the necessary pointwise bounds through the universal quantifier. Therefore
the displayed existential union is ≤Z. This proves the LUB claim and
includes the empty current family, whose union is Bottom.

For locality, current members B,D have local union because the smaller is
below the larger. Hence for every A their cross term


$$
B\land S(D\land A)
$$


is below A. Expand the local expression for J_X using S's existential-union
law and fixed-meet distributivity. A term with a zero coefficient vanishes;
every remaining term is one of these bounded cross terms. BF again permits
the universal algebraic bound to pass to the existential union. This gives
J_X∧S(J_X∧A)≤J_X∧A; the reverse bound is saturation's unit. Functionality
then gives P(J_X).

No arbitrary current family has been rigidified here. The lemma applies
only to already rigid membership predicates; it does not assert BC.

## 4. Canonical chains need only crisp subfamilies

We give the fixed-point argument in detail to locate the required rigidity.
For a code X:ρt let its chain members be exactly the current objects B with
\widehat X(B). Call X an f-chain when:

1. These members lie in P and form an algebraic chain.
2. Every nonempty crisp subfamily \widehat Y contained in the members has
   a least member. Here Y ranges over all admitted ρt codes.
3. Every member b is the algebraic LUB in P of the represented family
   \{f(a):\widehat X(a) and a<b\}.

All three conditions are formulas using only identities. For example the
LUB clause uses ∀z[Pz→(b≤z↔∀a(\widehat X(a)∧a<b→f(a)≤z))]. Thus the
predicate Chain_f(X) is rigid under C5, even though K need not be rigid.
The singleton of Bottom is an f-chain.

**Comparison.** Any two f-chains are comparable by initial segment. For
chains X,Y, let I consist of common members b whose strict predecessor
families in X and Y have the same actual members. This is an identity-only
formula, hence a crisp family. The usual order argument makes I an initial
segment of both chains. If both differences are nonempty, each is a crisp
family and therefore has a least member, say b,c. Both have precisely I
as their predecessor family. Their represented f-images therefore have
the same current members, so their LUBs b,c are identical by algebraic
antisymmetry. This makes that common member belong to I, a contradiction.
Notice that no equality of coextensive chain codes is used.

Define the canonical union


$$
A(b):=\exists X\,[\mathrm{Chain}_f(X)\land\widehat X(b)].
\tag{3}
$$


This formula uses only identities, so A is a rigid family. Comparison makes
it a chain in P. It is well-ordered with respect to crisp subfamilies:
given a nonempty crisp Z⊆A, choose b∈Z and an f-chain X containing b;
the crisp intersection Z∩X has a least member c. Initial-segment comparison
with any chain containing another Z-member shows that c is globally least.
Every member's predecessor family in A is already its predecessor family
in a chain containing it. Hence the LUB clause transfers as well. Therefore
A, viewed through its identical crisp membership, is itself an f-chain.

By the rigid-chain join lemma, let u=J_A∈P be its algebraic LUB. If u∉A,
A has no greatest member. For every a∈A choose b∈A with a<b; conformity at
b gives f(a)≤b≤u. Conversely a≤f(a), so every bound of f[A] bounds A.
Thus u is also the LUB of f[A]. The rigid family A∪{u} is then an f-chain:
old predecessors are unchanged, the new predecessor family is A, and
crisp well-foundedness is preserved by appending a largest member. This
contradicts the definition of A. Consequently u∈A.

If u<f(u), the rigid family A∪{f(u)} is again an f-chain. At an old a<u,
conformity at u gives f(a)≤u≤f(u); the remaining image f(u) is the greatest
member of f[A]. Thus f(u) is the required new LUB. The resulting membership
f(u)∈A contradicts that u bounds A. Since u≤f(u), we obtain u=f(u).

This proves the C5 theorem. Crucially, arbitrary material subfamilies were not used
for well-foundedness. All auxiliary differences, intersections and
predecessor families needed in the argument are crisp, and therefore are
among the tested subfamilies.

## 5. Scope and the remaining bare-C question

The construction uses the unboxed RC instance only to ensure actual
strictness of f on nonfull local sections. It does not require a necessarily
functional selector, persistent choice, quotient objects, BC, Zorn, or a
wellordering of all admitted objects.

The C5 step presently has two roles: identities and their negations are
rigid, and quantifiers preserve that rigidity. This keeps Chain_f and its
canonical union rigid, so material unions become the algebraic joins
required by the fixed-point proof. Bare C supplies NI but not ND or BF at
all types; simply repeating §3 there would be invalid. Removing those uses
is the next mathematical question, not an established consequence of this
argument.



## Appendix A. Saturation and normalization in C

### A.1. An admitted equivalence closure gives literal saturation identities

Work in bare finitary C, at an arbitrary type σ, including e. Let
R:σσt be an actual equivalence relation. All displayed definitions are
ordinary finite lambda terms in the existing types. Write A≈B for actual
coextension of properties of σ.

Define the admitted relation


$$
Q_R(x,y):=\forall P^{\sigma\sigma t}
 \bigl[(\mathrm{Equiv}(P)\land R\subseteq P)\to P(x,y)\bigr],
\qquad
R\subseteq P:=\forall u,v\,(R(u,v)\to P(u,v)).
$$


Uniformly in R, H proves that Q_R is an equivalence relation: every P in the
intersection is reflexive, symmetric and transitive, and those three
properties pass to this intersection by ordinary predicate logic. H also
proves R⊆Q_R. If R is actually an equivalence, instantiate P with R to get
Q_R⊆R actually. Thus Q_R and R agree actually. No quotient type, witness
selection or optional-premise use of Logical Equivalence is involved.

Define saturation on properties by


$$
S(A)(x):=\exists y\,[Q_R(x,y)\land A(y)].
$$


The uniform H proof of equivalence gives unconditional pointwise H
equivalences for the usual saturation laws. Applying C's Logical Equivalence
only to those unconditional equivalences gives genuine property identities


$$
S0=0,\qquad S1=1,\qquad S(SA)=SA,\qquad
A\lor SA=SA,
$$


$$
S(A\lor B)=SA\lor SB,\qquad
S(A\land SB)=SA\land SB.
$$


The last law follows by expanding two witnesses and using symmetry and
transitivity of Q_R. Saturation also commutes with each admitted material
existential family union, by interchanging the two existential quantifiers.
These are genuine intensional identities, not merely statements on the
actual quotient algebra. The initial unboxed hypothesis on R is therefore
not by itself an obstruction to obtaining an admitted idempotent closure.

### A.2. Exact locality, including a strict normalization

Distinguish the following two predicates:


$$
\begin{aligned}
\mathrm{Loc}^{\approx}(B)
 &:=\forall A\,[B\land S(B\land A)\approx B\land A],\\
\mathrm{Loc}^{=}(B)
 &:=\forall A\,[B\land S(B\land A)=B\land A].
\end{aligned}
$$


The second has the literal output-equality shape of the observer locality
predicate. It is stronger than the first. We do not identify material
coextension with property identity.

**Locality lemma.** Loc≈(B) is equivalent to B being an actual partial
R-transversal: any two B-members related by R are identical.

For the forward implication, suppose Bx, By and Rxy, and use the admitted
singleton A(z):=(z=y). Then S(B∧A)(x) holds. Locality implies A(x), hence
x=y. Conversely, if B is partial, a witness y to S(B∧A)(x), with Bx, must
equal x; hence Ax. The reverse inclusion follows from reflexivity.

There is also an explicit admitted normalization:


$$
N(B)(x):=Bx\land\forall y\,[(By\land Q_R(x,y))\to y=x].
$$


H proves uniformly that N(B) is a partial Q_R-transversal. Indeed, if
N(B)(x), N(B)(y) and Q_R(x,y), the uniqueness clause at x gives y=x.
The proof of the locality lemma then gives unconditional H equivalences of
the two pointwise formulas for N(B), for every A. Logical Equivalence yields


$$
\mathrm{Loc}^{=}(N(B)).
$$


If B is actually a partial R-transversal, N(B)≈B actually. Thus strict
locality can be obtained without altering the actual extension of a partial
transversal. This uses no RC, C5, Actuality, BC or Zorn.

Consequently there is an exact bare-C reduction:


$$
\boxed{\mathrm{TC}(R)\quad\longleftrightarrow\quad
\exists B^{\sigma t}
 \bigl[\mathrm{Loc}^{=}(B)\land\forall x^{\sigma}\,S(B)(x)\bigr].}
$$


From a transversal T use N(T); it has the same actual extension and hence
the same actual coverage. Conversely strict locality implies material
locality, and material coverage supplies a member of each cell. This is a
closure reformulation, not a proof that the displayed witness exists.

The coverage clause is deliberately material. The stronger identity
S(B)=1 implies it, but is not asserted equivalent to actual TC(R).
