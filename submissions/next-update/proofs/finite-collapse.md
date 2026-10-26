# The finite-collapse principle for represented mathematics under Max

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. The simplest statement

> **Operations under Max must survive a simultaneous finite collapse.**
> The collapse preserves their actual input–output identities and every
> necessary distinction. Each fixed type has a fixed finite capacity.

For freely represented algebraic operations, this necessary condition is
also sufficient. It applies to many sorts and to proposition-valued
readouts, not just to one carrier with operations returning to that carrier.

The capacities are


$$
c_e=1,\qquad c_t=2,\qquad c_{\alpha\rho}=c_\rho^{c_\alpha}.
\tag{1}
$$


They are the sizes of the full one-world C hierarchy with one individual.
For example, c_et=2 and c_tt=4. All these numbers are finite in the
metatheory. This is not a claim that actual type domains are finite.

The key qualification is **input–output identities**. Merely having an
ordinary graph with the right current truth conditions does not satisfy
the premise. This is why the principle can forbid familiar operations
while leaving all ordinary current relational mathematics available.

## 2. Exact many-sorted theorem

Work in the external ZFC metatheory. Let A be a set-sized finitary
many-sorted algebra. Assign each sort s a fixed admitted type τ_s, using
at most one carrier A_s per type. Each A_s is nonempty. The set of basic
operations can be infinite, but each has finite arity. Every positive-arity
operation has the form


$$
f:A_{s_1}\times\cdots\times A_{s_k}\longrightarrow A_r,
\qquad \tau_r\ne e.
$$


Nullary operations are allowed as designated constants at any sort. A sort at e may
be used for inputs and designated objects; there are no positive-arity
e-valued operation representatives in the fixed language. Choose any
set P_s of pairs of distinct elements of A_s to be protected.

An **operational realization** injects each A_s into the current
τ_s-domain and represents every basic operation by an admitted ambient
operation having the stipulated values as literal object identities.
Protection means $\Box(\widehat a\ne\widehat b)$ for each prescribed
pair. The represented carriers need not be rigid, persistent, or even
extensions of admitted domain predicates. No universal algebra law is
required to hold necessarily.

**Theorem.** The following are equivalent:

1. A has such an operational realization in some model of C + pure Max,
   protecting every pair in P_s.
2. There is one many-sorted quotient q:A→B, surjective on each sort,
   preserving all basic operations, such that

   
$$
|B_s|\le c_{\tau_s},\qquad
   q_s(a)\ne q_s(b)\quad\text{for every }(a,b)\in P_s.
   \tag{2}
$$


Necessity holds for every operational realization in every Max model.
The converse constructs a realization in some Max model. In fact it can
make the necessarily distinct pairs **exactly** those separated by q.

The operation symbols in this equivalence are freely represented
parameters, not preassigned logical operations or pure C terms. Section 5
gives the precise extension to literal bottom/top readouts and explains
the limitation for fixed operations. The theorem concerns pure Max;
the algebra parameters are not added to the reference language of Max.

Equivalently, there must be a many-sorted congruence with at most c_τ
classes at type τ, identifying no protected pair. This is a common
quotient for the whole operation package, not a separate quotient for
each operation or each marked pair.

**Partial-table version.** The same equivalence holds when only selected
input–output values are prescribed. Condition (2) then means that the
quotient admits total operation tables satisfying all those prescriptions.
Unspecified cells may take default values. This covers an inverse required
only on an image, without imposing equations or range restrictions
elsewhere.

## 3. Necessity: joint possibilities and compactness

Introduce an ordinary many-sorted first-order language with the basic
operation symbols and constants d_a for every a∈A_s. Form its theory T:

- every operation-table equation
  $f(d_{a_1},\ldots,d_{a_k})=d_{f(a_1,\ldots,a_k)}$;
- $d_a\ne d_b$ for each protected pair;
- a sentence bounding each whole sort by c_τ_s elements.

Every finite subset T₀ is satisfiable. To see this, let S₀ be the finite
set of sorts appearing in T₀. The **single** pure sentence


$$
\bigwedge_{s\in S_0}\mathrm{AtMost}_{c_{\tau_s}}(\tau_s)
\tag{3}
$$


holds in the one-world singleton-individual full C model. Pure Max
therefore supplies the possibility of (3). We do not infer a joint
possibility from separate possibilities.

If T₀ were inconsistent, first-order equality logic would give a finite
refutation of its diagram and bounds. Interpret each function symbol by
its admitted operation and each constant by its current represented
object. NI makes every stipulated current operation equation necessary;
the marked inequalities are necessary by hypothesis. Necessitating the
logical finite refutation would make the negation of (3) necessary,
contradicting its Max possibility.

First-order compactness now gives a model of T. Sending a to d_a in this
model preserves all operations. Its sortwise image is the required
bounded quotient B. This is external compactness, not an admitted
internal quotient map or an infinitary object-language inference.

For partial tables, any two prescribed cells with the same quotient
input tuple have the same quotient output, because the first-order model
interprets a function. Use that output on such a tuple and a fixed default
elsewhere. Thus totalizing does not require the first-order function's
unspecified outputs to lie in the named image.

Taking P_s to include **all** necessarily distinct current pairs gives
a particularly useful form: each kernel class consists of pairs which
can coincide. The result does not claim a single possibility realizing
every identification of an infinite kernel at once.

If no such quotient exists, compactness also supplies a finite obstruction:
finitely many current operation identities, finitely many protected
distinctions, and one finite conjunction of type bounds already conflict.
Consequently the negative application has a finite proof in the original
language. No infinite conjunction of actual or necessary laws is needed.

## 4. Sufficiency, including the previously excluded base type t

Assume q satisfies (2). Use the established free-current coalescence
construction with one Henkin C component M_i witnessing each C-consistent
closed pure sentence. There is at least one such component. This supplies
all the pure-Max possibilities at the new root.

### 4.1 Quotient behavior in the Max-witness components

In each M_i, choose a necessarily distinct family of |B_s| objects
$u^i_{s,b}$ at each type τ_s. C supplies families of the required sizes
by the [finite-core theorem](finite-type-capacities.md#3-the-bound-is-sharp-already-in-c).
At e the family has just one member.

For each operation f of the quotient, finite equality case distinction
gives an admitted operation on the selected cores. At arguments
$u^i_{s_1,b_1},\ldots,u^i_{s_k,b_k}$, its result is literally
$u^i_{r,f^B(b_1,\ldots,b_k)}$.

Explicitly, after flattening the output type as
$\tau_r=\rho_1\cdots\rho_l t$, use


$$
G_f(\bar x)[\bar z]
=\bigvee_{\bar b\in B_{s_1}\times\cdots\times B_{s_k}}
 \left(\bigwedge_j x_j=u^i_{s_j,b_j}\right)
 \land u^i_{r,f^B(\bar b)}[\bar z].                         \tag{4}
$$


The empty argument tuple l=0 is allowed, so this formula includes
propositional outputs. At selected inputs the matching equalities are
necessary and every nonmatching case is necessarily false. C's
Intensionality yields the whole output identity. This is not an illicit
use of Logical Equivalence under optional premises. Nullary cases are
the designated core object itself.

### 4.2 One extra S5 component separates the original elements

Add one **separating component** H: a full standard S5 C model with
individuals E and worlds W large enough for all the A_s. Its propositional
carrier is P(W), and its function carriers are full function sets.
Every relational carrier contains at least |P(W)| objects, using constant
functions repeatedly. Choose sortwise injections


$$
j_s:A_s\hookrightarrow D_{\tau_s}^{H}.
$$


For every basic operation, prescribe its value on the injected input
tuples to be the injected output, and extend it arbitrarily elsewhere.
Full function domains contain the resulting curried ambient operation.
Every such operation equation is a literal identity in H. All distinct
injected objects are necessarily distinct, because this S5 model uses
ordinary set identity at every world.

Unlike the quotient components, H remembers the entire original algebra.
It is a C component; it need not itself satisfy Max. Adding it leaves
the original pure-Max witnesses in place.

### 4.3 Assemble the whole root objects and operations

For a relational sort, choose a current extension S_a and encode


$$
\widehat a=
\left(S_a,\ (u^i_{s,q_s(a)})_i,\ j_s(a)\right).
\tag{5}
$$


These root objects are distinct because their H-coordinates are
distinct. Their current extensions need not be distinct. In particular,
when τ_s=t, each S_a is only one truth bit; this causes no obstruction.
The extra coordinate supplies injectivity even at base type t.

For the optional e-sort, use different root individuals for A_e. Map all
of them to its single quotient-core point in each M_i, and map them by
j_e in H. The free-current construction allows these arbitrary individual
projection maps; they need not be surjective.

Give each root operation the component operations just constructed.
Choose its current profile so that, on the encoded input tuples, its
output profile is S_f(a₁,…,a_k). This is well-defined because the
encodings are injective. The root's full current profile domain permits
the prescription, extended arbitrarily off those tuples. Thus application
has the desired current extension, every desired quotient coordinate,
and the desired H-coordinate. It equals the entire encoded output,
not merely its current extension. All operations are handled
simultaneously in this same model.

If q_s(a)≠q_s(b), the objects are distinct currently and necessarily
distinct in every component, so they are necessarily distinct at the
root. If a≠b but q_s(a)=q_s(b), their equality is top in every M_i.
It is therefore possible at the root, even though H keeps the two
objects distinct. This verifies the claimed exact protection pattern.

All constructions are set-sized in the metatheory. C validity follows
from the established coordinatewise coalescence argument: logical
operations, quantifiers and lambda abstraction use the full local
component domains; Logical Equivalence uses its actual H-theorem
certificate. No ordinary full-function or extensionality axiom is added
to the root theory.

The positive construction may also have both current quantified
Infinity_e and Infinity_t. Take the root individual set and W infinite.
The S5 propositional coordinate P(W) makes the root proposition carrier
infinite; constant functions and the product coordinates likewise make
every other relational root carrier infinite. The current profile domains
are full, so the Frege numerical core at each counting type is the external
finite successor orbit: that orbit itself is an admitted current inductive
extension, and every current inductive extension contains it by ordinary
external induction. Neither infinite carrier is exhausted by one of
those finite cardinalities.
This does not assert the boxed Infinity axioms, which the finite
Max-witness components would prevent.

## 5. Logical anchors and the limit of the converse

**Actual false and true readouts are included.** Suppose a t-sort contains
designated 0 and 1 that must denote the literal logical ⊥ and ⊤, and
q_t separates them. Since c_t=2, label its quotient values 0,1 accordingly.
In every M_i use the actual ⊥,⊤ core; in H choose
j_t(0)=∅ and j_t(1)=W. Give their root profiles the truth bits 0 and 1.
Equation (5) then makes the two encoded objects the literal root ⊥ and ⊤.
All readout equations into these anchors remain whole-object equations.

The same anchoring is available at other relational types if the
quotient separates prescribed literal bottom and top. The c_τ-sized
necessarily distinct family can be chosen to contain both: in the finite
truth-table construction retain bottom and replace the all-ones table
by literal top; the selected test tuples still distinguish it from every
other table. Choose the corresponding anchors in H and their exact
current root extensions.

For a **fixed two-element truth sort**, its Boolean operations may also
be the actual logical Boolean operations: their tables agree in all
components and at the root. In particular the theorem covers ordinary
Boolean readouts rather than two arbitrary labels named “false” and “true.”

For additional preassigned operations, the unrestricted converse is not
claimed. Application, quantification, a pure Frege successor, or Boolean
operations on a larger proposition algebra have their own fixed
interpretations. The finite quotient and the separating component must
respect those interpretations, and their root profiles are then not
free to prescribe. A many-sorted operation called “evaluation” cannot
silently be substituted for built-in application. Similarly, the positive
model is a copy of an abstract algebra; it is not automatically the
canonical Frege numerical core.

The **necessary** bounded-quotient condition remains valid for any
preassigned operation whenever the required current input–output
identities hold. Fixed C-theorems and literal anchors can impose further
constraints. Current truth of an arbitrary relation, without a whole
propositional identity or a necessity premise, is not one of the
transported constraints.

## 6. What the theorem unifies

**Field corollary.** Every field operationally represented at a fixed
relational type, with necessarily distinct zero and one, has at most
c_τ elements. In particular no infinite field, including the rationals,
reals or complex numbers, has such an operational representation.

Indeed apply the theorem to its additive and multiplicative operations
and the protected pair (0,1). The resulting bounded ring quotient has
distinct zero and one. Its kernel is a proper ideal of the original
field, hence zero, so the quotient map is injective. Equivalently, if a
nonzero x entered the kernel, applying the map to x times its existing
field inverse would identify one with zero. The argument needs only the
represented ring operations; it does not require an operation selecting
inverses. This corollary concerns literal input–output identities.
Ordinary relational presentations of these fields are not excluded.

Pairing, stacks and shifts fail for one reason: their operation identities
and protected outputs cannot survive the required finite collapse.
For pairing with both projections, a finite quotient Q would need an
injection Q²→Q while retaining two distinct elements. For a Boolean
stack, finite push/pop recovery and the anchored readout cannot coexist.
For a surjective operation, its finite quotient must be a permutation;
the original operation therefore cannot have a fibre containing a
protected pair. The individual notes
give direct finite proofs of these special obstructions.

The point is not merely that Max needs “some finite model.” The same
small quotient must carry **all** represented operations together,
separate **all** protected pairs, and obey the exact capacity of each
type. Moving an encoding to a different type may change the finite
capacity, but no fixed type has infinite capacity. Conversely, if that
joint algebraic test succeeds for freely represented operations, the
construction above supplies a Max realization, including at base t.

This is a representation theorem about actual operations and possible
identifications, not an inconsistency proof for Max or a failure of
ordinary current relational mathematics.

## Sources and relationship to prior notes

- [Stable-domain bound](finite-type-capacities.md),
  §§1–3: the singleton-model capacities and necessarily distinct cores.
- [Current analysis](current-analysis-under-max.md),
  construction section, and [Frege arithmetic](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md),
  §§37.4–37.5: free-current coalescence, arbitrary individual projections,
  component quantifiers, C validity, and the pure-Max witnesses.
- [Pairing](pairing-and-readouts.md), §§1–2, and
  [stacks and shifts](stacks-shifts-and-algebra.md), §§1–3: the examples now
  subsumed by the joint finite-collapse principle.
