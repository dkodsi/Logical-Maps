# Models separating operator principles

Original mathematical argument, direct source misc; unpaginated.

1. BOOLEAN AND ALL QUANTIFIER COMMUTATION DO NOT SUPPLY EQUALITY

The following is a full-typed model of H and Booleanism, with Functionality
at every admitted arrow type. Every finite-list Boolean/quantifier separation
formula holds, but a specific Logical Equivalence instance of C fails.

Domains. Take a singleton D_e. Put D_t=2 x 2, and at each permitted arrow
sigma->tau take ALL functions D_sigma -> D_tau. No arrow ends in e.
Interpret application and abstraction in the ordinary set-function way.
Actual truth of (b,c) is b=1.

Logical operations. Interpret AND, OR, NOT coordinatewise using the ordinary
Boolean operations on 2. At every sigma, set

  forall_sigma(F) = (forall x pi_0(Fx), forall x pi_1(Fx)),
  exists_sigma(F) = (exists x pi_0(Fx), exists x pi_1(Fx)).

Each coordinate is a Boolean truth value, even for infinite domains.
The fixed closed top and bottom therefore denote (1,1) and (0,0).
Interpret the primitive equality at EVERY type by

  eq_sigma(x,y) = (delta_xy, 0),

where delta_xy=1 precisely when x,y are the same domain element.

H verification. Actual truth is classical for every connective. The first
coordinate of either quantifier has the ordinary truth condition over its
nonempty domain. Equality is true exactly for literal identity, so Ref and
LL hold. Ordinary full-function interpretation validates beta and eta
conversion, including their contextual instances. MP, Gen and Inst are
truth-preserving with their usual free-variable side conditions. This checks
all H clauses without any equivalence-to-identity rule.

Full Booleanism holds: coordinatewise evaluation makes any two Boolean-
equivalent propositional terms equal under each assignment; full
function spaces then make their lambda abstractions equal as functions.
Current Functionality also holds at every admitted arrow type because
pointwise identity of ordinary functions is literal function equality.
The Boolean quantifier laws and contextual order adjunctions also hold
coordinatewise. These facts do not repair the primitive equality values.

Separating operators. For i=0,1 let

  E_i(b,c) = (pi_i(b,c), pi_i(b,c)).

Fullness admits these two operators. They preserve all Boolean
primitives and both constants. For every sigma and F,

  E_i(forall_sigma F)
     = (forall x pi_i(Fx), forall x pi_i(Fx))
     = forall x E_i(Fx),

and the same calculation with exists proves existential commutation.
If p!=q, some coordinate differs; the corresponding E_i-images differ in
actual truth. The reverse implication of separation is substitution.
The SAME two operators work for every type, so every fixed finite Delta
is covered. This last semantic fact is not an infinitary object formula.

Failed C identity. For any x:sigma,

  eq_sigma(x,x)=(1,0) != (1,1)=top.

But x=x and top are H-provably equivalent. Thus the nullary Logical
Equivalence instance (x=x)=top fails. More explicitly, the CLOSED Identity
Identity fails: at x=x its left-side equality predicate returns (1,0),
whereas forall F(Fx IFF Fx) returns (1,1). The corresponding lambda functions
are different. Consequently even Booleanism plus full Functionality,
quantifier adjunction, and literal Boolean/all-quantifier separating tests
does not imply C without a condition on identity.

A reflexivity-preserving variant. Change only eq_sigma(x,y) to (delta_xy,1).
Then equality reflexivity itself has value top, and both E_i preserve it.
Nevertheless for distinct x,y (take sigma=t), the full predicate domain has
predicates distinguishing x,y in each coordinate, so

  forall F(Fx IFF Fy)=(0,0),
  eq_sigma(x,y)=(0,1).

The Identity Identity still fails. In this variant the second-coordinate
observer can send a false equality to truth while sending a distinguishing
predicate to different truth values. It therefore fails the appropriately
translated LL clause. Preserving reflexivity alone is insufficient too.
These variants locate the missing obligation precisely; they do not assume
identity is merely a truth-functional connective in C.

2. A C MODEL WITH BOOLEAN SEPARATION BUT NO QUANTIFIER SEPARATION

Use the existing full action model full-two-object-retract, with its recorded
singleton individual action. The category has objects W,V, arrows

  h:W->V, j:V->W, k:V->V,
  jh=id_W, hj=k!=id_V, k^2=k, kh=h, jk=j.

At W, propositions are subsets of {id_W,h}, written (b,c). At V they are
subsets of {id_V,j,k}, written (a,b,c). Actual truth at each object reads
its identity-arrow coordinate. The proposition transports are

  h_t(b,c)=(c,b,c),
  j_t(a,b,c)=(b,c),
  k_t(a,b,c)=(c,b,c).

The full action construction is an established C model; the NEW assertions
here concern its operator-separation formulas.

Boolean separation holds. In addition to the identity operator, the natural
family with current applications

  E_W(b,c)=(c,c),
  E_V(a,b,c)=(a,c,c)

is an admitted exponential element at W. Check h E_W=E_V h and
j E_V=E_W j directly; compatibility with k follows, or is checked directly.
For example both h E_W and E_V h send (b,c) to (c,c,c), and both j E_V
and E_W j send (a,b,c) to (c,c). The full exponential contains this natural
family. Each component is a coordinate-selection map, so it preserves all
Boolean operations and constants literally. Identity observes b and E_W
observes c, hence these two Boolean tests distinguish all four propositions.

The forall_t obstruction. The transport h_t is not surjective: its image
is I={(c,b,c):b,c in 2}, only four of V's eight propositions. Fullness gives
a predicate F:t->t whose truth profile is

  F is true on every (id_W,p), p in D_t(W),
  F is true on (h,a), a in D_t(V), exactly when a is in I.

For precision, any such truth profile R determines the admitted exponential
by alpha(g,a)={l: (lg,l_t(a)) belongs to R}; this automatically satisfies
application/transport coherence. Thus this is an actual represented F,
not a presumed arbitrary graph in a restricted domain.

For every current p, Fp is the proposition (1,1): its root coordinate is
true by definition, and its h coordinate tests h_t(p), which lies in I.
However forall p Fp is (1,0), because a new V-proposition outside I is a
counterexample. Therefore

  forall p BOX(Fp) holds, but BOX(forall p Fp) fails.

This is a direct BF_t counterexample. By Theorem 2's GENERAL forward
argument, separation by operators preserving the universal operation at t fails here,
even though Boolean separation holds.

One can also see the obstruction without using the theorem. The current
truth map p |-> truth(Op) of a Boolean test is a Boolean homomorphism from
2x2 to 2, hence either b or c. A test of the c-coordinate sends forall F
above to false, whereas each O(Fp)=O(top) is true. It therefore fails the universal operation identity at t. Every eligible test therefore reads only b, so
none distinguishes (0,0) from (0,1).

The record also has Gallin Comprehension. Thus existence of a single correct,
globally bivalent Gallin evaluator with its established current quantifier
laws does not supply a SEPARATING FAMILY of such tests. The one evaluator
tracks root truth; it does not observe the h-coordinate.

The proved-only Engine was queried with empty background and optional
Gallin Comprehension in the premise set. It confirms that this recorded
model separates both C and C+Gallin Comprehension from BF_t. The explicit
profile above additionally supplies the direct mathematical witness.

3. BOOLEAN AND QUANTIFIER SEPARATION WITHOUT ATOMS OR ACTUALITY

Use the recorded finite-support-permutations model: the sole-object group
G is all permutations of N, individuals are N, and each relational domain
contains exactly the finitely pinned intensions of its type. In particular
propositions are subsets p of G whose membership depends on g restricted
to some finite N_p. Truth is membership of id_G. This is the source's
ideally full action model, not a full powerset hierarchy.

For a permutation pi with finite support K, consider the external
proposition action rho_t(pi):D_t->D_t. It is represented internally by an
admitted tt-operation E_pi. Here is the required admissibility proof.

In a one-object GROUP action, exponential elements correspond to functions
f:D_sigma->D_tau via

  alpha_f(g,a) = rho_tau(g) f(rho_sigma(g^-1)a).

For f=rho_t(pi), this is rho_t(g pi g^-1)(a). Transporting the operator by
h conjugates f to rho_t(h pi h^-1). If h and h' agree on K, their conjugates
of the finite permutation pi are identical: on h(K)=h'(K) they have the
same finite permutation, and they are the identity elsewhere. Hence K pins
the WHOLE exponential element, not just its actual extension. Ideal fullness
therefore puts E_pi in D_tt. Its outputs remain finitely pinned propositions
because group transport preserves each domain.

Boolean laws are immediate: rho_t(pi) is inverse image under the bijection
of arrows g |-> g pi, so it preserves complement, intersection, union and
both constants as actual proposition identities.

Quantifier laws at every type. Each group arrow acts bijectively on EVERY
admitted domain D_sigma. If F has current application f:D_sigma->D_t,
then the group-action quantifier formula is

  forall_sigma F = intersection {f(a):a in D_sigma},
  exists_sigma F = union {f(a):a in D_sigma}.

To check this, at arrow g the quantified variable ranges over D_sigma,
and the transported predicate evaluates rho_t(g) f(rho_sigma(g^-1)a).
Replacing a by rho_sigma(g)b is a bijective change of variable, so truth
at g is exactly truth at g of every/some f(b). The displayed intersection
or union belongs to D_t because this is an action model; there is no claim
that arbitrary external families of propositions have admitted meets.

Inverse image under g |-> g pi commutes with these intersections and unions.
Consequently, for every fixed sigma and current F,

  E_pi(forall x Fx)=forall x E_pi(Fx),
  E_pi(exists x Fx)=exists x E_pi(Fx).

This is identity of propositions, not just root agreement. At any
other arrow E_pi is transported to the operator of a conjugate finite
permutation, so the same proof also covers its transported inputs. The
unboxed finite-list laws already suffice for our separation claim.

Separation. If p!=q, choose g in their symmetric difference. Let N be the
union of finite pinning sets of p,q. The finite partial bijection g|N extends
to a permutation pi of finite support: extend it to a permutation of the
finite set N union g(N), and fix all other natural numbers. Thus pi agrees
with g on N, and pi still belongs to the symmetric difference. Since

  truth(E_pi(p))=1 IFF pi belongs to p,

the operator E_pi distinguishes p,q. The same operator satisfies the
Boolean and quantifier requirements for every member of any chosen finite
Delta. Thus S_B,Q_Delta holds for every finite Delta.

Atomlessness. Given a nonempty proposition p pinned by N and g in p,
choose n outside N. There are permutations g,g' agreeing on N but sending
n to different unused images. The proposition

  q=p intersection {h:h(n)=g(n)}

is nonempty, proper below p, and pinned by N union {n}. Hence there are no
propositional atoms. For a true p, take g=id and n outside its pinning set;
a permutation fixing N but moving n belongs to p. Thus p does not entail
the actual truth that n is fixed. No true proposition entails every actual
truth, so Actuality fails as well. These are also established record verdicts.

The E_pi are generally NOT bivalent. A nonempty proper p remains nonempty
proper after a bijective inverse image. This is why the example is compatible
with the separate audited theorem that diagonal BIVALENT characters separate
exactly under ND_t+Atomicity_t.

4. EXACT LESSONS AND STATUS

Established ordinary arguments:

 * Over H, S_B,Q_Delta need not imply C, even with all finite Delta, full
   Booleanism, and ordinary Functionality (section 1).
 * C does not imply S_B,Q_{t} (section 2, or exact BF obstruction).
 * C+S_B does not imply S_B,Q_{t} (same model).
 * S_B,Q_Delta at every finite Delta does not imply Atomicity_t, Actuality,
   or existence of an ordinary bivalent actual-truth evaluator (section 3).

The new satisfying/violating assertions are kept in this ordinary note;
no model YAML or existing argument history has been edited. These proofs
are not independent Lean model certificates. The counterexample to C -> S_B is proved in
reverse-entailment-countermodel.txt. The stronger separation of necessary
Boolean tests from quantifier tests is in ordered-symmetry-observers.txt.

SOURCE LOCATORS

The coordinate H model and the new observer verdicts are original arguments
here (misc, sections 1-3). The reused C constructions are not ours:

 - topics/classicism/models/full-two-object-retract.yaml and
   groups/full-action-models.yaml: Bacon-Dorr, map's 16 May 2023 draft,
   section 3.5 p.59 fifth paragraph/n.81, p.61.
 - topics/classicism/models/finite-support-permutations.yaml and
   groups/finite-support-one-object.yaml: that draft Appendix D,
   Proposition D.5(1), pp.74-76, with the finite-pinning construction.

For direct checking I used the author-hosted 1 July 2022 draft at
https://andrew-bacon.github.io/papers/Classicism.pdf, Definitions 3.18-3.20
pp.55-56, and Appendix D Definitions D.1-D.4/Proposition D.5 pp.73-74.
Those locators differ from the repository's later draft and are not mixed.
The source proves the underlying constructions are C models; the observer
properties above are the new deductions, not attributed to the paper.

Finite algebra check (23 October 2026). A separate Python enumeration checked
the retract E_W/E_V Boolean operations and h,j,k coherence, the four-element
image obstruction to BF_t, and the Leibniz equality value for all pairs of
B4 elements against all 256 B4-valued predicates. All passed. This checks
those finite coordinate calculations; it is not a proof of the infinite
higher-type hierarchy or an independent Lean model certificate.
