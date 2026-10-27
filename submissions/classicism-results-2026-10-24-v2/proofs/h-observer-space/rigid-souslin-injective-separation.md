# A rigid Souslin algebra with separating complete selfembeddings

26 October 2026. Ordinary mathematical argument by OpenAI Codex. Direct source: `misc`, this note, unpaginated.


## 1. Result and scope

Assuming diamond, there is an atomless complete Boolean algebra B such that:

1. B is rigid: its only Boolean automorphism is the identity.
2. For every nonzero b in B, the join of E(b), over the complete injective
   endomorphisms E of B, is 1.
3. Its only surjective complete endomorphism is the identity. Consequently its
   only complete endomorphism with a complete left inverse is the identity.

Thus the exact Boolean criterion of
[the generic separation test](generic-boolean-separation-test.md), §§2–4, has
v_Inj = 1, v_Split = 0 and delta_B = 1. The full generic Boolean Henkin model
therefore satisfies

    C5 + boxed full InjSep + boxed all-type RC + boxed all-type TC
       + boxed all-type Zorn + boxed failure of propositional SplitMono.

Every observer qualification retains identities of whole Boolean and quantifier
operations. The inverse requirement is a whole-operation identity with a
qualified logical left inverse. The failure uses the propositional instance
whose qualification includes quantification over propositions, and therefore
refutes the full SplitMono schema. No extra assumption is added to the proposed
implication. The construction disproves it even after adding current full RC
and all-type Zorn. Section 9 proves that ZFC itself constructs the stated
countable Henkin countermodel by using the algebra and full hierarchy internal
to L; diamond need not hold in the ambient universe.

## 2. Normal trees and tail projections

We build a normal tree T of height omega_1, with countable levels and countably
infinitely many immediate successors at every node. The root is the only node
of level 0. All later levels are countably infinite. Limit nodes are determined
by their predecessors. Every node has extensions at every later level.

A projection i is introduced at a birth level beta_i >= 1. It is a level-preserving
map pi_i on the tail T at levels at least beta_i, compatible with predecessors
within that tail. It is onto every such level and has the following lifting
property, called niceness here:

    if pi_i(s) <=_T u, then some t >=_T s has pi_i(t) = u.

There is no requirement to define pi_i on earlier tree levels. This is essential:
a complete Boolean embedding may send an earlier tree node to a join of many
tree nodes. A projection on a cofinal tail is sufficient to represent it.

At any countable limit alpha above beta_i, put X_alpha = [T restricted to alpha],
the space of all cofinal branches through the tree already constructed. For a
node s, write [s] for the set of branches containing s. These cones form a
countable clopen basis. Choosing an increasing cofinal sequence of levels
identifies X_alpha with the inverse-limit space of a countable sequence of
countable discrete levels. It is a nonempty Polish space with no isolated points.
Normality supplies branches through every node by dependent choice along that
sequence.

The tail projection induces a continuous open surjection pi_i:X_alpha -> X_alpha.
For a node s at or above its birth, niceness gives exactly

    pi_i[[s]] = [pi_i(s)].                                      (2.1)

To lift a prescribed target branch through pi_i(s), successively lift its nodes
on a cofinal sequence of levels, starting at s. Their union is the required
source branch. Equation (2.1) proves openness; compatible predecessors prove
continuity. The earlier levels of an output branch are its unique predecessors.

Projection names introduced below a fixed countable alpha form a countable set.
Every finite composition of their branch maps is defined on X_alpha and is again
continuous, open, onto, and nice on a sufficiently high common tail.

## 3. Successor labels and the two fibre properties

At each level gamma, first introduce the fresh projections assigned to that
level as in §6. Let I_gamma be the countable set of all projection names born
at or below gamma. Let M_gamma be the free monoid of finite words in I_gamma,
including the empty word. Label the successors of each node s in T_gamma by

    K_gamma = {k:M_gamma -> omega : k has finite support}.

This is a countably infinite set. A successor is denoted (s,k). For every active
projection i define

    pi_i(s,k) = (pi_i(s), shift_i(k)),
    shift_i(k)(v) = k(iv).                                     (3.1)

Each shift is onto K_gamma: to lift l, put k(iv)=l(v) and put zero elsewhere.
Its fibres are infinite because k at the empty word remains free. Thus (3.1)
preserves niceness, surjectivity, and compatibility with predecessors. The label
set changes when the active alphabet grows. No identification with the previous
level's label set is needed: (3.1) uses the same current label set at every node
of the current level, which is all that composition requires.

Our word convention is

    pi_(iv) = pi_v composed with pi_i.

The first letter is applied first. At a successor beyond all birth levels in
the word w,

    pi_w(s,k) = (pi_w(s), shift_w(k)),
    shift_w(k)(v) = k(wv).                                     (3.2)

Two consequences will be used at every later countable limit alpha.

**(A) Every nonempty word map is nowhere locally injective.**
Take any nonempty basic open cone, refine it past all births in w, and choose
a successor level still below alpha. Two successor labels can agree at every
w-prefixed coordinate while differing at the empty coordinate. The corresponding
distinct nodes have the same pi_w-image. Niceness of the composition lifts one
target branch through that image to a branch through each of the two nodes.
Both branches lie in the original cone and have the same image.

**(B) If w does not begin with i, including the empty word, pi_w is nowhere
locally constant on every fibre of pi_i.**
Fix z in X_alpha and a nonempty relatively basic open set
[s] intersect pi_i^{-1}{z}. Choose gamma sufficiently high that gamma+1<alpha,
all the names in i,w are active, and gamma is above s. A branch in that fibre
supplies a node t at level gamma. If z's successor label at gamma+1 is l, the
condition pi_i(t,k)=z restricted to gamma+1 fixes exactly

    k(iv)=l(v), for all v in M_gamma.

Since w does not begin with i, k(w) remains free. Give it two different values.
The root coordinate of shift_w(k) then differs, so the two resulting pi_w-image
nodes are different. Both source nodes lift, by niceness of pi_i, to branches
whose complete pi_i-image is z. Thus every relatively basic open set in the
fibre contains two different pi_w-images.

In particular every pi_i-fibre is nonempty, closed, and has no isolated points:
apply (B) to the empty word. It is a perfect Polish space. Notice that (B) does
not require preserving simultaneous prescribed fibres of several maps. A single
successor can change the pi_w-image irreversibly, after which only the prescribed
pi_i-image needs to be lifted. This is why the single-fibre limit construction
below is sufficient.

## 4. Two countable-level extension lemmas

Fix a countable limit alpha and abbreviate X_alpha by X. All maps in this section
are those born below alpha.

### 4.1 The countable closure construction

Suppose N subset X is dense, is closed under every pi_i, and has the property
that N intersect pi_i^{-1}{z} is dense in pi_i^{-1}{z} for every z in N.
There is a countable dense D subset N, containing any prescribed countable
subset of N, such that D is forward closed and

    D intersect pi_i^{-1}{z} is dense in pi_i^{-1}{z}
    for every i and every z in D.                              (4.1)

Start with a countable dense subset of N and the prescribed points. Repeatedly
close under all word maps. For each point z currently selected, every active i,
and every basic cone meeting its fibre, choose a point of N in that intersection.
Repeat this process omega many times. There are only countably many requirements
at each round, and every eventual point's requirements are handled at a later
round. The union is the desired D.

Make T_alpha consist of one new node for each branch in D. Forward closure
extends every pi_i to this level. Condition (4.1) makes each extension onto and
nice: if z in D extends pi_i(s), lift z to a branch through s using (2.1), then
use (4.1) in that cone to obtain an admitted source branch. Density of D makes
the new tree level normal. Distinct branches give distinct nodes.

### 4.2 Comeagre sets can be respected

For a continuous open surjection pi:X->X and a comeagre G_delta A subset X,
there is a comeagre G_delta set K_pi(A) of targets z such that
A intersect pi^{-1}{z} is comeagre in that fibre.

Here is a direct proof. First take A=U open dense. For each basic open V,
pi[V intersect U] is open and dense in the open set pi[V]. The exceptional
targets for that V lie in

    pi[V] minus pi[V intersect U],

a subset of the nowhere dense boundary of the open set pi[V intersect U].
Outside the union of these closed boundaries, U meets every
nonempty relatively basic open subset of the fibre. Hence its intersection
with the fibre is open dense. For A a countable intersection of open dense
sets, intersect the corresponding comeagre G_delta target sets and use the
Baire theorem in each nonempty closed Polish fibre. We require only a comeagre
G_delta set contained in the good targets; the exact set of good targets need
not itself be G_delta.

Now let M subset X be comeagre G_delta. Set M_0=M and recursively choose

    M_(n+1) = M_n intersect (intersection_i pi_i^{-1}[M_n])
                     intersect (intersection_i K_pi_i(M_n)).   (4.2)

Every set here is comeagre G_delta. Preimages of comeagre sets under continuous
open maps are comeagre. Put N=intersection_n M_n. Then N is comeagre and forward
closed. For z in N, its pi_i-fibre meets every M_n comeagrely, by z's membership
in K_pi_i(M_n); their intersection N is therefore comeagre in that fibre. Thus N
has all the hypotheses of §4.1. We can select D wholly within M while extending
all projections nicely.

## 5. Sealing a nontrivial homeomorphism

Suppose f:X->X is the homeomorphism induced by a nontrivial automorphism of a
cofinal restriction of the tree already built. There is a nonempty cone U with
f[U] disjoint from U: take a moved node and the disjoint same-level image cone.

For every nonempty word w, the closed set

    {x in U : f(x)=pi_w(x)}

has empty interior. Otherwise pi_w would equal the injective f on a nonempty
open set, contrary to §3(A). The empty word gives no equality on U. By Baire,
choose x in U such that, putting y=f(x),

    y is not pi_w(x) for any finite word w.                    (5.1)

Let F be the union, over all finite words including the empty word, of
pi_w^{-1}{y}. Every one of these closed sets is nowhere dense: word maps are
open, and X has no isolated points. Hence N=X minus F is comeagre. It contains
x by (5.1), excludes y, and is forward closed.

For every z in N and every i, N is also comeagre in the fibre pi_i^{-1}{z}.
Indeed, if w begins with i, write w=iv. On that fibre pi_w is constantly
pi_v(z), which is not y because z is outside F. Its forbidden preimage is empty.
If w does not begin with i, §3(B) makes its forbidden preimage a closed nowhere
dense subset of the fibre. The countable union is meagre in the nonempty
perfect Polish fibre.

Apply §4.1 to N, prescribing x. The resulting D extends x but not f(x), and
still extends every projection nicely. Therefore f cannot extend across this
new tree level. This seals f without deleting or modifying any previously
constructed node or projection.

## 6. The diamond recursion

Use a standard diamond sequence on omega_1. Code two kinds of objects with
different initial tags: a tree antichain, or an automorphism of a club restriction
of a tree. This does not require diamond on a preassigned stationary subset.
Each tagged global code is itself guessed on a stationary set. Intersecting
that set with the relevant club of coding-closure stages gives the needed
guesses. For example, code level alpha in the countable ordinal interval
[omega*alpha,omega*(alpha+1)). Work on the club of alpha with omega*alpha=alpha,
also closed under the chosen tuple-coding functions. At those stages, restriction
of the global code to alpha codes precisely the structure below alpha. Coding
graphs, a club of levels, and the initial tag uses the same closure convention.

At level alpha>=1, after the level has been constructed, introduce one fresh
projection for each ordered pair (t,s) in T_alpha squared. Its initial map on
T_alpha is any onto map with infinite fibres that sends t to s. Such a map
exists on every countably infinite set, even after prescribing that value.
It has no earlier tail obligations. There are countably many new names.

At successor levels use §3. At a nonzero countable limit alpha, inspect the
diamond guess.

* If it codes a maximal antichain A of T restricted to alpha, the set of branches
  meeting A is open dense in X_alpha. Apply §4.2 and then §4.1 with this set M.
  Every new node then extends a member of A, so A remains maximal in the entire
  future tree.
* If it codes a nontrivial automorphism of T restricted to a cofinal club of
  levels below alpha, apply §5 to its induced branch homeomorphism.
* Otherwise use §4.1 with N=X_alpha.

The tags distinguish the first two tasks, so simultaneous satisfaction of their
extra requirements is unnecessary. In every case all active projections remain
nice and onto, and the tree remains normal with countable levels. Fresh maps
are then introduced on the completed level alpha as just described.

The resulting T has no uncountable antichain. If A were a maximal antichain
of T, there is a club of countable alpha such that A restricted to the lower
tree is already maximal there: close alpha under the choice, for every lower
node, of a compatible member of A and the levels needed for their compatibility
witnesses. At a correct tagged diamond guess on this club, the construction
seals that initial antichain. No later node can belong to A. Therefore A was
bounded and countable. Every antichain extends to a maximal one, so T is ccc.
A normal splitting omega_1-tree with a cofinal branch would have an uncountable
antichain by taking an off-branch successor at each level. Thus T has no cofinal
branch and is a Souslin tree.

## 7. The Boolean algebra is rigid and its embeddings separate

Let B=RO(T), with tree nodes identified with the corresponding regular-open
cone conditions. This is an atomless complete Boolean algebra, and T is a
dense Souslinization.

Every Boolean automorphism h of B restricts to an automorphism of T on a club
of levels. We use the Restriction Lemma cited in §10. Here is the short argument.
Every countable maximal antichain of B is refined by a tree level: below each
antichain member choose a maximal family of tree conditions, use ccc to bound
the union of those families in height, and take a later level. Close a club of
countable ordinals under the levels needed to refine h[T_alpha] and h^{-1}[T_alpha].
At a limit delta in this club and t in T_delta, h(t) lies below a unique member
of each lower tree level; the refinements make these members a coherent branch.
Some u in T_delta meets the nonzero h(t), since T_delta is a maximal antichain.
It follows that u has precisely this predecessor branch, and unique limits make
u unique; therefore h(t)<=u. For every beta<delta, a refining level below delta
makes u lie under a member of h[T_beta]. Since u meets h(t), that member must
be h(t restricted to beta). Thus h^{-1}(u) lies below every predecessor of t.
In a Souslinization t is their meet,
so h^{-1}(u)<=t and h(t)=u. Thus h permutes T_delta. The same proof works for
an isomorphism between two Souslinizations.

If a Boolean automorphism were nontrivial, choose a moved node on its club
representation. At a correct tagged diamond guess alpha beyond that node,
with alpha a limit point of the club, §5 extends a branch x but omits its image.
Since the club is closed, alpha belongs to it, so the purported automorphism
would have to send the new node above x to a node above the omitted image.
There is no such node. This contradiction proves rigidity of B.

Each tail projection pi_i yields a complete injective endomorphism E_i of B.
For a node s at a level gamma>=beta_i, its value is

    E_i(s) = join {t in T_gamma : pi_i(t)=s}.                   (7.1)

The fibres partition each level. Niceness says that the inverse image of every
dense open subset of the target tail is dense in the source tail. Equivalently,
the equivalence relation of having the same pi_i-image is a nice tree equivalence
relation, and the quotient tree is isomorphic to the original target tail.
Its regular-open algebra is therefore a complete subalgebra of B, with (7.1)
the complete embedding. One can check regularity directly on maximal antichains:
every maximal antichain is countable and hence bounded in height; refine to a
level beyond that bound and beta_i, whose inverse-image partition still has join
1. Nonempty fibres make the map injective. These facts also show that ignoring
the initial part of the tree loses no Boolean conditions.

Fix nonzero b,c in B. Choose nodes s<=b and t<=c and extend them to a common
level alpha>=1. The projection born for the ordered pair (t,s) satisfies
pi_i(t)=s, so

    0 < t <= c meet E_i(s) <= c meet E_i(b).

Thus every nonzero c meets at least one E_i(b). Completeness of B gives

    join_i E_i(b)=1 for every b>0.                             (7.2)

In particular v_Inj=1 for the full external class of complete injective
endomorphisms; (7.2) uses only the explicitly built family.

## 8. No qualified left-inverse separation, and the typed model

First, rigidity of any complete Boolean algebra B rules out an isomorphism
alpha:B -> B restricted to u when u<1. Put a=not u>0. Restricting alpha to the
interval below a gives an isomorphism from B restricted to a to B restricted
to alpha(a). These are disjoint nonzero intervals. Swapping them by this
isomorphism and its inverse, and fixing the complementary interval, gives a
nonidentity automorphism of B, a contradiction.

If F:B->B is a surjective complete endomorphism, its kernel has a largest element
a, the join of the kernel, because F is complete. Its restriction to B below
not a is an isomorphism onto B. The previous paragraph forces a=0; F is then
an automorphism and hence is the identity. If F composed with E is identity
and both are complete endomorphisms, F is onto, so F=E=identity. Therefore

    v_Split = meet {b : b>0} = 0,                             (8.1)

using atomlessness. Combining (7.2) and (8.1) gives delta_B=1.

For the logical interpretation use the full generic Boolean Henkin construction
and its exact observer identification, as proved in
[the generic separation test](generic-boolean-separation-test.md), §§2–3.
The ambient domains are A_e=omega, A_t=B, and the full permitted function sets.
A sufficiently large H_theta and countable elementary M contain these domains,
B, its operations, and the projection/embedding family. The interpreted domains
are D_sigma=M intersect A_sigma; worlds are all M-generic ultrafilters on B
intersect M. Formula denotations use ambient Boolean quantification, and the
generic truth lemma turns these into classical quantification over the D_sigma.
Restriction is faithful by elementarity. The construction satisfies C5.

Every E_i is a complete Boolean endomorphism and therefore preserves every
ambient typed quantifier, not just a bounded collection. Thus the same observer
meets any requested finite qualification list, with equality of whole
operations. For every nonzero admitted b, the dense set below the values
E_i(b), supplied by (7.2), and elementarity give a separating admitted E_i at
each generic world. Unequal higher relational objects have an admitted argument
tuple where their B-values differ, again by elementarity; the same propositional
separator then handles that tuple. This gives full relational InjSep everywhere.

Conversely an admitted observer qualified at input type t is an ambient complete
Boolean endomorphism: every external subset S of B is encoded by the admitted
ambient predicate taking b to b on S and to 0 elsewhere, and faithful
elementary restriction transfers its whole-quantifier test back to the ambient
map. A qualified pair with whole inverse identity therefore consists of two
ambient complete endomorphisms whose composite is identity. Both are identity
by the preceding argument. At any generic world, a fixed admitted 0<b<1 agrees
in truth with either 0 or 1 while being distinct from that endpoint. Identity
alone cannot separate that pair. This is failure of the propositional SplitMono
instance, and hence of full SplitMono, at every world.

The admitted rigid wellorders and least-member definitions in
[the choice-model proof](generic-boolean-choice-model.md),
§§2–4, prove all-type RC and TC at every world, including individual outputs
represented by relations. The recorded TC-to-Zorn implication gives all-type
Zorn. These are existing facts about the ambient full-hierarchy construction.
Since every nonzero M-Boolean element is contained in some M-generic world,
a formula true at every world has value 1. The corresponding native boxes
therefore hold, giving all the separately boxed schema verdicts stated in §1.

## 9. ZFC constructs the countermodel using L

Work now in an arbitrary ambient universe V satisfying ZFC. Perform §§2–8's
tree and Boolean-algebra construction inside L, which satisfies diamond. Form
inside L the full relational hierarchy A_e=omega, A_t=B and
A_(sigma tau)=(A_tau raised to A_sigma)^L for every permitted arrow. These are
sets in V. Choose theta regular in L and sufficiently large in L for all these
domains, all the function spaces and powersets used in the qualification tests,
the Boolean operations and joins, and the construction parameters. Theta need
not be regular in V.

In V, downward Lowenheim–Skolem supplies a countable

    M elementary in H_theta^L

containing the hierarchy and these parameters. Use D_sigma=M intersect A_sigma
and restricted application. Elementarity makes the restriction faithful: if
two ambient L-coded functions in M differ, their difference has an argument
witness in M. Lambda denotations and the Boolean operations computed in L belong
to the designated L-function domains, and their definitions with M-parameters
return their codes to M.

Here the quantifier truth lemma can be verified directly, so it does not assume
that the L-algebra is complete in V. For an M-coded f:A_sigma->B put

    q = meet^L {f(a):a in A_sigma}.

The following set is dense in B as computed in L and has its code in M:

    D_f = {c>0 : c<=q or some a in A_sigma has c<=not f(a)}.

Elementarity makes D_f intersect M dense in B intersect M and supplies an
M-witness a for its second alternative. Build, in V, ultrafilters G on the
countable Boolean algebra B intersect M meeting every M-coded dense set.
Countable diagonal construction supplies such a G below any prescribed nonzero
M-condition. Then

    q in G iff f(a) in G for every a in D_sigma.

The forward implication uses q<=f(a). For the reverse implication, a member
of G intersect D_f cannot lie below q if q is absent from G, so an M-witness
to the second alternative supplies an a with f(a) absent from G. Existential
quantification follows by complementation. Formula induction now gives the
same classical generic truth lemma as in §8. Every nonzero M-Boolean value has
a world where it is true. This supplies the same C and C5 interpretation,
including faithful whole-operation identities and native boxes.

An admitted qualified observer is an L-coded M-function. Qualification at
input type t tests every L-subset of B through its predicate code in the
L-full hierarchy. Elementarity therefore identifies it with an L-complete
endomorphism, which is exactly the class covered by the proof of rigidity and
surjective-endomorphism uniqueness carried out in L. Conversely each of the
constructed L-complete E_i preserves every L-typed quantifier. For admitted
b>0, the L-dense set of conditions below some E_i(b) is M-coded. Its meeting
at G and elementarity return an admitted i and E_i separating b. Higher
relational separation uses the same faithful argument witnesses as in §8.
If an admitted qualified pair has composite identity after restriction, its
ambient L-composite is identity by faithfulness; the L theorem forces both
maps to be identity. Thus the positive and negative observer verdicts transfer
with their full scopes.

Finally, L supplies a genuine wellorder of each entire A_sigma, whose Boolean
characteristic relation can be selected in M by elementarity. Such a wellorder
remains well-founded in V: in L it has an order isomorphism with an ordinal,
and that isomorphism is still present in V. Its restriction externally
wellorders D_sigma. The least-member relational constructions of the cited
choice proof consequently apply at every generic world, giving the same
boxed all-type RC, TC and Zorn verdicts.

This proves in ZFC the existence of the countable Henkin countermodel in §1.
It makes no claim that the L-algebra is complete or rigid with respect to every
new subset or map in V. Those extra maps are not admitted objects of this
Henkin hierarchy. The only completeness, rigidity, and endomorphism facts used
are the L-facts transferred through the selected L-full domains and their
countable elementary hull.

## 10. Sources and verification boundary

The existence construction, including the tail-birth bookkeeping, free-word
successor labels and the two limit fusion arguments, is new research in this
note: direct source `misc`, §§1–8, unpaginated.

Gido Scharfenberger-Fabian, [Souslin Algebra Embeddings](https://arxiv.org/pdf/0904.0113),
§1.3, Restriction Lemma 1.2, printed p.6, supplies the club representation used
in §7. Its §1.4, printed p.7, recalls diamond coding. Its §5.3, Theorem 5.8,
printed pp.30–31, supplies the background method of sealing automorphisms while
preserving nice projections; our additional selfembedding family and its
separation property are not conclusions attributed to that theorem. The paper's
§2 supplies the nice tree-equivalence representation of complete subalgebras;
§5.1, Lemma 5.6, printed p.28, states the open branch projection fact also proved
directly here.

The exact passage from complete Boolean endomorphisms to full typed observer
qualifications and separation is the existing reduction in
[the generic separation test](generic-boolean-separation-test.md), §§2–4.
The admitted-wellorder choice verification and TC-to-Zorn use the existing
sources linked in §8.
