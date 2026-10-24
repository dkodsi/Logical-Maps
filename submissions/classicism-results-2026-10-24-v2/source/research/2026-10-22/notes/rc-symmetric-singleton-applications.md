# Singleton-individual variants: direct choice verdicts from the stabilizer theorem

OpenAI Codex research argument, 22 October 2026. No records were edited. This is a narrow audit of the ten recorded `symmetric-*.yaml` constructions and their generated singleton-individual variants, using `rc-symmetric-ideal-full-categories.md`. These are new mathematical verdicts here, not a claim that a fresh engine computation has updated the map. The existing shared group's Relational Choice failure argument is restricted to `individuals: base`.

## 1. Criterion used

At an evaluation object V, a membership-selector instance of RC_(tt,t) would have a finite pinning set N such that every symmetry fixing N acts trivially on D_t(V). Therefore, to refute this RC instance, it suffices to show:

    for every finite pinning set N, some g∈(G_V)_N and p∈D_t(V)
    satisfy g_*p≠p.

This concerns propositions and pinning carriers. Replacing the actual individual domain by a singleton does not remove these propositions or change the transport action on them.

The common proposition is

    p_ab(w) iff w(a)=w(b).

It is symmetric because target symmetries are injective, and it is pinned by {a,b}. Precomposition gives g_*p_ab=p_(g(a),g(b)). Thus, when g transposes a and c and fixes b, a permitted arrow w with w(a)=w(b)≠w(c) proves g_*p_ab≠p_ab. The points a,b,c in this test are pinning-carrier points, not terms required to exist at individual type e.

## 2. Direct negative applications

Each line refers to the exact construction in `topics/classicism/models/<id>.yaml`. In every case the conclusion is failure of RC_(tt,t), and hence of the full RC schema, for BOTH choices of individual domain. The base-individual failure was already established by the shared group's separate type-(et,e) proof; the useful new application is the singleton variant.

| Construction ID | Symmetry and distinguishing arrow |
| --- | --- |
| `symmetric-all-surjections` | Choose a,b,c outside N; g=(a c). A surjection can identify a,b while keeping c distinct. |
| `symmetric-infinite-classes` | Choose a,b,c outside N in one infinite qualitative class; g=(a c) is a class automorphism. All surjections are arrows, so the required collision pattern is available. |
| `symmetric-class-reflecting-surjections` | Choose a,b,c outside N in one qualitative class. Use g=(a c), and a surjection that maps each qualitative class onto itself, merging a,b but not c in their class. Such a map reflects the qualitative equivalence, hence is an allowed arrow. |
| `symmetric-collapse-pair` | Choose a,b,c outside N and the distinguished pair. Use g=(a c). A surjection may collapse the distinguished pair and also a,b, while keeping c distinct; it is an allowed collapsing arrow. |
| `symmetric-range-gap` | Choose a,b,c outside N and the distinguished d. Use g=(a c), fixing d. A function omitting d from its range can realize the required collision pattern, so is an allowed arrow. |
| `symmetric-range-gap-without-actuality` | The same symmetry and omitted-d arrow are allowed by the second arrow clause of this construction. |
| `symmetric-two-object-unpinned` | At the first object choose a,b,c outside N and g=(a c). Define p_ab on all outgoing arrows by the collision formula. It is false on the root's permutation arrows; an arrow to the second object is any function and can realize the distinguishing collision. This is a finitely pinned symmetric proposition at the first object. |
| `symmetric-qualitative-links` | Choose a,b,c links in one infinite fiber outside N, and transpose a,c while fixing every point and every other nonpoint. The collision pattern is realized by a surjective relation-preserving map collapsing the distinguished point-pair; the direct construction is detailed below. |
| `symmetric-qualitative-contrast` | Use the different proposition construction below, because every arrow is injective. |

### Qualitative links: the needed arrow exists

Choose two distinct point endpoints u,v away from the distinguished point-pair, and choose a,b,c links over (u,v), outside N. The transposition (a c) preserves the ternary relation and fixes every point, so is in the designated symmetry group.

Choose a surjective map f on the infinite point set which collapses the distinguished pair and fixes u,v. Extend f to the nonpoints fiber by fiber. A companion pair over x maps onto the companion pair over f(x). A link fiber over distinct x,y maps into the link fiber over f(x),f(y) if these differ, and into the two companions of their common value if they agree. Choose each such fiber map surjective; these are the concrete countably infinite link fibers in the recorded construction. On the unchanged infinite fiber over (u,v), choose its surjection to identify a,b and keep c distinct.

The resulting whole map preserves the ternary relation. It is onto points by construction. Every target companion pair has a source companion pair above a point preimage; every target link fiber has a source link fiber above preimages of its distinct endpoints. Hence the whole map is surjective. It collapses the distinguished pair, so belongs to the allowed second class of arrows. It distinguishes p_ab and p_cb as required.

The record already states the stronger fact that arbitrary binary assignments on finitely many nonpoints can be realized by a collapsing arrow (its singleton Tame Rigidity argument). The present fiberwise construction proves only the small instance needed here.

### Qualitative contrast: target-coordinate propositions

Write V=W_0 and W=W_1 as in the record: all arrows between any objects are permutations; G_V is the full permutation group and G_W is trivial. Fix a carrier point k at W. For a carrier point a at V define the proposition p_a at V by

    p_a(w) iff target(w)=W and w(a)=k.

It is symmetric: at W the symmetry group is trivial, and profiles ending at V are empty. It is pinned by {a}. For any finite N choose distinct a,c outside N and g=(a c)∈G_V. Then g_*p_a=p_c, and a permutation w:V→W with w(a)=k has w(c)≠k. Thus the two propositions are distinct. RC_(tt,t) fails at the root, including in the singleton variant.

## 3. The positive singleton case: old and new individuals

The remaining construction, `symmetric-old-new-individuals`, behaves differently with a singleton individual domain. It satisfies Relational Choice and Transversal Choice at BOTH objects, hence their boxed schemas at the evaluation object. No metatheoretic choice beyond finite choice is needed.

The record already proves that every type domain is finite and every entity is fixed by every designated symmetry in this variant (`when: individuals: singleton`, dated 7 October 2026). Here is the intensional induction, to ensure that finiteness of root extensions is not being mistaken for finiteness of entities.

At E there are two arrow kinds, E→E and E→O. At O there are three: O→E, O→O in G_O (old/new preserving permutations), and O→O in K (injections landing among old individuals). Compositions of kinds are determined by kinds. The individual domains are singleton, so finite, and their symmetry actions are trivial.

Assume inductively that the domains of all argument types of a relation type are finite at both objects and their symmetry actions are trivial. Take any finitely pinned intension X at a source object, with finite pinning set N. If h,h′ are two arrows of the same kind, a symmetry g of their common target can match their restrictions on N:

* at target E, any finite partial bijection of images extends to a permutation;
* at target O, for E→O or K arrows all relevant images are old, so a permutation of old individuals matches them;
* for G_O arrows, the finite matching preserves old/new status and extends separately on the two parts.

Therefore gh and h′ agree on N. Pinning and symmetry give

    X_h′ = X_(gh) = g_*[X_h] = X_h,

because g fixes every lower-type argument entity by induction. Thus the entire intension is determined by finitely many profiles, one for each arrow kind, each a subset of a finite tuple-domain. There are only finitely many such profile assignments, so the whole higher-type domain is finite.

Precomposition by a symmetry of the source preserves arrow kind. Hence it fixes every profile assignment, so acts trivially on this higher-type domain. This completes the simultaneous finiteness/trivial-action induction, including all transports.

Finally, in ANY C-model in which the actual input and output domains are finite, every serial relation has an admitted functional subrelation: enumerate the finitely many actual inputs x_i, choose one y_i in each fiber by finite choice, and use

    S(x,y):=∨_i (x=x_i ∧ y=y_i).

The formula is an admitted relation and is functional and contained in the given relation at the evaluation point. Likewise, for an equivalence relation on a finite domain, choose one point from each of the finitely many cells and represent the resulting finite transversal by a disjunction of equalities. These are actual statements, so no persistence of the finite choices is required.

This works at both E and O and every admitted type. The transport semantics then validates the boxed RC and TC schemas at the root E.

## 4. Limits of this application audit

This table settles the mathematical RC verdict for the singleton variants under the recorded construction definitions, but does not claim a database update or a proof-assistant check. It does not infer failures of any particular TC INSTANCE from failure of RC_(tt,t), nor identify TC with the distinct principle recorded under `transversal-r`. It also makes no general RC⇒TC claim beyond the ideal-full semantic theorem.

The useful outcome for the search is narrow: none of these ten singleton variants supplies an RC/TC separator. Nine already fail a proposition-output membership selector; the old/new variant has finite domains and satisfies both schemes at every world.
