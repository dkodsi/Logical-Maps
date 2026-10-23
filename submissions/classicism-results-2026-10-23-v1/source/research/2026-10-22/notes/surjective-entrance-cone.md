# A surjective entrance cone: Tame Rigidity and boxed Barcan without necessary tameness

Research argument, 22 October 2026. This is a new construction, not a database edit or a claimed formal verification. Its role is to locate the remaining TR+RP=>WRP problem: unlike the fixed-point entrance cone, it preserves Barcan but loses Rigid Power.

## Statement

There is a singleton-individual symmetric ideally-full model satisfying TR and boxed BF at every type, while failing boxed TR, RP and WRP. Thus even adding necessarily constant quantifier domains in the Barcan sense does not make an unboxed Tame Rigidity assumption necessary.

The semantic construction is Dorr's symmetric ideally-full construction, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8, and Proposition 20. The tail is the recorded `symmetric-qualitative-links-individuals-singleton` model. The source records used for its TR and RP failures are the later `tame-rigidity` and `rigid-power` arguments in `topics/classicism/models/symmetric-qualitative-links.yaml`, dated 11 October 2026. The finite-prescription reasoning is adapted from `arguments/tame-rigidity-factorizable.yaml` and `arguments/rigid-power-surjections.yaml`. The new construction and adaptation have source category `misc`.

## 1. Category

Let B be the qualitative-link pinning base, L its points, and V its nonpoints (companions and links). Both sets are countably infinite. Every tail arrow preserves L and V and is surjective on each. Its symmetry group is the recorded G.

Adjoin an object A whose base is a copy of V. Its endomorphisms are all surjections V->V, and its symmetry group is the full permutation group of V. The incoming arrows A->B are all surjections V->V viewed as maps into B with range exactly the nonpoints. There are no arrows B->A. Composition closes because every tail arrow restricts to a surjection of V. Both objects use finite pinning. Interpret e by a singleton at both objects, and use the symmetric ideally-full domains. Incoming arrows do not alter the tail domains.

For a root relation F pinned by S and with actual extension E, write

    B_S(E)_j = union { j' E : j' has j's target and agrees with j on S }.

The usual weak-rigidity criterion gives F=B_S(E) whenever F is weakly rigid. This criterion is valid with several objects: its proof uses only weak persistence, finite pinning, and the admitted tests B_N(E).

## 2. Every root weakly rigid relation has an exact-image profile

Let F be weakly rigid at A, pinned by finite S, with extension E. If a root endomorphism u fixes S pointwise, pinning gives F_u=E and weak persistence gives uE⊆E.

Fix any outgoing root arrow j, either to A or to B. It is a surjection onto its relevant V. A member of F_j=B_S(E)_j has the form j'a, where a∈E is pinned by a finite M and j' agrees with j on S. Choose a surjection u:V->V fixing S with

    j u = j' on M.

This is a compatible finite prescription: on M∩S take u(x)=x; elsewhere take any j-preimage of j'(x). Every finite prescription on the countably infinite V extends to a surjection. Then ua∈E and, by the pinning of a, j'a=j(ua). Thus F_j⊆jE. Weak persistence gives the reverse inclusion, so

    F_j=jE

at every outgoing arrow.

An exact-image relation is rigid: at any reached world h, its extension after a further k is k(F_h), so every future member is the image of a current member. This proves both persistence and weak inextensibility there, for arbitrary admitted tests. Hence TR holds at A at every relational type. The argument does not assert that every actual extension has an admitted exact-image relation.

## 3. BF holds necessarily

At the root, every outgoing arrow is surjective on each interpreted type. Surjectivity at e is trivial because e is a singleton.

For a root endomorphism j and a root relational entity X pinned by N, choose a finite section s:N->V with j s=id_N. Define Y at an outgoing k by taking the union of X_l over the arrows l having k's target and satisfying l|N=k s. This profile is pinned by s(N) and symmetric. At k j the displayed condition becomes l|N=k|N, so pinning gives (jY)_k=X_k. Thus jY=X.

For an incoming h:A->B and a tail relational entity X, first replace any point in a finite pinning set N by one of its companions. Keep every nonpoint already in N. This yields a finite N'⊆V that still pins X: tail arrows agreeing on a chosen companion agree on its point, since they preserve the companion relation. Choose a section s:N'->V of h. Define Y to have empty extension at all root-target arrows and, at an incoming k, extension

    union { X_l : l is a tail arrow and l|N'=k s }.

It is pinned by s(N') and symmetric. A matching tail arrow need not exist for arbitrary k; an empty union is harmless. At k=m h, the tail arrow m itself matches, and all matching arrows give the same extension by pinning. Thus hY=X.

Surjectivity on all type domains proves BF at A directly. BF already holds at every tail world because the tail arrows are surjective on their pinning base and all domains are finitely pinned (the recorded `barcan-surjective` argument). Therefore boxed BF holds at A.

## 4. Necessary Tame Rigidity fails

The unchanged singleton-individual qualitative tail has the recorded weakly rigid nonrigid relation U at type (tt)t. Since B is reachable from A, boxed TR fails at A. In particular TR+BF does not imply boxed TR; indeed even TR+boxed BF does not imply it.

## 5. Why Rigid Power fails: the projection-code obstruction

Let π:V->L send a companion to its point and an ordered link over (a,b) to a. It is equivariant for every tail arrow m:

    π(mz)=m(πz).

For a link whose endpoints merge, its image is a companion of that common image point, so the same equation still holds. π is surjective.

For x,y∈V define a root proposition r_xy by its profiles:

- at a root endomorphism k, it is true iff kx=ky;
- at an incoming h, it is true iff π(hx)=π(hy).

This proposition is symmetric and pinned by {x,y}. For a root j, transport gives j r_xy=r_(jx,jy). For an incoming h, it gives

    h r_xy=q_(πhx,πhy),

where q_ab is the tail proposition that an arrow identifies the points a,b.

Let Y be the root property of propositions with extension {r_xy:x,y∈V} at every root endomorphism, and Q(L)={q_ab:a,b∈L} at every incoming arrow. It is symmetric and pinned by the empty set. All root arrows are surjective on V and all tail arrows on L, so its profile is exactly the image of its actual extension at every arrow. Thus Y is rigid.

But hY=Q(L), and the tail's recorded `rigid-power` argument proves that the rigid-power property of Q(L) is not weakly inextensible. If RP held at A, the rigid-power property of Y would be rigid, and its transport would be precisely the rigid-power property of Q(L), hence rigid at B. This contradicts the recorded tail failure. Therefore RP fails at A. WRP fails as well, since C proves WRP=>RP.

The obstruction is informative: unrestricted admission of symmetric finitely pinned profiles lets an equivariant qualitative projection lift the tail's problematic rigid bound. A successful TR+RP/WRP separator would need a different tail or a justified restriction on admitted profiles that blocks this lift while preserving the required logical closure. No such restriction is claimed here.
