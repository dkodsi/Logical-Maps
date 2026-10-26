# Symmetric ideally-full model: recurrent finite colour approximations

Original ordinary mathematical construction, Codex, 26 October 2026. Direct source: `misc`. No Lean verification, independent human checking or literature novelty is claimed.

## 1. Statement and source boundary

The construction below gives a pointed model of fixed Classicism C with

```math
C+\Box\mathrm{BF}+\Box\mathrm{RP}+\Box\mathrm{BC}+\mathrm{TR}
+\neg\mathrm{WRP}_{et}+\neg\Box\mathrm{TR}_{et}.
```

Thus the proposed implication BF_all + TR_all + RP_all ⇒ WRP_all is false, even with BF and RP boxed and full boxed Boolean Completeness added. Sections 2–9 first prove current RP; section 11 upgrades it to boxed RP, and section 12 verifies boxed BC. All types are the fixed relational types, and the higher-type quantifiers range over the full admitted domains. The model does not have Rigid Comprehension: it fails even Weak Rigid Comprehension at et. Consequently it does not settle the separate strengthening that adds full Rigid Comprehension.

The semantic framework is Dorr's symmetric ideally-full construction, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8, and Lemma 21, p. 10, as recorded in `topics/classicism/groups/symmetric-ideally-full.yaml`. The all-type Barcan argument is the finite-section argument in that group's `barcan-surjective`, located there at §3.1, p. 9, and Proposition 22, p. 11. These sources supply the semantics and the general Barcan lemma, not this new category or the separation proof.

The approximate-lifting method adapts `topics/classicism/arguments/rigid-power-surjections.yaml`, especially parts (a)–(d), and the earlier original `research/2026-10-23/finite-compression-labelled-entrance.md`, §§3 and 7. The new step is compression to a world with a sufficiently large finite colour set, followed by a bijective return. It preserves a given finite pin and the finitely many arrow values relevant to an arbitrary test. Unlike the earlier one-way colour collapse, there is no permanent transition after which all labels can be masked by top.

## 2. The category and its domains

There are objects W_m for every positive integer m, and an object W_infinity. Every underlying base is a separate copy of N. Choose E_m⊂W_m of size m, and choose E_infinity⊂W_infinity infinite and coinfinite. These are the coloured sets. Every uncoloured complement is infinite.

For every ordered pair of objects V,W, the arrows V→W are **all globally surjective functions** f such that f[E_V]⊆E_W. In particular arrows run in both directions between finite-colour and infinite-colour objects. Identities and composites satisfy the same condition, giving a small category of functions. At V use the symmetry group of all permutations preserving E_V setwise, and use the ideal of finite subsets of the whole base.

Take the symmetric ideally-full domains associated to this data. Individuals are the base points. At each relational type the admitted entities are the symmetric profiles pinned by finite base sets. A pin P of an entity x means that arrows with common source and target agreeing on P transport x identically as an entire entity. A finite pin of a tuple is the union of pins of its coordinates. A transported entity h*x has pin h[P]. The domain-admission criterion is finite pinning together with equivariance under postcomposition by target symmetries.

All symmetries are allowed invertible arrows, and images of finite sets are finite, so the stated data meet the symmetric ideally-full construction requirements. Interpret any required relational constants by top. The resulting structure is a model of C. The designated evaluation object is W_1; the proofs will give the same separation at every W_m with finite m.

We use two elementary C facts: coextensive weakly rigid relations are identical, and a relation with an admitted exact-image profile h↦h[D] is rigid. The latter holds because at every reached object its further extensions are exactly the direct images of its current members. Tests necessary on all those members therefore cover every subsequent extension. These facts apply to arbitrary finite argument tuples, including the empty tuple.

### Finite prescriptions

A finite partial map V→W whose prescribed coloured source points have coloured images extends to an allowed surjection. Assign all remaining coloured points, if any, to some fixed member of the nonempty E_W. The infinitely many unprescribed uncoloured points can supply every remaining target value. This is used repeatedly below; no injectivity restriction applies to uncoloured points.

## 3. Boxed BF at every type

Every base arrow is surjective. The finite-section lemma consequently makes every transport at every admitted type surjective. For clarity, if b at W is pinned by M and h:V→W, choose a finite section s:M→V of h. Define a profile at V at an arrow l:V→T by the union of the b-extensions at arrows k:W→T satisfying k|M=l s. If there is no such k take the empty extension. The profile is pinned by s[M] and symmetric. After transport by h, all matching k have the same extension as the actual further arrow, by the pin M, and that actual arrow is among the matches. Thus its transport is b. The individual case is the given base surjectivity; the displayed argument handles any relational type and its full argument domains.

Surjectivity implies BF at every object and every type: any future quantified object is a transport of a present one. Hence full boxed BF holds at every evaluation point. In particular the universal relation at every argument tuple type is an admitted exact-image profile and is rigid.

## 4. Exact images and TR at every finite-colour object

Fix A=W_m with finite m. Let S be a finite subset of A containing E_A. Suppose a set D of tuples from the A-domains is stable under every root endomorphism u fixing S pointwise. Then h↦h[D] is an admitted exact-image profile, pinned by S.

Indeed, let h,h':A→V agree on S and let a∈D have finite pin M. Choose u:A→A fixing S such that h u agrees with h' on M. On M\S choose h-preimages of the required h'-values, and retain the identity on S. These prescriptions are consistent. Because E_A⊆S is fixed, the finite-prescription extension to a surjection is an allowed A-endomorphism. Then u*a∈D and h'*a=h*(u*a), proving h'[D]⊆h[D]. Interchanging h,h' gives equality. Postcomposition by a target symmetry sends h[D] to (g h)[D], proving symmetry. Admission and rigidity follow.

Now let F be weakly rigid at A and let S contain a pin of F and E_A. Write D=F_id. If u fixes S, then u*F=F; weak persistence gives u[D]⊆D. The preceding paragraph supplies an admitted rigid exact-image relation with current extension D. Coextensive-weak-rigidity uniqueness identifies it with F. Therefore

    F_h = h[F_id] for every h out of A.

This proves full TR at each finite-colour object, uniformly over all relational types. It also proves exactness of every rigid bound used below.

## 5. The infinite-colour relation is weak but not rigid

At B=W_infinity define U by U_h=E_V for every h:B→V. It is pinned by the empty set and symmetric. Colour preservation gives weak persistence.

Let Z be an admitted unary test necessary of every current U-member, and let N pin Z. Given h:B→V and y∈E_V, choose x∈E_B\N. Extend h|N together with x↦y to an allowed surjection j:B→V by the finite-prescription lemma. The test assumption gives y=jx∈Z_j. Since j and h agree on N, Z_j=Z_h. Thus E_V⊆Z_h for every h, so U≤Z. This proves weak inextensibility and hence WR(U) at B.

Choose c:B→W_1. The transported U has at W_1 the singleton extension E_1={a}. Let H be the haecceity of a at W_1; H is rigid and coextensive with c*U there. Along any allowed k:W_1→B, however, H has extension {ka}, whereas k c*U has extension the infinite E_B. Thus c*U does not entail H. Since H necessarily holds of its sole current member, c*U fails weak inextensibility. Consequently U is not rigid at B.

The return arrows are essential here. Weakness can fail at a finite-colour object and return at W_infinity. No monotone stage predicate or permanent collapse is used.

## 6. Approximate lifting at a finite-colour target

Fix a finite-colour source A, a rigid relation F at A, an arrow h:A→V with V also finite-colour, a finite N containing E_A and a pin of F, and a rigid Y≤h*F at V. We prove that there are an arrow j:A→V agreeing with h on N and a rigid X≤F such that j*X=Y.

Choose a finite pin T of Y containing E_V. Extend h|N to a surjection j whose only nonsingleton fibres are the finitely many finite fibres already prescribed on N: map A\N bijectively onto V\h[N]. Since every coloured source point is in N, this is colour-compatible. Also j*F=h*F.

Choose a finite P containing N, every nonsingleton fibre of j, and one j-preimage of each member of T. Write D=F_id and set

    D'={a∈D : j*a∈Y_id}.

Exactness of F and Y≤j*F give j[D']=Y_id. If u:A→A fixes P, then j u is constant on every fibre of j: nontrivial fibres are fixed pointwise, and singleton fibres impose no condition. There is therefore a surjection v:V→V with j u=v j. It fixes T, by the chosen preimages. In particular it fixes the finite set E_V pointwise, so it is an allowed V-endomorphism.

Pinning and persistence give u[D]⊆D and v[Y_id]⊆Y_id. The commutative equation therefore gives u[D']⊆D'. Section 4 produces a rigid root exact-image relation X with current extension D'. It satisfies X≤F. The relations j*X and Y are rigid and currently coextensive, so they are identical as whole entities. This proves the lemma. The approximation j may depend on Y and on N; no lift along the original arbitrary h is asserted.

## 7. Compression of an infinite-colour target

Keep a finite-colour source A, a rigid F, a finite N containing E_A and a pin of F, and h:A→B where B=W_infinity. Let Y≤h*F be rigid and let T be a finite pin of Y. Put L=T∪h[N].

Choose a finite-colour object V=W_r and a bijective allowed arrow k:V→B whose image of E_V includes L∩E_B. This is possible: choose a finite nonempty K⊂E_B containing L∩E_B, take r=|K|, map E_V bijectively onto K, and map the infinite uncoloured complement bijectively onto B\K. Notice that k is a bijection of bases, but its inverse need not be an allowed tail arrow.

Choose an allowed surjection c:B→V agreeing with the ordinary inverse k^{-1} on L. The prescribed coloured points lie in K, so their inverse images are coloured; the finite-prescription lemma applies. Then k c fixes T and hence

    k*(c*Y)=Y.

The ordinary function g=k^{-1}h is an allowed arrow A→V: it is surjective, and every coloured point of A lies in N, whose h-image in E_B lies in K. Also c h and g agree on N, so (c h)*F=g*F. Consequently c*Y is rigid and lies below g*F.

Apply section 6 to g, c*Y, and N. It gives an allowed v:A→V agreeing with g on N and a root rigid X≤F with v*X=c*Y. Now j=k v is an allowed A→B arrow, agrees with h on N, and satisfies

    j*X=k*(v*X)=k*(c*Y)=Y.

This proves approximate lifting at the infinite-colour target. The finiteness used is only that of the chosen pins and the source colour set. The extension of Y, the extension of F, and the higher-type domains may all be infinite.

## 8. Full RP at every finite-colour object

Fix a finite-colour A and any rigid F at any relational type τ. Let

    R_F(X) := Rigid(X) ∧ X≤F.

This property is persistent in C. To prove weak inextensibility, let Z be any admitted test necessarily true of every current R_F-member. Choose finite N containing E_A and pins of F and Z.

At an arbitrary h:A→V, let Y be any member of (R_F)_h. The semantics of quantification gives precisely a rigid Y in the full V-domain with Y≤h*F. Sections 6–7 supply a root rigid X≤F and an arrow j:A→V agreeing with h on N such that j*X=Y. The test hypothesis gives Y∈Z_j. Pinning gives Z_j=Z_h. Therefore every member of (R_F)_h satisfies Z_h, for every h; that is R_F≤Z.

Thus R_F is weakly rigid at A. Section 4 gives TR at its higher relation type τt, so R_F is rigid. Since τ and F were arbitrary, full current RP holds at A. This is an all-type proof, not extrapolation from unary classification.

## 9. Failure of WRP and the Rigid Comprehension boundary

At A=W_1 (or any finite W_m), let F be the universal unary relation. It is rigid by section 3. Put W_F(X)=WR(X)∧X≤F. Every current W_F-member is rigid by section 4 and therefore necessarily satisfies the test Z(X)=Rigid(X).

There is an allowed h:A→B. At B the relation U of section 5 is weakly rigid, below h*F=top, and nonrigid. It is therefore a member of (W_F)_h not satisfying Z_h. So W_F does not entail Z and is not weakly inextensible. This is failure of the official WRP_et instance. The same U witnesses failure of boxed TR_et.

For the additional Rigid Comprehension question, fix a∈E_A and consider the current property x≠a. Suppose it had a weakly rigid coextension G. Choose a finite pin S of G containing E_A, and choose an uncoloured x outside S. Its current G-membership is true. An allowed root surjection u can fix S and send x to a. Pinning gives u*G=G, while weak persistence gives a∈G_id, a contradiction. Thus Weak Rigid Comprehension at et and Rigid Comprehension at et fail at the evaluation point.

## 10. Verification of the construction

- Category closure uses only global surjectivity and preservation of colour into colour. Arrows between every pair of objects are present.
- All target and source colour sets are nonempty, and every uncoloured complement is infinite; this verifies every finite-prescription extension used above.
- Section 4 includes the entire finite source colour set in its pin. It does not claim that an arbitrary root surjection is a tail arrow.
- Section 6 includes the entire finite target colour set in T, making the quotient map v an allowed arrow. The approximation handles finite nonsingleton fibres explicitly.
- Section 7 includes h[N] in the compression pin, making k^{-1}h an allowed arrow and preserving the transported rigid bound. The set-theoretic inverse k^{-1} is not silently treated as a tail arrow.
- The returned equality k c*Y=Y follows from agreement on a pin of the whole entity. It is stronger than present coextension and does not require k c to be the identity everywhere.
- All uses of coextension uniqueness compare two weakly rigid relations at the same evaluation object. Every future relation used in the power proof ranges over the full admitted target domain.
- The conclusion is current full TR, full boxed BF, RP and BC, and failure of WRP_et. The boxed RP upgrade is justified in section 11, and BC in section 12; Rigid Comprehension is false.

## 11. A general propagation lemma: RP over a rigid universe is boxed RP

This is a separate ordinary C argument, valid independently of the model. Fix τ and assume that the universal τ-relation top_τ is rigid and that current RP_τ holds. Its rigid-power property is exactly

    R_top(X)=Rigid(X),

since X≤top_τ is a theorem. Applying RP_τ to top_τ therefore makes the rigidity predicate R_τ itself rigid.

Use its weak inextensibility with the admitted test

    Z(F) := Rigid(λX. Rigid(X) ∧ X≤F).

For each current rigid F, RP_τ gives Z(F). Rigidity is a necessitated condition, so Z(F) implies □Z(F). Thus every current R_τ-member necessarily satisfies Z. Weak inextensibility of R_τ gives R_τ≤Z, namely

    □∀F (Rigid(F) → Rigid(λX. Rigid(X) ∧ X≤F)).

This is exactly boxed RP_τ. No universal quantifier was boxed merely from its current truth: the boxed universal is supplied by weak inextensibility of the rigid predicate R_τ.

Consequently, whenever the universal relation is rigid, current and boxed RP at that type are equivalent. Full boxed BF makes every such universal relation rigid, giving the all-type theorem

    □BF_all + RP_all ⇒ □RP_all.

More generally Rigid Rigidity_τ + RP_τ suffices by the same test, without the universal-bound premise.

Apply the lemma to sections 3 and 8. At a finite-colour evaluation point, RP holds at every type and every universal relation is rigid. Hence **boxed RP holds at every type**. Since every object is reached from W_1, the model satisfies RP everywhere, including at W_infinity, where TR fails.

## 12. Boxed Boolean Completeness and atomlessness

The model also satisfies BC at every relational type and every object. This follows from Dorr's hull theorem, *Boolean Completeness does not imply Rigid Comprehension*, Theorem 36, p. 18, and Corollary 37, p. 19, in the multiple-object form recorded in `groups/symmetric-ideally-full.yaml`, `hull-conditions` and `boolean-completeness`. Here are the two required verifications, not an appeal to the analogous one-object model's verdict.

At a finite-colour source V take M_0=E_V; at W_infinity take M_0=∅. For the amalgamation condition (B1), suppose h,h':V→W agree on finite M⊇M_0, and finite P,Q satisfy P∩Q⊆M. Prescribe the amalgam to agree with h' on P and h on Q. The prescriptions agree on the overlap and respect colour. Section 2's finite-prescription lemma extends them to an allowed surjection. This proves the amalgamation demanded by (B1) for all arrows, so in particular for the arrows to which its separation proviso applies.

For the symmetry-evacuation condition (B2), given finite N⊇M_0 and finite P,Q, move P\N off Q by a permutation fixing N and preserving colour. At a finite-colour source all coloured points already lie in N, and the uncoloured complement is infinite. At W_infinity both colour orbits are infinite. One can therefore choose the required fresh images in each orbit and extend the finite injections to permutations. This is exactly (B2).

The hull theorem yields full BC at each object. Since every reachable object was checked, the designated model has full boxed BC, not merely BC_t.

There are nevertheless no propositional atoms at any object. Let p be any nonzero proposition at V, with finite pin S. Choose an arrow h:V→W at which p is true. Take distinct uncoloured a,b outside S. The finite-prescription lemma gives two arrows h_0,h_1:V→W agreeing with h on S, with h_0(a)=h_0(b) and h_1(a)≠h_1(b). Both still satisfy p by its pinning. Thus the admitted identity proposition a=b splits p into two nonzero parts. This proves atomlessness at t at every object.

In particular Actuality fails everywhere: an actuality witness would be a true atom, since it decides every proposition by classical truth and its entailment of every truth. Rigid Comprehension implies Actuality, so the model fails Rigid Comprehension everywhere. This confirms precisely why adding BC_t cannot rescue the main conjecture, while the additional Rigid Comprehension requirement remains outside this separator.
