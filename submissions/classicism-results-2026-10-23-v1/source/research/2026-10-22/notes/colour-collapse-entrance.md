# A colour-collapse entrance separating the single-type power principles

Research proof, 22 October 2026. This construction and its verifications were developed in this research session and independently checked between the rigidity and principles lanes. No database record has been edited; no formal verification or literature novelty is claimed.

## Exact result

There is a model of fixed Classicism satisfying

    TR at every relational type,
    boxed BF at every type,
    boxed RP at relation type et,

but failing WRP at relation type et. Here et means unary relations on individuals; their power properties have type (et)t. In particular, the implication TR_et+RP_et=>WRP_et is false, even when TR and BF are strengthened to the displayed full-schema/boxed assumptions.

The full-schema conjecture TR+RP=>WRP remains open in this analysis: RP at all higher relation types has not been verified for this model. The result shows that any proof of that full-schema implication must use RP instances beyond the unary type where its conclusion is asserted.

The construction uses Dorr's symmetric ideally-full semantics, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8, and Proposition 20. The finite-pinning weak-rigidity criterion is the one recorded in `topics/classicism/arguments/tame-rigidity-factorizable.yaml`; the surjective-arrow BF argument is `barcan-surjective` in `groups/symmetric-ideally-full.yaml`. These sources supply the general semantics, not the new colour-collapse construction, whose source category is `misc`.

## 1. The three-object category

Take three countably infinite bases A,B,C. At B distinguish an infinite coinfinite subset E_B. At C distinguish a two-element subset E_C={c_0,c_1}. Call members of E the coloured individuals; A has no distinguished colour.

- Endomorphisms of A are all surjections A->A.
- Endomorphisms of B and C are all globally surjective maps preserving the coloured set into itself. They may send uncoloured individuals to coloured individuals.
- Arrows B->C are all globally surjective maps sending E_B into E_C.
- Arrows A->B and A->C are all globally surjective maps, with no colour restriction.
- There are no arrows in the other directions.

The symmetry group at A is its full permutation group; at B and C it consists of the permutations preserving E setwise. Every object carries the finite-set ideal. Interpret e by the base itself and interpret any optional relational constants by top.

Composition respects these definitions, so this is a category of functions with the required symmetry groups. Use the symmetric ideally-full domains. All finite prescriptions compatible with a colour restriction extend to a global surjection: the unprescribed uncoloured set remains countably infinite and can cover all still-required uncoloured targets, while any remaining coloured targets can be supplied by coloured or uncoloured source points as appropriate.

For a relation F at an object, with extension D at its identity, write B_N(D)_h for the union of h'D over arrows h' with h's target agreeing with h on N. A relation pinned by S is weakly rigid exactly when F=B_N(D) for every finite N⊇S. The proof is the usual weak-persistence/weak-inextensibility test and applies to this several-object category.

## 2. Boxed Barcan at every type

Every base arrow is surjective. At any relational type, transport is surjective as well: for an entity at the target pinned by a finite set N, choose finitely many preimages of N and pull its profile back along the resulting finite section, exactly as in the recorded `barcan-surjective` argument. In detail, at an outgoing source arrow l use the union of target-profile extensions over arrows k with k|N=l s; an empty union is allowed when there is no such k. After transport along the chosen arrow, the current k itself matches, and pinning makes all matching extensions identical.

Therefore every future entity is the image of a current entity at each type. The usual direct Barcan argument applies at every object, giving boxed BF at A, B and C. In particular the universal unary relation top_et is rigid at every object.

## 3. Tame Rigidity at the entrance A, at every relational type

Let F be weakly rigid at A, pinned by finite S and with extension D. If u:A->A fixes S, pinning and weak persistence give uD⊆D.

For any outgoing h:A->T and any tuple h'a in B_S(D)_h, let M pin the tuple a. The arrows h,h' are surjective and agree on S. Choose a root surjection u fixing S such that h u and h' agree on M: prescribe u(x)=x on S and choose h-preimages of h'(x) on M\S, then extend the finite prescription to a surjection. It follows that ua∈D and h'a=h(ua). Hence

    F_h=hD

for every outgoing arrow. The reverse inclusion is weak persistence.

Every root weakly rigid relation therefore has an exact-image profile. At any reached world, its extension after a further arrow is the image of its extension there. This directly gives persistence and weak inextensibility, hence full rigidity. Thus TR holds at A at all relational types, not just et.

## 4. The coloured unary relation is weakly rigid but not rigid at B

Define U at B to have extension E_B at every endomorphism of B and E_C at every arrow to C. It is symmetric and pinned by the empty set.

For any finite N and outgoing h from B, B_N(E_B)_h equals the coloured target set. One inclusion follows because every arrow preserves colour. For the other, choose a coloured source point outside N, prescribe its image to be the desired coloured target, preserve h on N, and extend to an allowed surjection. Therefore U=B_N(E_B) for every finite N: U is weakly rigid at B.

At C, its extension is the two-element E_C at every further arrow. The finite union H of the two individual haecceities is rigid and coextensive with U there. Choose a surjective m:C->C preserving E_C and merging its two members to c_0; the missing target c_1 is supplied by an uncoloured preimage. Then H has extension {c_0} after m, while U still has extension E_C. Hence U is not identical to H and cannot be weakly rigid at C. Thus U is not rigid at B.

Since all arrows are globally surjective, U is bounded by the rigid universal unary relation. This bounded failure is what the weak power property at A detects.

## 5. Classification of rigid unary relations at every object

We prove that every rigid unary relation has actual extension either finite or the whole individual domain. The converse holds: finite extensions have their finite haecceity unions, and the universal relation is rigid by boxed BF. A rigid relation with one of these extensions equals that canonical representative, because coextensive weakly rigid relations are identical.

Fix a rigid F pinned by finite S, with actual extension D. Enlarge S freely when needed. The extension D is invariant under every symmetry fixing S. Also, for every allowed endomorphism u fixing S, persistence and pinning give uD⊆D.

At A, the complement of S is one symmetry orbit. If D is infinite, it contains that orbit. An endomorphism fixing S can send one fresh member of D to any specified individual while remaining surjective, so uD⊆D forces D to be the whole domain. Otherwise D is finite.

At C, include E_C in S. The uncoloured complement of S is one infinite orbit. If D meets it, it contains all of it, and a surjection fixing S can send a fresh uncoloured member to any specified individual, while preserving E_C. Thus D is whole. If it does not meet that orbit, D is finite.

At B, the two infinite orbits outside S are E_B\S and the uncoloured complement of S. If D contains the uncoloured orbit, the same fresh-uncoloured-point argument makes D whole. If not, its uncoloured part K is finite. If D does not contain the coloured orbit either, it is finite. In the remaining case, fresh coloured points can be sent to any coloured target while fixing S, so every coloured individual belongs to D. Thus the only remaining candidate is

    D=E_B union K, with K finite and uncoloured.

This candidate cannot be the extension of a rigid F. For any incoming h:B->C, the B_N criterion with N containing K gives

    F_h=E_C union hK.

Indeed every fresh coloured source point can be sent to either target colour while preserving any finite prescription, and the images of K are fixed by N. Choose h with hK⊆E_C. Then F_h has finite extension E_C, so rigidity makes hF identical to the finite haecceity union of E_C. After a surjective m:C->C merging the coloured pair, it must have extension mE_C={c_0}. But the same displayed B_N formula at m h gives E_C union m hK=E_C. Contradiction.

Therefore the classification is proved at all three objects.

## 6. Boxed Rigid Power at et

At any object, let F be rigid, with extension D finite or whole. At a future arrow h, its extension is hD. A rigid subrelation X of hF has extension E⊆hD, with E finite or whole by section 5.

If D is finite, E is finite. Choose a finite preimage subset D'⊆D with hD'=E. Its finite haecceity union is a current rigid subrelation of F and transports to X, by coextensive-rigid uniqueness.

If D is whole, a finite E is lifted the same way, and the whole future extension is lifted by the current whole relation. Thus every future rigid subrelation of hF is the image of a current rigid subrelation of F; the reverse inclusion is automatic. The rigid-power property of F has an exact-image profile and is therefore rigid.

This holds at every object and proves boxed RP_et. No claim about RP at higher relation types is used or established.

## 7. Weakly Rigid Power at et fails at A

Let F be the universal unary relation at A and P(X):=WeakRigid(X) and X<=F. Every actual P-member is rigid by the full TR result of section 3, so every actual P-member necessarily satisfies the test Z(X):=Rigid(X).

At B, however, U from section 4 is weakly rigid, lies below the transported universal F, and is not rigid. Thus P does not entail Z. This violates weak inextensibility of P. Therefore WRP_et fails at A.

The result is an exact type-use obstruction to a proof of the full-schema conjecture: even TR at every type, boxed BF at every type and necessary RP_et together do not suffice for WRP_et. Any surviving proof must genuinely use higher Rigid Power instances, or another hypothesis absent here.
