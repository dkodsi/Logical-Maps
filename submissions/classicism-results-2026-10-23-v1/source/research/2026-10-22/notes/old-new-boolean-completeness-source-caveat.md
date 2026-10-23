# Audit caveat: the even-haecceity family is not admitted

22 October 2026. Independent mathematical audit by the choice lane, confirming the principles lane's objection. No existing record or source proof was edited. This diagnoses the stated witness, not the truth of Boolean Completeness in the construction.

## Exact source locations

* `topics/classicism/writeups/symmetric-old-new-individuals.md`, lines 45–57: symmetry and finite-pinning conditions defining the relational domains.
* The same writeup, lines 284–300: proposed failure of Boolean Completeness at et, using the external family {η_n:n even}.
* The same writeup, lines 304–308: later statement describing that family as infinite but not internally countable.
* `topics/classicism/models/symmetric-old-new-individuals.yaml`, lines 106–115: the corresponding `boolean-completeness-r` failure verdict, for `individuals: base`.
* `topics/classicism/principles/boolean-completeness-r.yaml`: the principle quantifies over admitted properties X^(τt), not arbitrary external subsets of a type domain.

All paths above are relative to `/Users/danielkodsi/Downloads/classicism-map`.

## Why no admitted property has the required actual extension

Let X be an admitted property of et-entities at E, pinned by the finite individual set S. Its actual extension X_1 must be invariant under every permutation g∈Sym(N) fixing S pointwise.

Indeed, for any et-entity Y, symmetry gives

    (Y,1_E)∈X iff (g·Y,g)∈X.

The reverse direction follows by applying symmetry with g^(-1). Since g and 1_E agree on S, finite pinning gives

    (g·Y,g)∈X iff (g·Y,1_E)∈X.

Consequently Y∈X_1 iff g·Y∈X_1. This is a necessary condition on the actual extension of every admitted property, independent of what its other arrow-indexed extensions might be.

For the haecceities η_n, transport is g·η_n=η_(g(n)). Given any finite S, choose an even n and an odd m outside S and let g interchange them, fixing every other individual. An actual family containing exactly the even haecceities would contain η_n but not g·η_n=η_m, contradicting the necessary invariance just proved. Hence **no admitted X has actual extension {η_n:n even}**.

The source's least-upper-bound argument can still correctly show that this external family has no supremum in the external order of admitted et-objects. It therefore witnesses external incompleteness of that Boolean algebra. It does not witness failure of the object-language Boolean Completeness schema, whose family parameter X must itself be admitted.

Nor can the issue be repaired by assigning the same desired actual extension a different behavior at future arrows: the contradiction used only symmetry, pinning, and the actual extension. The later statement that the family is not internally countable understates the issue: the required family object is absent already, before a countability label relation is considered.

## Exact consequence and limits

The displayed proof does not justify the listed BC-failure verdict. Any use of this model as a separator with ¬BC should be marked unsupported pending an alternative **represented** family or another argument. This audit does not prove that BC holds, does not invalidate the model construction, and does not challenge unrelated ND, Atomicity, Actuality, or inextensible-comprehension arguments merely by association.

In particular, replacing the even family by all haecceities is not an immediate repair. That family is symmetry-compatible and has the explicit upper bound which at arrows into E holds of every individual, and at arrows into O holds exactly of old individuals. The external range-of-the-arrow union is not automatically the algebraic least upper bound inside the admitted domain. A new failure proof must verify its family admission and its order-theoretic obstruction separately.

## Stronger positive result: the et instance of BC actually holds at E

Added by the principles lane, 22 October 2026. This is a new direct verification about the existing construction. It concerns exactly the relation type at which the recorded counterexample was claimed; the full all-type BC schema remains unproved here.

Write FC(N) for the finite/cofinite Boolean algebra of subsets of N. The Boolean algebra of admitted unary individual relations at E is order-isomorphic to

    FC(N) × FC(N) × 2.

Here is a complete classification. If F is pinned by a finite S, its identity extension A=F_(1_E) is invariant under every permutation fixing S, by the preceding argument. Therefore membership in A is constant outside S, so A is finite or cofinite with all its exceptional points in S.

Let i:E→O be the inclusion into the old individuals. The extension F_i is invariant under every old/new-preserving permutation fixing iS. Its old part is therefore a finite/cofinite subset B of N with exceptional points in S, and its new part is either empty or all of N'. Denote that last choice by c∈2.

These three data determine the entire intension. For h:E→E, extend h|S to a permutation g of N. Pinning gives F_h=F_g and symmetry gives F_g=gA. For h:E→O, choose an old/new-preserving permutation g of O whose restriction to iS agrees with h; then pinning and symmetry give F_h=F_(gi)=gF_i. Both formulas are independent of the extensions chosen, since A and F_i have the displayed stabilizer invariance.

Conversely, every triple (A,B,c) with A,B finite/cofinite defines an admitted F. Choose S containing the finite exceptional sets of both A and B. At an arrow into E, transport the finite exceptional set of A by that arrow, retaining A's generic outside-S truth value. At an arrow into O do the same with B on old individuals, and use c on all new individuals. These profiles are symmetric and pinned by S, so they are admitted. This also proves uniqueness of the triple classification.

Entailment is componentwise inclusion. Necessity implies inclusion at 1_E and i, hence on all three components. Conversely, to compare two triples, choose one S covering both finite exceptional sets. At any arrow use the same extending symmetry for both relations in the preceding formulas; componentwise inclusion then gives inclusion of their entire profiles.

Now let X be any admitted property of et-relations, pinned by a finite S_0. Its current extension A_X is invariant under Fix(S_0). Root permutation transport sends a triple (A,B,c) to (gA,gB,c). Therefore the external unions

    A_* = union { A : (A,B,c) belongs to A_X },
    B_* = union { B : (A,B,c) belongs to A_X }

are each invariant under Fix(S_0). They are consequently finite/cofinite, since Fix(S_0) acts transitively on the complement of S_0 in N. Put c_*=1 iff some current family member has c=1. The triple (A_*,B_*,c_*) is admitted and is the least upper bound of the family by componentwise inclusion. The empty family gives the bottom triple. Negation yields greatest lower bounds as well.

Thus **the Boolean Completeness instance at et holds at E**, even though the external et Boolean algebra is incomplete. Together with the separately verified ND and failure of IC at et, this gives a precise local separation: ND plus BC_et does not imply IC_et or RC_et. It does not yet settle ND plus the full BC schema versus RC, because higher relation types have not been classified by this argument.

## All-type strengthening: BC holds at E

The preceding unary argument extends to every permitted relational type. This strengthening was independently derived by the principles and root lanes on 22 October 2026. It supersedes the preceding section's temporary all-type reservation. The original record remains untouched.

Fix any τ=σ_1...σ_n t, including n=0, and write D_tuple(E), D_tuple(O) for the products of the already constructed argument domains at the two objects. No external fullness of those domains is assumed. Each symmetry is invertible and hence acts bijectively on these domains by the model's transport action.

**Pair classification.** An admitted F of type τ at E is determined by two subsets

    A=F_(1_E) ⊆ D_tuple(E),
    B=F_i ⊆ D_tuple(O),

where i:E→O is the old inclusion. If S is a finite pinning set for F, then A is invariant under Fix_E(S), and B is invariant under Fix_O(iS). The first follows by comparing a symmetry fixing S with the identity. For the second, if γ∈G_O fixes iS, the arrows γi and i agree on S, so pinning gives F_(γi)=F_i, whereas symmetry gives F_(γi)=γF_i. Notice that Fix_O(iS) includes every permutation of the new individuals, with the old individuals fixed.

For an arbitrary h:E→E, extend its finite partial injection h|S to g∈G_E. Then

    F_h=F_g=gA.

For h:E→O, its range is old. Extend h|S to γ∈G_O on the old coordinates (and arbitrarily, for example identically, on the new coordinates). Then

    F_h=F_(γi)=γB.

These formulas determine every profile, since these are all arrows out of E. They use only the finite partial-injection extension property of the individual symmetries, not a claim that h transports every higher-type object surjectively.

**Converse admission.** Suppose A and B are arbitrary metatheoretic subsets of the displayed tuple domains such that, for some common finite S, A is Fix_E(S)-invariant and B is Fix_O(iS)-invariant. Define F_h by the two formulas above. The definition is independent of the chosen extending symmetry: two choices differ by a symmetry fixing S or iS, respectively. It is pinned by S, since h|S determines the chosen-symmetry coset. It is symmetric, since postcomposing h with a target symmetry postcomposes the chosen extending symmetry and transports the displayed subset accordingly. Hence the ideally-full domain admits F by its literal defining conditions. This verifies the converse for every tuple type without adding any unavailable external subset as an entity: only the resulting symmetric finitely pinned intension is asserted to be admitted.

**Order.** F≤G iff A_F⊆A_G and B_F⊆B_G. One direction evaluates entailment at 1_E and i. For the converse take a common finite support S for both pairs, and use the same extending symmetry for both at each arrow. Inclusion is preserved by that symmetry's action, giving inclusion of every profile.

**Action on pairs.** If g∈G_E, let ĝ∈G_O act as g on old individuals and as the identity on new individuals. Then ig=ĝi. Root transport sends

    (A_F,B_F) ↦ (gA_F, ĝB_F),

because (g·F)_(1_E)=F_g and (g·F)_i=F_(ig). This identity uses the actual action on higher-type arguments, so it is valid at arbitrary types.

**Represented joins.** Let X be an admitted property of τ-entities at E, with finite pin N_0. Its actual extension S_X is invariant under Fix_E(N_0), by symmetry and pinning. Define external componentwise unions

    A_* = union_(F∈S_X) A_F,
    B_* = union_(F∈S_X) B_F.

The action-on-pairs formula shows A_* is Fix_E(N_0)-invariant, and B_* is invariant under the corresponding old-coordinate permutations fixing N_0. Each B_F is invariant under all new-coordinate permutations, because every support for an entity at E consists of old individual coordinates only. Hence their union B_* is invariant under all new-coordinate permutations as well. Every member of Fix_O(iN_0) is the product of such an old-coordinate permutation and a new-coordinate permutation. Thus B_* is Fix_O(iN_0)-invariant.

The converse classification therefore supplies an admitted τ-relation J with pair (A_*,B_*), pinned by N_0. The order classification says exactly that J is an upper bound of all current X-members and lies below every other current upper bound. Thus J is their LUB. Empty families are covered by empty unions. Boolean complementation gives the GLB form.

This proves **the full Boolean Completeness schema at E**, for every permitted relation type, including t and higher-type arguments.

## Consequence: ND + BC does not imply RC or IC

The same existing model has ND at E by the recorded finite-invertibility proof (`symmetric-old-new-individuals.md`, section “ND at E”): every outgoing arrow can be followed so as to recover any prescribed finite root behavior, which preserves distinctness of finitely pinned entities. Its individual arrows are injective. This proof is independent of the invalid BC-failure argument.

Its recorded IC failure at et is likewise independent and direct. If Y is coextensive with the universal individual property and inextensible, finite pinning and symmetry force Y to hold of every individual at every arrow into E. Current weak inextensibility, tested against the property of being old, forces Y_i to contain only old individuals at O. Fix a new individual b there. Every Y_i-member is necessarily distinct from b, because all individual arrows are injective. Weak inextensibility at i would therefore entail the property λx.x≠b. But any return arrow m:O→E makes Y_(mi) universal, so it contains m(b), whereas that transported inequality fails there. This contradiction refutes IC_et and consequently RC_et.

Consequently this fixed-framework model establishes

    C + ND + BC + ¬IC_et + ¬RC_et.

In particular ND+BC does not imply IC, TR, or RC: BC+ND gives WeakRC by already recorded consequences, while TR+WeakRC gives RC. This result leaves intact the newly proved positive theorem ND+IC⇒WRP and shows that its IC premise cannot simply be replaced by BC.

The construction itself and its ND/IC verdicts are previously recorded. The all-type BC verification and resulting corrected separation are new arguments from this research session (`misc`), not results attributed to Dorr or the earlier recorded authors. No database record has been modified, and no formal-verification status is claimed.
