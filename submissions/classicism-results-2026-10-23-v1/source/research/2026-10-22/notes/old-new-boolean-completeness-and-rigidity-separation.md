# Old/new model: Boolean Completeness and the rigidity separation

Research theorem and correction audit, 22 October 2026. Ordinary mathematical proof in the fixed relational framework C. The new all-type BC argument and corrected future BC failure have direct source `misc`; no claim of literature novelty, human checking, or formal verification is made. The existing database remains unchanged.

## The result

At its original evaluation object E, the recorded symmetric ideally-full old/new model satisfies ND and the full Boolean Completeness schema, but fails Inextensible Comprehension and Rigid Comprehension already at et. At its accessible object O, BC fails already at et. Thus

    C + ND + BC does not imply IC, RC, or TR,
    and this model satisfies BC but not boxed BC.

The TR conclusion uses the already recorded ND+BC⇒WeakRC and TR+WeakRC⇒RC. Its separately recorded boxed Rigid Power also makes this a model of ND+BC+boxed RP+not TR; that stronger statement depends on that separate RP proof.

## Exact construction and owning sources

The construction is unchanged from `topics/classicism/models/symmetric-old-new-individuals.yaml` and `topics/classicism/writeups/symmetric-old-new-individuals.md`, relative to `.`.

The two objects are E=N and O=N disjoint-union N', with old and new individuals at O. Arrows E→E are all injections; E→O are all injections with old range; O→E are all injections; O→O are the old/new-preserving permutations G_O together with all injections whose range is old. Root symmetries G_E are all permutations of N; O symmetries are G_O. The ideal at each object is the finite subsets. Evaluate at 1_E. All arrows are injective and the displayed arrows are closed under composition.

At each relational type, the domain contains exactly the symmetric finitely pinned intensions. An intension F at W is symmetric when F_(gh)=g F_h for every target symmetry g. It is pinned by a finite S⊆W when h|S=h'|S, for arrows with the same target, implies F_h=F_h'. Individual arguments use the displayed domains and arrow actions; higher arguments use the recursively constructed domains and transport. These are the literal owning definition at writeup lines45–57. No extra naturality condition along arbitrary noninvertible arrows is imposed.

The model's ND proof is in the writeup's ND section; its IC failure is in “Inextensible Comprehension fails (corrected).” The old BC failure argument at lines284–300 uses the external even-haecceity family, which is not admitted. The chronological audit `old-new-boolean-completeness-source-caveat.md` proves that defect separately: an admitted root family must have an actual extension invariant under all permutations fixing a finite set, whereas the even-haecceity family does not. The positive BC proof below supersedes that failure verdict mathematically, without modifying the record.

## Full Boolean Completeness at E


The following proof applies to every permitted relational type. It was independently derived by the principles and root lanes and independently audited by the choice and rigidity lanes on 22 October 2026. The original record remains untouched.

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

The same existing model has ND at E by the recorded finite-invertibility proof (`symmetric-old-new-individuals.md`, section “ND at every type at E”). Here is the full check. Given f:E→V, h:E→U and a finite root set S, prescribe k(f(s))=h(s) for s∈S. Injectivity makes this a consistent finite partial injection. If V=U=E, extend it to an injection E→E. If V=E,U=O, extend it to an injection into the old individuals. If V=O,U=E, extend it to an injection O→E. If V=U=O, extend it to an injection O→O with old range, which is a permitted K-arrow. Thus in every case kf agrees with h on S.

For distinct root relations F,G, take S pinning both and a tuple a at some target U with different truth values in F_h and G_h. For each outgoing f, choose k as above. Pinning gives F_(kf)=F_h and G_(kf)=G_h, so their transports f·F and f·G still differ at the tuple a and arrow k. Hence every outgoing arrow preserves their inequality. This works for arbitrary higher-type argument tuples because pinning compares exactly the same target tuple. Individual inequality is preserved because all individual arrows are injective. Therefore ND holds at every permitted type at E, independently of the invalid BC-failure argument.

Its recorded IC failure at et is likewise independent and direct. If Y is coextensive with the universal individual property and inextensible, finite pinning and symmetry force Y to hold of every individual at every arrow into E. Current weak inextensibility, tested against the property of being old, forces Y_i to contain only old individuals at O. Fix a new individual b there. Every Y_i-member is necessarily distinct from b, because all individual arrows are injective. Weak inextensibility at i would therefore entail the property λx.x≠b. But any return arrow m:O→E makes Y_(mi) universal, so it contains m(b), whereas that transported inequality fails there. This contradiction refutes IC_et and consequently RC_et.

Consequently this fixed-framework model establishes

    C + ND + BC + ¬IC_et + ¬RC_et.

The failure of TR also has an explicit witness. Let U have extension all individuals at arrows into E and exactly the old individuals at arrows into O. The pair classification identifies U as the LUB of the admitted family of all current individual haecceities: their E-components union to all E and their O-components union to all old O. A join of the current tuple haecceities is weakly rigid (its upper-bound and leastness clauses give weak persistence and weak inextensibility directly). At i, however, its current members are all necessarily distinct from a new b, while after a return m it contains m(b). Thus U is not rigid. This explicitly exhibits the failed preservation of an existing join of rigid relations.

In particular ND+BC does not imply IC, TR, or RC: BC+ND gives WeakRC by already recorded consequences, while TR+WeakRC gives RC. This result leaves intact the newly proved positive theorem ND+IC⇒WRP and shows that its IC premise cannot simply be replaced by BC.

The construction itself and its ND/IC verdicts are previously recorded. The all-type BC verification and resulting corrected separation are new arguments from this research session (`misc`), not results attributed to Dorr or the earlier recorded authors. No database record has been modified, and no formal-verification status is claimed.

## Failure of BC at O


Let D be the individual predicate at O whose extension at every arrow into E is all E-individuals, and whose extension at every arrow into O is exactly the old individuals. This is symmetric under the target symmetry groups and pinned by the empty set: its extension depends only on the target. At 1_O its extension is the old individuals.

Let η_x=λy(y=x), the available haecceity operation, and define

    X(F) := exists x (D(x) and F=η_x).

This is an admitted property by C comprehension. Its actual extension at 1_O is exactly {η_n:n old}. There is no external-family gap: alternatively, its arrow extension consists of the haecceities of all individuals at target E, and of the old individuals at target O, which directly verifies symmetry and empty pinning. Equality of individual haecceities is exactly equality of their individual parameters.

## No least upper bound

Suppose L were a least upper bound of that current family, and let finite S⊆O^e pin L. Choose an old n outside S and a new m outside S. Fix any injection h:O→E.

There is an injection h':O→E agreeing with h on S and satisfying h'(n)=h(m). Indeed h(m) is outside h(S), since m∉S and h is injective; this is a consistent finite partial injection, extendible to an injection from the countable source into E.

Since η_n≤L, the instance L(h'(n),h') holds. Thus L(h(m),h') holds. Pinning by S and h'|S=h|S then give L(h(m),h).

But the admitted predicate

    Q_m(y,k) iff y≠k(m)

is an upper bound of every old haecceity η_a: a≠m, and every arrow is injective. It is symmetric and pinned by {m}, or simply the C term λy(y≠m). It fails at (h(m),h). Therefore L is not below this upper bound, contradicting leastness.

So the et instance of BC fails at 1_O. Since O is reachable from E, □BC_et fails at the original evaluation point 1_E.


## Checks, exact scope, and the positive boundary

The all-type pair classification and represented-union proof were independently derived by root and principles, then independently checked by choice and rigidity against the literal domain definition. The corrected O counterfamily was independently found by choice and principles and independently found again by rigidity; its admission and finite-prescription argument were checked. The ND and IC arguments were rechecked directly and do not depend on the withdrawn BC witness.

The newly proved theorem ND+IC⇒WRP is in `nd-inextensible-comprehension-implies-weak-power.md`. Combined with recorded arrows, it gives the exact equivalence over ND+BC:

    IC ⇔ RC ⇔ TR ⇔ WRP.

Indeed IC gives WRP by that theorem, WRP gives TR, TR plus WeakRC gives RC, and RC gives IC; ND+BC already gives WeakRC. The model here shows these equivalent additional conditions are not automatic. Its separately recorded boxed RP does not suffice to reach them.

This proof neither changes the fixed language nor invokes external fullness of the higher-type tuple domains. External unions occur only in the metatheoretic construction of a symmetric finitely pinned intension, whose admission is then proved. This is precisely the distinction that the earlier even-family counterargument failed to respect.
