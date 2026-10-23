# Necessary distinctness and Inextensible Comprehension imply Weakly Rigid Power

Research theorem, 22 October 2026. Original derivation in the principles lane; independently audited by the root and rigidity lanes, including the weakening from Rigid to Inextensible Comprehension. No database edits or formal verification. Literature novelty unchecked; direct source category misc.

## The theorem and its exact type scope

Over fixed C,

    ND + Inextensible Comprehension ⇒ Weakly Rigid Power.

More precisely, for each relational type τ=σ̄t,

    ND_t + IC_(τt) ⇒ WRP_τ.

Here IC_(τt) supplies inextensible coextensions of properties of τ-relations. This implies the previously proved ND+RC⇒WRP, since rigid relations are inextensible. The current proved-only Engine derives neither theorem. Under ND+IC it derives Actuality, but not BC, WeakRC, Plenitude or RC; none of the latter are assumed in the proof.

ND_t supplies ND at every type: for current a≠b, p:=(a=b) differs from top; ND_t makes that difference necessary. Any future a=b would make p=top by NI, contradiction.

No ND, IC, TR or RP assumption is moved under a box. All future applications below use either C theorems or properties explicitly established as necessary.

## 1. ND forbids a new persistent truth

If p is persistent, meaning □(p→□p), and currently false, then p≠top. ND_t gives □(p≠top), or □¬□p. Combining with persistence gives □¬p. This elementary observation is the modal step closing the proof.

## 2. A persistent, necessarily separated relation equals any inextensible coextension

Let P be a persistent relation of any relational type. Assume necessarily that distinct current P-tuples remain distinct; abbreviate this as □ND_P. Let G be inextensible and currently coextensive with P.

Every current G-tuple necessarily satisfies P, by current coextension and persistence of P. WI(G) gives G≤P.

At any reached world, suppose P(ā) and ¬G(ā). Each current G-tuple b̄ lies in P and differs from ā, so □ND_P gives □b̄≠ā. WI(G), available at this world because G is inextensible, gives □¬G(ā). Persistence of P already gives □P(ā). Consequently any witness to

    q := ∃ā(P(ā)∧¬G(ā))

remains a witness at every later world. Hence □(q→□q). Current coextension gives ¬q; section 1 gives □¬q. Thus P≤G. With G≤P, obtain P=G. Since P is persistent and G inextensible, P is rigid.

Only inextensibility of G was used. This is why the stronger RC premise can be removed.

## 3. A current weakly rigid relation is necessarily internally separated under ND

If P is weakly rigid, so is P×P. Weak persistence is immediate. For WI, apply WI(P) first to the second variable and then to the first, exactly as for ordinary product rigidity. This argument uses only the current weak-rigidity assumptions.

Each current P-pair satisfies

    D(ā,b̄):=□(ā=b̄)∨□(ā≠b̄)

by NI and current ND. D is persistent by 4. WI(P×P) therefore gives (P×P)≤D, hence □ND_P.

IC at the type of P provides an inextensible coextension G. The relation P is persistent, as every weakly rigid relation is in C. Section 2 now gives P=G and proves P rigid. Therefore

    ND_t + IC_τ ⇒ TR_τ.

This does not infer TR from ND alone. The recorded symmetric old/new individuals model has ND and fails TR; it fails IC as required.

## 4. The family of rigid subrelations has necessarily separated members

Fix a rigid F of type τ. Section 3's product argument gives □ND_F; it needed only weak rigidity, which F has.

At any reached world let distinct rigid X,Y≤F be given. Coextensive weakly rigid relations are identical in C, so X,Y differ on a current tuple ā. Suppose X(ā) and ¬Y(ā). Positive X-membership is necessary. Every current Y-tuple is an F-tuple different from ā, hence necessarily different by ND_F. WI(Y) gives □¬Y(ā). Thus □X≠Y. The reversed membership case is the same.

Accordingly the property

    R_F(X):=Rigid(X)∧X≤F

has □ND_R_F. It is persistent, since rigidity and necessary containment are persistent properties. IC_(τt) gives it an inextensible current coextension. Section 2 makes that representative equal to R_F and hence makes R_F rigid. Therefore

    ND_t + IC_(τt) ⇒ RP_τ.

## 5. Inextensible Comprehension descends one property type

For any X of type τ, form its current singleton family

    J(X)(Y):=∃ā(X(ā)∧Y=δ_ā).

By IC_(τt), choose an inextensible G currently coextensive with J(X). Every current G-member is a tuple haecceity and hence rigid. Rigidity is persistent, so WI(G) gives G≤Rigid. More explicitly, singletonhood itself is persistent: a current witness ā to Y=δ_ā remains a witness by NI. Thus WI(G) also seals G≤Singletons. This is the necessary containment needed when transporting the union construction.

Define u(G)(ā):=∃Y(GY∧Y(ā)). At every reached world, G is weakly inextensible and its current members are rigid. A test necessary on every current union-instance bounds each current G-member by that member's WI; WI(G) then bounds the union. Hence u(G) is inextensible. At the initial world it is coextensive with X, because G and J(X) are coextensive. Thus

    IC_(τt) ⇒ IC_τ.

The same argument with only current WI proves the analogous descent for Weak Inextensible Comprehension. The stronger boxed conclusion in the IC case comes from G's inextensibility and the sealed singleton/rigidity containment, not from boxing current coextension.

## 6. Bounded propagation supplies weak power

Under ND, any future weakly rigid X below an actual rigid F is rigid. For completeness, □ND_F was proved in section 3. At a reached world, every current F-tuple has its X-membership decided: positive membership is necessary; for a tuple outside X, WI(X) with the complement of its haecceity and ND_F makes nonmembership necessary. The decision predicate is persistent, so WI(F) propagates it to every future F-tuple.

At any later world, let Z be necessary on all current X-tuples. Each current F-tuple either belongs to X and necessarily satisfies Z, or necessarily fails X. Thus every current F-tuple necessarily satisfies X→Z, and WI(F) gives X≤Z. This establishes WI(X) everywhere; X is already persistent, so it is rigid.

Now IC_(τt) gives IC_τ by section 5, hence TR_τ by section 3. A current weakly rigid F is therefore rigid. Its weak-power family P_F(X):=WeakRigid(X)∧X≤F agrees necessarily with R_F by bounded propagation. Section 4 proved R_F rigid, so P_F is rigid and in particular weakly rigid. This proves WRP_τ.

## Further exact consequences and boundaries

Under ND+IC, for every relation F,

    Rigid(F) iff Persistent(F) ∧ □ND_F.

The forward direction is persistence plus section 3; the reverse uses an IC representative in section 2. No RC assumption is needed for this characterization.

Combining the theorem with existing arrows also gives ND+IC+WeakRC⇒RC (use the new TR and the recorded TR+WeakRC⇒RC), and thus ND+IC+BC⇒RC using the recorded ND+BC⇒WeakRC. Neither BC nor RC has been derived here from ND+IC alone.

The unrestricted TR+RP⇒WRP question remains open. The theorem is a substantive sufficient condition using a comprehension principle; it is not a proof of that unrestricted implication. The colour-collapse model in `/tmp/classicism-research/colour-collapse-entrance.md` separately shows that TR(all types)+boxed BF(all types)+boxed RP_et does not suffice for WRP_et, so higher-type assumptions in the local theorem are essential to its method.

### Exact classification over ND + BC

The corrected old/new-model audit in `old-new-boolean-completeness-source-caveat.md` proves full BC at its original evaluation object E, contrary to the existing verdict's inadmissible external-family argument. Together with its independently verified ND and failure of IC_et, this is a countermodel to ND+BC⇒IC or RC. The IC premise of the present theorem therefore cannot simply be replaced by BC. Its future object O fails BC_et by the represented old-haecceity family in `old-new-necessary-bc-failure.md`.

Over ND+BC, the following all-type principles are equivalent:

    IC  ⇔  RC  ⇔  TR  ⇔  WRP.

Indeed ND+BC gives WeakRC by recorded results. The present theorem gives IC⇒WRP; the recorded arrows give WRP⇒TR and TR+WeakRC⇒RC; finally RC⇒IC is immediate. In contrast, RP alone does not reach this equivalence class even over ND+BC: the same old/new model has recorded boxed RP and fails TR. This last stronger model comparison depends on the separate recorded boxed-RP proof, not on the BC correction.
