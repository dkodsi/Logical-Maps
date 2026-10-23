# One actual-world kernel for evaluator uniqueness and quantifier laws

22 October 2026. Ordinary mathematical refinement by OpenAI Codex; direct source `misc`. No independent or formal verification claim. Originals: [actual-truth evaluator ladder](../notes/actual-truth-evaluator-ladder.md), [Gallin evaluator, §§3–5 and 7](../notes/gallin-bivalent-evaluator.md), and [atom-local evaluator criterion, §24](../notes/structural-world-representation.md#24-the-exact-bare-c-condition-an-atom-local-barcan-law).

## Exact improvement

The Gallin note proves uniqueness and current typed quantifier commutation using globally bivalent outputs and persistent-falsity arguments. Both proofs can instead use one actual-world kernel.

More precisely, **ordinary bivalent actual-truth evaluation already supplies a canonical replacement commuting with every current typed quantifier**. Global bivalence is needed to identify an arbitrary original evaluator with that replacement, not to construct it. This strictly lowers the assumptions of the **existence** formulation; it does not assert the stronger equations for every ordinary evaluator witness.

Write

    Eval(E) := ∀p[(p→Ep=⊤) ∧ (¬p→Ep=⊥)],
    Global₂(E) := □∀p(Ep=⊤ ∨ Ep=⊥).

All equalities below are proposition or operation identities. Outer quantifiers over input predicates remain unboxed unless expressly stated. Types are the fixed relational types; no quantification over types is introduced.

## 1. The kernel and its canonical evaluator

Assume Eval(E), and define the admitted terms

    w_E := ∀p(Ep↔p),
    C(E) := λq. □(w_E→q).                                    (1)

The proposition w_E is true now. If q is any current truth, Eq=⊤, and NI preserves that endpoint identity. Necessary universal instantiation of w_E therefore gives □(w_E→q). Thus w_E is an Actuality witness: a true proposition entailing every current truth. In particular it is an atom, since for each current q either q or ¬q is a truth it entails.

Moreover Eval(E) applied to the currently true w_E gives E(w_E)=⊤, while E(⊥)=⊥. NI preserves both equations. If w_E ever became identical to ⊥, substitution would equate the two endpoints. Hence

    □◇w_E.                                                  (2)

This obtains a persistently possible actual world directly, without first deriving the full ND schema.

For any such world w, put E_w(q)=□(w→q). If q is currently true, Actuality gives w≤q; this box formula is necessary by 4, so E_w(q)=⊤. If q is false, w≤¬q. At every successor this entailment persists, and w remains possible by (2); consequently w≤q cannot hold there. Thus E_w(q)=⊥. We have proved Eval(C(E)).

Actuality witnesses are unique: if w,v are true and each entails every current truth, then w≤v and v≤w. Consequently all ordinary Eval witnesses have the same kernel, and

    Eval(E) ∧ Eval(E′) → C(E)=C(E′),
    Eval(E) → C(C(E))=C(E).                                  (3)

The equalities follow by substitution of the identical kernels into (1), not by an unlicensed inference from pointwise agreement of operations. Every current value of C(E) equals the corresponding current value of E, since both evaluate truth into the same endpoints. It does not follow that E=C(E).

### A one-pair stability criterion

The same construction gives a shorter hypothesis on an initially arbitrary truth classifier. Put

    TF(f) := ∀p[p ↔ f(p)=f(⊤)].

Then, over C,

    ∃f[TF(f) ∧ □(f(⊥)≠f(⊤))] iff ∃E Eval(E).                (3a)

No bivalence of the original f is required: only its two displayed outputs are required to remain distinct. To prove the forward direction put v:=∀p(f(p)=f(⊤)→p). TF makes v true. For any current truth q, f(q)=f(⊤); NI and the necessary q-instance of v give v≤q. Thus v is the actual world. Since v is true, TF also gives f(v)=f(⊤), an identity preserved by NI. If v became ⊥, this identity would contradict the assumed necessary distinction between f(⊥) and f(⊤). Therefore □◇v, and §1's construction E_v supplies Eval and all the quantifier laws below.

Conversely an Eval witness has TF, sends ⊥ and ⊤ to those distinct endpoints, and NI together with their logical necessary distinction gives the boxed inequality. This proves (3a). TF alone is the original ladder's Actuality level; the one additional boxed output inequality supplies exactly the stability needed for normalized evaluation. It is not a claim that an arbitrary f itself becomes bivalent or satisfies the evaluator identities.

## 2. Actuality already supplies every current atom-local Barcan law

For a true Actuality witness w and every fixed input type σ,

    ∀F^(σt) [(∀x^σ w≤Fx) → w≤∀x^σ Fx].                      (4)

Indeed w is true, so the premise makes every current Fx true. The current universal ∀xFx is therefore true, and Actuality places it above w. This argument needs neither ordinary BF nor persistent nonzeroness of w. It is a relative law at the actual world, not BF_σ for arbitrary propositions.

This elementary observation is what the canonical evaluator needs. It is already implicit in the old atom-local criterion, but making it explicit removes the repeated global-bivalence machinery from the current-quantifier argument.

## 3. Literal quantifier commutation for the canonical replacement

Let w=w_E, and fix a current F:σt. Put U=∀xFx and Q=∀xE_w(Fx). Their current truth values agree, because Eval(E_w) holds. The proposition E_w(U) is an endpoint. To prove its identity with Q, it remains to prove that Q is the same endpoint.

If Q is true, (4) gives L:=□(w→U). The C theorem

    □(w→∀xFx) → ∀x□(w→Fx)

is ordinary necessary universal instantiation, not BF. Necessitate this theorem, and use 4 on L. It gives □Q, so Q=⊤. If Q is false, some current x has E_w(Fx)=⊥. NI preserves that identity; this fixed witness keeps Q false at every successor. Hence Q=⊥. Thus

    E_w(∀x^σ Fx) = ∀x^σ E_w(Fx).                             (5)

For the existential, put V=∃xFx and R=∃xE_w(Fx). If R is currently true, a current top-valued witness and NI make R necessary. If R is false, V is false and Actuality gives w≤¬V. At any successor, a putative witness of R would give both □(w→Fx) and □(w→¬Fx) there, the latter by necessary universal instantiation of w≤¬∃xFx. This contradicts the continuing possibility of w. Therefore □¬R. Again R and E_w(V) are the same endpoint, proving

    E_w(∃x^σ Fx) = ∃x^σ E_w(Fx).                             (6)

This direct existential argument avoids silently putting the merely current Boolean laws of E_w under a future quantifier.

The single term C(E) works for each fixed type σ, with no separate selection of an evaluator by type. Equations (5)–(6) hold for every **current** F and, by NI, persist for each such F. They do not establish □∀F of those equations, which would also cover future predicates absent now.

## 4. Global bivalence identifies the original witness

Now suppose also Global₂(E). We show E=C(E), which yields the original Gallin quantifier theorem for this very E and proves its uniqueness by (3).

At any accessible point, let q be any proposition there. Its E-value is an endpoint. The defining universal w_E=∀p(Ep↔p) gives the necessary instance w_E→(Eq↔q). If Eq=⊤, NI and this instance give w_E≤q. If Eq=⊥, they give w_E≤¬q. Since w_E remains possible, the two cases are exclusive. They imply, respectively, E_(w_E)(q)=⊤ and E_(w_E)(q)=⊥, by the same persistence argument as in §1.

Therefore necessarily, for every future q, Eq=E_(w_E)(q). Intensionality gives the literal operation identity

    Eval(E) ∧ Global₂(E) → E=C(E).                            (7)

There is no use of BF or of necessitation under an unboxed optional premise: the future argument uses the expressly boxed range condition, the boxed persistence (2), and necessary instances of the definition of w_E.

The same argument shows that w_E is an atom at every successor. At any such point, its principal truth test necessarily preserves Boolean endpoints and finite Boolean operations: a nonzero atom decides negation, and w≤p∧q iff w≤p and w≤q. Hence the original **necessarily universal finitary Boolean laws** for a Gallin evaluator also follow from this kernel description. No corresponding future quantifier law is inferred.

Thus one kernel lemma replaces the separate persistent-disagreement and persistent-falsity proofs of uniqueness, current quantifier commutation, and finite Boolean structure. Global bivalence has an exact remaining role: equation (7).

## 5. Strict scope and the simpler unnormalized operator

Over C the existence of an ordinary Eval witness is therefore equivalent to the existence of an Eval witness satisfying all the current-typed laws (5)–(6). The same canonical operation satisfies every fixed type instance. This is the level ND+Actuality of the existing ladder, strictly below Gallin Comprehension.

A proved-only Engine separation query, with `distinctness-necessary-r` and `actuality` in the queried premises and an empty background, returns `full-two-object-double-retraction` as a separator from `gallin-extensional-comprehension-r`. Its existing record attributes the model to Cian Dorr, 6 October 2026. The theorem above supplies the canonical quantifier-preserving evaluator there; no new model or changed verdict is needed. Arbitrary original Eval witnesses need not preserve the literal quantifier identities: the original world-representation note, §27, explicitly supplies such a failing witness. Canonical replacement is essential.

There is an even simpler **unnormalized** operator P_w(p)=w∧p. C itself proves

    P_w(∀xFx)=∀xP_w(Fx),
    P_w(∃xFx)=∃xP_w(Fx),

by distribution of a scalar independent of x through quantification; the universal equation uses the standing nonempty types. These are logical identities and can be universally closed and necessitated. Under Actuality, P_w takes current values ⊥ and w and its top fibre records truth. It sends ⊤ to w, however, and w may vanish. It is not the normalized top/bottom evaluator required by Eval. This explains why those stronger-scope scalar identities do not settle the open boxed-quantifier question for normalized Gallin evaluators.

Sources: original evaluator ladder, levels 1–3; `gallin-bivalent-evaluator.md`, §§3–5, 7, 10; `structural-world-representation.md`, §§24 and 27. These are unpaginated local research notes. Background C Intensionality and NI are the recorded Classicism results (draft 16 May 2023, §1.5, pp. 17–18; §2.1, p. 22). The refinement reorganizes and strengthens the existence formulation of these existing arguments; it is not a claim of literature novelty or a resolution of the archived boxed-quantifier question.
