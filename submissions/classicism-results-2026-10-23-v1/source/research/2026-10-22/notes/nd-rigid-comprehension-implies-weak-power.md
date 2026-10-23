# Necessary distinctness and Rigid Comprehension imply Weakly Rigid Power

**Stronger subsequent result:** `/tmp/classicism-research/nd-inextensible-comprehension-implies-weak-power.md` weakens Rigid Comprehension to Inextensible Comprehension, with an independently audited proof. This file preserves the earlier special case and its definition ladder.

Research proof, 22 October 2026. Original derivation in the principles lane, independently audited by the root and rigidity lanes. No database edits, formal verification, or literature novelty claim. Direct source category misc. The existing proved-only Engine does not derive the implication from the current records.

## Exact statement

Over fixed Classicism C,

    ND + Rigid Comprehension ⇒ Weakly Rigid Power.

The sharper type-local theorem is

    ND_t + RC_(τt) ⇒ WRP_τ

for every relational type τ=σ̄t. Here RC_(τt) concerns properties OF τ-relations. ND_t implies necessary distinctness at every type: if current a≠b, the proposition p:=(a=b) differs from top; ND_t makes this necessary, whereas any future a=b would, by NI, make p=top. Thus no separate argument-type ND assumptions are needed.

This resolves the ND case of TR+RP⇒WRP by a stronger route: RP itself follows from ND+RC. It does not settle unrestricted TR+RP⇒WRP, nor any single-type version lacking the higher comprehension instance.

## 1. Two elementary rigidity lemmas

For a rigid F of type τ, its product F×F on pairs of argument tuples is rigid. Persistence is immediate. For WI at any reached world, a test necessary on all current F-pairs is first universalized over the second F-tuple using WI(F), then over the first using WI(F). This proves the necessary bound without BF.

Write ND_F for necessary distinctness of current F-tuples. At the starting point ND gives ND_F. Each current F-pair satisfies

    D(ā,b̄):=□(ā=b̄)∨□(ā≠b̄),

using NI and ND_F. D is persistent by 4. WI(F×F) therefore makes D hold of every F-pair at every reached world. In particular □ND_F.

A second useful lemma is that coextensive weakly rigid relations are identical. Each has necessary positive membership, so WI of the other yields each inclusion. This is a C theorem and may be used at future worlds without assuming necessary TR or necessary RC.

## 2. Rigid subrelations of F are necessarily distinct

At any reached world let X,Y be distinct rigid subrelations of F. The preceding uniqueness lemma shows that they differ on a current tuple ā. Suppose X(ā) and ¬Y(ā); the other case is symmetric. Then ā∈F, and □X(ā) by persistence.

Every current Y-tuple b̄ belongs to F and differs from ā. The necessary ND_F gives □b̄≠ā. Applying WI(Y) to the test b̄≠ā yields □¬Y(ā). Hence X and Y cannot become identical. Therefore, at every reached world,

    Rigid(X)∧X≤F∧Rigid(Y)∧Y≤F∧X≠Y ⇒ □X≠Y.

This is necessary internal distinctness of the family R_F(X):=Rigid(X)∧X≤F. It applies to genuinely new future subrelations too, because it was derived inside each reached world from the necessarily available ND_F and the rigidity of X,Y there.

## 3. A rigid representative of the power family is the power family

Use RC_(τt) to choose a rigid G currently coextensive with R_F. Each current G-member necessarily satisfies R_F: rigidity is persistent, and containment is a necessary identity/order assertion. WI(G) therefore gives G≤R_F.

Consider an arbitrary reached world with R_F(Y) and ¬G(Y). Every current G-member X belongs to R_F and differs from Y, so section 2 gives □X≠Y. WI(G) applied to λX.X≠Y gives □¬G(Y). The other conjunct R_F(Y) is already necessary. Thus any witness to

    q := ∃Y(R_F(Y)∧¬G(Y))

remains a witness at every later world. This proves □(q→□q).

But q is false at the starting point, by the chosen coextension. Hence q≠top; ND_t gives □(q≠top), that is □¬□q. Together with □(q→□q), this yields □¬q. Therefore R_F≤G. Combining with G≤R_F gives R_F=G, so R_F is rigid.

This proves RP_τ for the arbitrary rigid F. The only comprehension used in the power argument is the single higher instance RC_(τt), evaluated at the starting point. It is never boxed.

## 4. From rigid power to weakly rigid power

First RC_(τt) implies RC_τ. Given F, code its current tuples by their rigid haecceities, J(F)(X):=∃ā(F(ā)∧X=δ_ā). Choose a rigid family K coextensive with J(F). Its current members are rigid haecceities; WI(K) makes that remain true of every future member. The union u(K)(ā):=∃X(KX∧X(ā)) is rigid, by applying WI first to its members and then to K. It is currently coextensive with F. Thus RC_τ holds, and uniqueness of coextensive weakly rigid relations gives TR_τ.

Second, ND gives bounded propagation of tameness: every future weakly rigid X≤F, for current rigid F, is rigid. Here is the direct proof. Section 1 gives □ND_F. At a reached world, for each current F-tuple ā, positive X-membership is necessary. If ¬X(ā), each current X-tuple is necessarily distinct from ā by ND_F, and WI(X) gives □¬X(ā). The persistent decision predicate □X(ā)∨□¬X(ā) therefore holds of all current F-tuples; WI(F) propagates it to all future F-tuples.

At any later world let Z be necessary on every current X-instance. A current F-tuple either belongs to X and necessarily satisfies Z, or necessarily fails X. Thus every current F-tuple necessarily satisfies X→Z. WI(F) yields X≤Z. This establishes WI(X) at every later world; X was already persistent, so X is rigid.

Finally take a current weakly rigid F. TR_τ makes F rigid. The weak-power family P_F(X):=WeakRigid(X)∧X≤F agrees necessarily with R_F by bounded propagation. Section 3 proved R_F rigid, so P_F is rigid, hence weakly rigid. This is WRP_τ.

## 5. A reusable criterion behind the proof

The power argument is an instance of a more general lemma. Assume ND_t. Let P be persistent and have necessarily internally distinct members. If it has a rigid current coextension G, then P=G and P is rigid.

Indeed WI(G) gives G≤P, since current G-members necessarily satisfy P. At any future world, a P-member outside G is necessarily distinct from every current G-member; WI(G) makes its nonmembership in G necessary. Therefore the difference has a persistent existential witness. Its existential proposition is currently false, so ND_t rules out its becoming true. Thus P≤G as well.

Consequently, under ND+RC, rigidity of a relation F is equivalently persistence together with necessary internal distinctness of its members. The forward direction uses section 1; the reverse direction uses this criterion with an RC representative. In the power theorem, P=R_F is automatically persistent and section 2 supplies its necessary internal distinctness.

## 6. The modal/rigidity definition ladder

These are explanatory equivalences, not separate novelty claims.

- ND is equivalent to every persistent proposition being top or bottom. A currently true persistent proposition is top. A currently false one cannot become true under ND_t, since a future truth would become necessary. Conversely equality propositions are persistent by NI, so this property makes current inequalities necessary.
- Equivalently, at any one fixed relational type, no nonzero persistent relation is actually empty. Existential projection of a persistent relation is persistent; the converse uses constant relations to encode propositions.
- C5 is equivalent to every persistent relation being rigid. Under C5, S5 makes every current membership decision stable, and BF combines the pointwise necessary tests needed for WI, at every world. Conversely the nullary instance gives ND, and the persistent universal relations become rigid, yielding BF (indeed boxed BF); the recorded ND+BF characterization gives C5.
- C5 is also equivalent to actual coextensionality implying identity for persistent relations. The forward direction uses their rigidity. Conversely this restricted extensionality gives ND from persistent propositions; and if every current tuple necessarily satisfies Z, then λā.□Z(ā) is persistent and currently coextensive with top, so their identity gives BF.
- Tame Rigidity occupies the weaker exact position: weak rigidity implies rigidity. Equivalently, rigid relations are closed under all existing admitted joins, as proved in `/tmp/classicism-research/rigidity-by-joins-and-boolean-closure.md`.
- Replacing full persistence by weak persistence is a substantial change. Even the nullary assertion that every weakly persistent proposition is weakly rigid implies Extensionality: every currently false proposition is vacuously weakly persistent and hence equals bottom; apply this also to negations of truths. Extensionality supplies the converse.
