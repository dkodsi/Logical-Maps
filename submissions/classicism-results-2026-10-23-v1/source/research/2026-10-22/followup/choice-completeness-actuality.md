# Relational Choice and Boolean Completeness imply Actuality

22 October 2026. Original ordinary mathematical argument by OpenAI Codex; direct source `misc`, this note. No human check, independent-agent check, formal verification, or literature-novelty claim. No database or frozen-archive edit.

## Exact local theorem

Over the original fixed C,

    RC_(t,t) + BC_(tt)  ⇒  Actuality.

Here RC_(t,t) is relational selection from propositions to propositions, and BC_(tt) is Boolean Completeness of the algebra of properties of propositions. Both premises are **actual and unboxed**. In particular, unboxed all-type Relational Choice plus unboxed all-type Boolean Completeness implies Actuality. Section 7 proves this sharpest local version. Sections 1–5 retain the independently useful guarded proof with RC_(tt,t), selection from proposition-properties to propositions.

The short route is: BC_(tt) forces a true disjoint join to have a true member. RC_(t,t), with the resulting BC_t, gives a disjoint refinement of all actual falsehoods. If Actuality failed, those falsehoods would have join ⊤, yielding a true disjoint join with no true member.

The proof uses no ND, BF, Plenitude, persistent selected edges, optional necessitation, or infinitary syntax. It does not use RC+BC⇒Transversal Choice; the direct proof below supplies an independent route. Its fixed-point input is the bare-C Bourbaki–Witt lemma already written out in `notes/relational-choice-boolean-completeness-transversal-proof.md`, §5, with the guarded-operation refinement in `notes/rc-guarded-progressive-operation.md`.

A fresh proved-only engine query before this argument found no recorded derivation or separator for RC+BC⇒Actuality. That is the record status, not an objection to the new proof.

## 1. Evaluation and the proposed meet reduction

Write H_a:=λz(z=a), of type tt. Evaluation at any proposition x has right adjoint

    r_x(b):=λz((z=x)→b).

Indeed X(x)≤b iff X≤r_x(b): after unpacking algebraic order, this is the necessary universal closure of the H theorem

    ∀z[Xz→((z=x)→b)]  ↔  (Xx→b).

Consequently evaluation preserves every represented algebraic join that exists. This does not identify algebraic joins with material unions.

BC_(tt) implies BC_t. Given a represented family of propositions, take its family of constant properties c_p:=λz.p, form their join at tt, and evaluate it at ⊤. The result is the join of the original family. Boolean duality gives meets as well.

Thus let m be the Boolean meet of the actual truths, represented by λp.p. Then

    Actuality  ↔  m is true  ↔  m≠⊥.

If an actuality witness u exists, u≤m, so m is true. If m is true, it itself is a witness. If m is false, ¬m is an actual truth, so m≤¬m and therefore m=⊥. Conversely ⊥ is false. Dually, under failure of Actuality, the join of all actual falsehoods is ⊤.

The additional argument needed is that relational selection forces enough disjoint refinement of those falsehoods. Algebraic completeness alone does not supply that refinement.

## 2. A true disjoint join has a true member

This lemma uses **only C+BC_(tt)**. Call A:tt a false antichain when

    ∀a(Aa→¬a),
    ∀a b(Aa∧Ab→[a=b ∨ a∧b=⊥]).

Zero members are harmless for this lemma. Suppose, toward contradiction, that the algebraic join j of A's actual instances is **true**.

Use BC_(tt) to form J, the join of the represented family of haecceities H_a with Aa. For every actual a∈A,

    H_a≤J,             J(a)=⊤.

Define C(x,y):=(x=y ∨ x∧y=⊥). We first prove

    J(x)∧J(y) ≤ C(x,y)                 for all actual x,y:t.       (1)

Fix actual a,b∈A. Either a=b or a∧b=⊥. Each alternative is a positive identity, so its truth is necessary by bare-C Necessity of Identity. Necessary substitution therefore gives

    H_a(x)∧H_b(y) ≤ C(x,y).

For fixed a, move H_a(x) to the right by Boolean implication adjunction and use that J(y) is the join of the H_b(y)'s. Then move J(y) to the right and use that J(x) is the join of the H_a(x)'s. This proves (1). No inequality is necessitated, and no ND is used. J may include ⊥; (1) does not forbid that.

Now put

    v:=∀p(J(p)→¬p).

For every a∈A, necessary universal instantiation and J(a)=⊤ give v≤¬a. Hence every a∈A lies below ¬v, so j≤¬v. Since j is true, v is false. Classical quantifier duality therefore supplies an **actual** q with

    J(q) ∧ q.

For every a∈A, q≠a because q is true and a is false. By (1), q∧a=⊥. Therefore every a∈A lies below ¬q, and j≤¬q. The truth of j contradicts the truth of q. This proves the lemma.

Equivalently, for **any** represented pairwise-disjoint family, its algebraic join is actually true iff some member is actually true. The reverse implication is immediate from being an upper bound. This disjoint-join reflection theorem uses no Relational Choice.

The essential combination is higher-type completeness and actual quantification: joining the haecceities forces an actual true member, while the stable antichain identities prohibit it.

## 3. Under ¬Actuality, every nonzero proposition has a nonzero false part

Let b≠⊥. If b is false, use b itself. If b is true, failure of Actuality says b does not entail every actual truth. Choose true q with b≰q. Then

    c:=b∧¬q

is false, nonzero, and below b. This is an ordinary actual argument; no choice principle is needed for this one existential conclusion.

Consequently, if A is a represented nonzero false antichain and j is its Boolean join, section 2 gives j≠⊤. There is a nonzero false a≤¬j. It is disjoint from every A-member and is not itself an A-member. Thus every such antichain has a strict extension by one false proposition.

## 4. A chain-complete algebraic poset of guarded antichains

Put

    D(p):=¬p ∧ p≠⊥,
    P(F):= [F≤D] ∧ ∀p q □(F(p)∧F(q)→C(p,q)),

where C is from (1). Order the P-members by the algebraic Boolean order at tt. This is an antisymmetric represented poset. Its actual members are nonzero false antichains.

Every represented algebraically comparable family of P-members has its ambient join J by BC_(tt), and J still satisfies P. First J≤D because D upper-bounds the family. For fixed actual p,q and any two members F,G, comparability puts both below one of them. That member's boxed antichain clause gives

    F(p)∧G(q)≤C(p,q).

The same two Boolean-adjunction steps used in section 2, with evaluation preserving the joins, yield J(p)∧J(q)≤C(p,q). Thus P(J). The empty family has join bottom, which satisfies P. Therefore the poset has represented chain suprema and a least element. The quantifier over p,q in P is outside its box; no interchange of □ with ∀ is made.

## 5. RC supplies an everywhere-guarded strictly progressive operation

Continue to assume ¬Actuality. For every P-member F, section 3 supplies a nonzero false a disjoint from every actual F-member. Otherwise permit any output. Thus the relation

    U(F,a):= P(F) → [¬a ∧ a≠⊥ ∧ ∀q(F(q)→a∧q=⊥)]

is actually serial. RC_(tt,t) supplies an actually total functional S⊆U. Define

    N(F,p):= S(F,p)
             ∧ ∀r(S(F,r)→r=p)
             ∧ D(p)
             ∧ ∀q(F(q)→[C(p,q)∧C(q,p)]),
    g(F):=λp(F(p)∨N(F,p)).

This is an admitted operation (tt)→(tt). Its construction does not reify S as an operation selecting proposition entities.

The H theorem F(p)→g(F)(p) gives F≤g(F). If P(F), then g(F)≤D because the new clause explicitly implies D. To preserve the boxed antichain clause, check the four old/new cases for two arguments. Two old members use P(F); two new members are identified by the uniqueness guard; and one old plus one new uses the appropriate direction of the safety guard. Necessitate only this unconditional H implication and combine it with P(F)'s existing boxes. Hence P(g(F)). No future functionality or containment of S is assumed.

Actually, at a P-member F the unique S-output a is false, nonzero, and disjoint from every F-member. Boolean commutativity gives disjointness in both directions, so all guards hold. Moreover F(a) is false: otherwise a would be disjoint from itself and hence zero. Thus g(F)(a) holds while F(a) does not, proving

    P(F) → F<g(F).

The bare-C Bourbaki–Witt lemma now applies to this represented chain-complete antisymmetric poset and its progressive operation. It gives F with g(F)=F, contradicting strictness. Therefore ¬Actuality is impossible, completing the local theorem.

## 6. Alternative route and modal scope

As a cross-check, Transversal Choice gives the recorded preorder form of Zorn's Lemma. Apply it to actual nonzero false antichains under inclusion: material unions bound comparable families. Under ¬Actuality, maximality and the density argument in section 3 force the maximal antichain to have join ⊤, contradicting section 2. Thus TC together with BC_(tt) also implies Actuality. This alternative uses the recorded TC⇒Zorn theorem; the direct proof above does not.

The local implication, including its sharper form proved next, is a closed C theorem with its assumptions discharged. Necessitating that **theorem** gives

    □RC_(t,t) + □BC_(tt) ⇒ □Actuality.

No boxed conclusion is inferred from the unboxed premises alone. This note supplies a mathematical proof, not an update to the conjecture records or any formal verification status.

## 7. Sharpening: RC_(t,t) supplies a disjoint refinement

**Disjoint-refinement lemma.** Over C+BC_t+RC_(t,t), every represented family X:tt has a represented pairwise-disjoint nonzero refinement with the same Boolean join. Each refinement member lies below some actual X-member.

Let j=∨X. Use RC_(t,t) to select x from the serial relation requiring

    X(x) ∧ x≰b     if b<j,
    x=⊥            otherwise.

Seriality when b<j follows from j's least-upper-bound property: not every X-member can lie below b. Let S(b,x) be the actual functional selector, and define the actual functional graph

    f(b,c):=∃x(S(b,x) ∧ c=b∨x).

On the algebraic interval [⊥,j], f is progressive, stays in the interval, is strict below j, and fixes j. The interval has suprema for all represented chains by BC_t. Apply the canonical-chain part of the bare-C Bourbaki–Witt proof: the union A of its f-chains is an internally well-ordered chain with greatest member j, and each b∈A is the supremum of f-values at its strict predecessors. In particular, if b<c in A then f(b)≤c. Function notation here abbreviates the uniquely specified actual graph value; no selecting operation is asserted.

For b∈A with b<j define its increment d_b=f(b)∧¬b. Its represented graph existentially binds the unique f-value. The increment is nonzero, and if x is S's value at b, then

    d_b=(b∨x)∧¬b=x∧¬b≤x,       X(x).

If b<c are in A, then d_b≤c and d_c≤¬c, so their increments are disjoint. Let Δ be the represented image of these increments. It is a nonzero antichain refining X.

We verify that j is its join, rather than assuming a transfinite telescoping rule. Every increment lies below j. If k upper-bounds Δ and some b∈A fails b≤k, take the least such b. For every c<b in A, c≤k and d_c≤k, hence f(c)=c∨d_c≤k. The defining supremum condition at b gives b≤k, contradiction. Therefore every A-member lies below k, including j. This proves j=∨Δ.

Now assume ¬Actuality. By section 1, the represented family X(p):=¬p of all actual falsehoods has join ⊤. Apply the lemma. Every member of its disjoint refinement Δ is false, since it lies below a false X-member; yet ∨Δ=⊤ is true. This contradicts the disjoint-join reflection theorem of section 2. Since BC_(tt) supplies BC_t, this proves

    C + RC_(t,t) + BC_(tt) ⊢ Actuality.

The increment construction adapts the already audited disjoint-increment calculation in `notes/relational-choice-countable-completeness-ccc.md`, §3. Here no CCC or countability assertion is used; the additional spanning argument is the least-counterexample proof just given.

## 8. An explicit single relation witnessing the obstruction

The required choice instance can be made parameter-free. Define

    W(b,x):= [b≠⊤ ∧ ¬x ∧ x≰b] ∨ [b=⊤ ∧ x=⊥].

Bare C proves Serial(W) iff ¬Actuality. The forward obstruction is immediate from an actuality witness u: every false x lies below ¬u, so the row b=¬u≠⊤ is empty. Conversely, under ¬Actuality, section 3 supplies a nonzero false part x of ¬b whenever b≠⊤; then x≰b. At b=⊤ use ⊥.

Under BC_(tt), W has **no** actually total functional subrelation. Such a subrelation would give the construction of section 7 with j=⊤, producing a represented false antichain with join ⊤, contrary to section 2. Thus any C+BC_(tt)+¬Actuality model explicitly fails relational selection for this one W. No model-construction hypothesis is involved in this obstruction.

Even a subrelation of W with nonempty **internally finite** output fibres is impossible under those assumptions. The Boolean join of each such fibre exists, is false, and stays outside the input b when b≠⊤; at ⊤ it is ⊥. These joins have an admitted actually functional graph by their unique algebraic characterization, so they would supply the forbidden functional subrelation. The finite-join assertion is proved by the map's Frege induction: remove one member, take the induction hypothesis's join, and adjoin that member by binary ∨. It does not assume external standardness or a selecting operation.

## 9. Consequences and limits

Under all-type BC, section 2 also makes the Boolean join of any represented **algebraically disjoint** family of relations actually coextensive with its material union. Fix an actual argument tuple. Evaluation takes the join to the join of the corresponding proposition values; those values form a represented antichain, so section 2 reflects its truth to one member. This is actual coextension, not identity of relation entities.

With all-type RC as well, the disjoint-refinement construction works at any relational type τ, using RC_(τ,τ) and BC_τ. Each refinement member lies below an original member. The same argument therefore shows that **every** represented algebraic join is actually coextensive with its material union. This does not claim necessary coextension, transport of a current supremum to a future supremum, BF, or Plenitude.

Combining the new Actuality conclusion with the recorded BC+Actuality⇒Weak Rigid Comprehension and RC+Weak Rigid Comprehension⇒TC yields another proof of the all-type RC+BC⇒TC result. The original **RC alone ⇒ TC** question remains unresolved. In particular, the proof here requires completeness at **tt**, not merely BC_t; the haecceity join is the decisive higher-type use.

There is also a stronger locality consequence for the TC question: **all-type RC plus BC_(tt) alone implies all-type TC**, since Actuality gives the recorded Transversal principle and Transversal+RC gives TC. No completeness premise at the individual-property type et or at every higher type is needed for this consequence.

Conversely, under C+RC_(t,t)+BC_t+¬Actuality, section 7 produces a specific represented nonzero false antichain Δ with join ⊤. The family {H_a:Δ(a)} then has **no** Boolean join at tt, by section 2's proof. This is a concrete missing-join obstruction, rather than just the negation of a completeness schema. The case RC+BC_t⇒Actuality is not settled here.

Without BC_t there is a precise two-level alternative. Under RC_(t,t)+¬Actuality choose S for the explicit W and form f(b)=b∨S(b) relationally. The union A of all f-chains is still represented and internally well ordered: the comparison and union portions of the fixed-point proof require no completeness. If A has an algebraic supremum, the final fixed-point argument makes it ⊤ and places ⊤ in A; the increments then give the preceding Δ and its missing haecceity join. Hence either this particular internally well-ordered family A has no join at t, or its increment antichain has no haecceity join at tt. This is a statement about two explicit represented families, not arbitrary external transfinite iteration.

## Audit status

Both proofs are ordinary mathematical arguments by this agent, not independently checked new results. The final checks preserve the positive-identity use of NI, the exact type tt of the haecceity join, actual quantifier duality, represented internal well-ordering, and the restriction on necessitation. Temporarily adding the unboxed and boxed all-type conclusions to the proved-only engine in memory introduced no new conflicts with recorded proved models; this consistency check is not a proof. Database records remain untouched. The engine separately reports `full-boolean-valued-atom-and-atomless` as a separator from **necessary** Actuality for the unboxed premises, so that stronger unboxed-to-boxed claim is not made.
