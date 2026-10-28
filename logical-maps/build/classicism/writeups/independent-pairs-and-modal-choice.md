# Independent-pair models for modal Choice

Two ordinary ZFC constructions distinguish current Relational Choice, Intensional Choice and their modal strengthening. They use the same elementary restriction: every admitted entity has finite support under independent swaps of countably many pairs. External Choice remains available. Neither construction assumes a model of choiceless set theory.

The first is a free root over a classical Henkin leaf. It satisfies current RC and TC, necessary IC, necessary OS, necessary BF, necessary BC_t and Actuality, but fails Modalized RC at (e,e). The second has an absorbing entrance into a group of intensions. It satisfies current IC, necessary full BC, necessary full Atomicity and necessary Actuality, but fails necessary IC at e. Its BF_e and ND_e hold necessarily, while BF_t and ND_t fail.

These are the existing 26 October 2026 constructions, with a fresh independent integration check. Their formulas and proofs below keep the current/necessary and individual/relational scopes separate.

## 1. The classical Henkin leaf

Let individuals be labels L_i and options A_i^0,A_i^1 for i in N. Let Gamma=2^N fix labels and independently swap the two options in each pair. Write Gamma_N for the subgroup fixing every pair in a finite set N. Set D_t=2 with trivial action. Recursively, D_(sigma tau) consists of all actual functions D_sigma -> D_tau with finite Gamma-support under conjugation, for every permitted relational codomain tau. Every individual and every admitted entity has finite support.

This is a genuine typed Henkin hierarchy. Its domains are sets, invariant and nonempty. Boolean operations, equality and each typed quantifier are invariant. An abstraction with finitely many parameters is supported by the union of their supports, by the equivariance induction through terms. Its values lie in the required codomain by the same induction with an arbitrary assigned argument. Thus application, all lambda abstractions and all quantifiers are admitted. Equality is actual function equality. H holds, and H-equivalent formulas define identical actual functions, giving C's restricted Logical Equivalence rule. Extensionality holds and native necessity is truth.

Define the invariant serial relation U by

    U(L_i,y) iff y=A_i^0 or y=A_i^1;
    U(A_i^epsilon,y) iff y=L_0.

It is admitted at eet with empty support. If an admitted total functional S<=U existed, choose a finite support N for S and i outside N. The ith pair swap fixes S and L_i but moves its unique output, a contradiction. Hence RC_(e,e) fails.

At this one-world leaf IC holds at every type: for a fixed inhabited F choose one x satisfying F and its admitted singleton haecceity. No uniform choice of x over all F is made. BF and OS hold at every type, using identity for the latter.

## 2. The free-root construction and soundness

Add a root r with one arrow to this leaf H, and no return arrow. Individuals are unchanged and transport identically. For each relational type tau=sigma_1...sigma_n t set

    D_tau(r) = P(product_j D_sigma_j(r)) × D_tau(H).

The empty tuple gives D_t(r)=2×2. This is recursion on proper subtypes. Every root relation is a pair (A,a) of an arbitrary current extension and an admitted leaf entity. Transport pi is the second projection, which is onto at every type.

Application takes a section of A and applies a to the projected argument. Abstraction pairs its arbitrary current truth extension with the admitted leaf abstraction. Quantifiers use the root domains in their first coordinate and the leaf quantifiers in their second. Equality at a type is literal root equality in the first coordinate and equality of projections in the second. Onto projections make quantifier transport exact. Conversion and substitution follow by induction.

Both evaluations satisfy H. An H-theorem equivalence gives equal current extensions and identical leaf abstractions, so the resulting root entities are identical. This verifies C's original theoremhood restriction. For propositions,

    Box(epsilon,b) = (epsilon and b,b).

Thus a closed box at the root tests both evaluations. Boolean order at every relational type is current-extension inclusion together with leaf entailment. The root is not C5: its proposition (1,0) is nonzero but transports to zero.

## 3. Free current selection and stable single selection

Given a serial current R, external Choice selects a functional subrelation A of its current extension. Pair A with the empty leaf relation. The resulting admitted S is currently total and functional, and S<=R. This proves full RC, including individual outputs. Likewise an externally chosen current transversal, paired with empty leaf extension, proves TC.

For IC, let F be necessarily inhabited. Choose a current instance x and a leaf instance y. The root property

    G = ({x}, lambda z(z=y) at H)

is admitted. It entails F and has exactly one instance at each evaluation, even when pi(x) is not y. IC permits the unique instance to vary; it does not require the current singleton to transport as a singleton graph. IC holds at H as above, so every separately boxed IC instance holds at r.

Let R have universal current extension and leaf component U from §1. It is necessarily serial. If Modalized RC supplied S<=R necessarily total and functional, its admitted leaf component would be a total functional subrelation of U. This is impossible. Thus MRC_(e,e) fails at r. Since RC fails at H, necessary RC fails too.

## 4. The free root's additional structure

Every typed pi is onto. If every root x satisfies Box Fx, all root instances and all projected leaf instances are true; onto transport covers the leaf domain. Hence BF holds at r and necessarily, since it holds at H.

The true proposition (1,0) witnesses Actuality. The proposition algebras 2×2 and 2 are finite complete Boolean algebras, so BC_t holds necessarily. No all-type BC verdict is inferred here.

Identity and the admitted reader E_leaf(epsilon,b)=(b,b) separate propositions. The reader transports to identity. It preserves every typed quantifier at the root because pi is onto, and at the leaf because it is identity. The calculations apply to arbitrary future inputs and prove whole-operation qualification. Different root relations either differ on a current tuple, handled by identity, or in their leaf entities. Leaf extensionality supplies a differing tuple; onto transport lifts it and the reader detects it. Thus full OS holds at both worlds, giving necessary OS.

The staged record derives TC from RC+Actuality via the already integrated Vicinity theorem, and necessary BF from necessary OS. Their direct proofs remain here. The failure of MRC directly settles the old recorded question whether unboxed RC plus IC suffices; it does not settle RC -> TC by itself, since TC holds here.

## 5. The absorbing-entrance construction

Now use individuals X={A_n^0,A_n^1:n in N}, with the same independent Gamma swaps. The category has objects r,s, one arrow a:r->s, no reverse arrow, and the endomorphism group Z at s, with k a=a for every k. Every category arrow acts identically on individuals. Gamma acts trivially on category arrows. The category group and support group are distinct.

For tau=sigma_1...sigma_m t define

    E_tau(v) = disjoint union over h:v->w of product_i D_sigma_i(w),
    D_tau(v) = all finitely Gamma-supported subsets of E_tau(v).

Transport precomposes the arrow tag; application reads transported arguments. Both preserve finite support. Pointwise Boolean operations, local-domain quantifiers and the equality profile h |-> (h_*x=h_*y) are equivariant. The parameter-support induction admits every abstraction, including higher types. The standard substitution induction verifies H; H-theorem equivalents have the same tagged extensions, so strict Logical Equivalence gives C. These closure checks concern the restricted hierarchy itself, not merely a full external action model.

At t Gamma fixes the empty tuples and arrow tags, so every subset of outgoing arrows is admitted. Native necessity tests all those arrows and their full local quantifier domains.

## 6. Current IC and its accessible failure

At r exactly two arrows depart, identity and a. A necessarily inhabited F has nonempty extensions at both. Choose one x in the first and one y in the second, and let G have singleton rows {x},{y}. The union of their finite supports admits G; it entails F and is necessarily uniquely instantiated. Hence full IC holds at r.

At s choose a fixed bijection nu:N->Z and the empty-supported property

    F(nu(n)) = {A_n^0,A_n^1}.

Every row is inhabited. A necessarily singleton admitted G<=F would have a finite support N. At an index n outside N, the nth pair swap fixes G and its arrow tag but exchanges the two possible singleton values. Contradiction. Thus IC_e fails at s, and necessary IC_e fails at r.

## 7. Necessary completeness, atoms and Actuality

At every relational type, Boolean order is inclusion of tagged sets. An admitted property P of relations has a finite support N. Its current family of members is Gamma_N-invariant. The intersection of that family (the whole tagged space for the empty family) is therefore invariant under Gamma_N, admitted, and its GLB. This proves full BC at both objects and hence necessary full BC at r.

Each tagged tuple has finite support, since its finitely many entries do. Its singleton is admitted and an atom. Every nonzero relation contains one, proving necessary full Atomicity. At each object the singleton identity-arrow proposition is true and entails every current truth, proving necessary Actuality. These are local witnesses, not one persisting actual-world witness.

Individuals are transported identically, so BF_e and ND_e hold at both objects and necessarily. Root predicates transported along a are exactly the constant-extension intensions at s, because k a=a. The image is Gamma-invariant. Define Q at r to accept every root predicate, and at a to accept exactly the image predicates. It is admitted with empty support. Every current F satisfies Box QF, but Box forall F QF fails because the nonconstant F of §6 is missing from the image. Thus BF_(et) fails. The same test at t uses the image {Bottom,Top} inside P(Z), giving failure of BF_t. The distinct root propositions {identity_r} and Bottom coalesce at s, giving failure of ND_t.

The individual-type verdict is deliberately not substituted for the failed relational BF instance in the IC propagation theorem. The staged schema records fail BF_t and ND_t; the exact e and et facts remain here without inventing unmatched native nodes.

## 8. Sources and review status

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Free root over a choiceless Henkin leaf*, 26 October 2026, §§1–7; *Classical Henkin leaf with independently swappable pairs*, same date, §§1–4; *Absorbing entrance with finitely supported pair intensions*, same date, §§1–5; all unpaginated. The original source notes made no independent-review claim; this integration independently checks their complete typed constructions and the listed verdicts.

The background full-action construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5 pp.58–61 and Appendix D pp.73–74, recorded in [full-action-models](https://github.com/zwlgzwlg/Logical-Maps/blob/6f15ef5c491fcb117d4d11d8837545a9baaa042d/logical-maps/topics/classicism/groups/full-action-models.yaml). The free-root background is its Appendix E Definition E.2, pp.80–83, recorded in [coalesced-sums](https://github.com/zwlgzwlg/Logical-Maps/blob/6f15ef5c491fcb117d4d11d8837545a9baaa042d/logical-maps/topics/classicism/groups/coalesced-sums.yaml). The restricted finite-support hierarchy and the specific new verdicts are the AI source proofs, not results attributed to that paper. The existing [choiceless Henkin model](henkin-without-relational-choice.html) keeps its own hypothesis and record unchanged.

All verification here is ordinary mathematics. Repository validation checks the candidate records; it does not supply a human check or Lean certification.
