# Exact limits of compatible selector histories

22 October 2026. Ordinary mathematical arguments by OpenAI Codex, direct source `misc`, this note. Self-audited only. No database, original proof, or frozen-archive edits. The target remains unboxed Relational Choice ⇒ Transversal Choice over the original C; it is not settled here.

## 1. Setup and the new limit statement

Use the notation of `choice-transversal.md`: R is an actual equivalence on σ, ρ=σt, θ=ρσt, and Q is a fixed membership selector from RC_(ρ,σ). A valid graph S:θ is actually functional and, at each nonfull F:ρ, selects a point in an R-cell missed by F. The finite-ambiguity operation h_S has a canonical internally well-ordered trajectory Run_S and terminal partial transversal L(S).

For valid S,T, write S≼T when their actual graphs agree at every input F strictly included in L(S). Then Run_S is an initial segment of Run_T and L(S)⊆L(T). The earlier note constructs a total valid upper bound B_C for any represented ≼-comparable family C. Its fallback choices can produce extra progress, so it does not prove an exact terminal union or a least upper bound.

That excess can be removed **by allowing a partial selector graph at the limit**. For every represented ≼-comparable family C of valid selectors, define

    P_C(F,y) := ∃S[C(S) ∧ F⊊L(S) ∧ S(F,y)],
    U_C(y)   := ∃S[C(S) ∧ L(S)(y)].

The new claim is

    L(P_C) ≈ U_C.

Here L is extended to the partial graphs described below. Thus the canonical trajectory can reach the exact material union of the earlier terminal partial transversals. There is no arbitrary default at the boundary. **P_C need not be total**, so this does not assert an exact bound among the original valid selectors or provide another RC witness by itself.

## 2. The partial-graph version of h and L

Call P:θ safe when it is actually at-most-one-valued and every P(F,y), for nonfull F, satisfies Miss(F,y). Totality is not required. Define

    M_P(F,x)(y) := Rxy ∧ ∃G[G≈F ∧ P(G,y)].

Use the same h formula as in the earlier note: adjoin the Q-choice from the unique rigid representative of every nonempty internally finite M_P(F,x), unless F is full. The proof that h_P is progressive, preserves ordinary partial transversals, and respects actual coextension does not use totality of P. Totality was used only to guarantee some nonempty ambiguity range.

Consequently the bare-C quotient-compatible canonical-chain proof applies, giving Run_P and L(P) for every safe P, with h_P(L(P))≈L(P). These are admitted formulas and lambda operations at the same types as before. Neither an entity-valued canonicalizer nor an algebraic supremum is asserted.

## 3. P_C is safe and preserves every earlier trajectory

If two C-members S,T both cover an input F in the displayed definition of P_C, comparability shows that their outputs at F agree. If S≼T, use F⊊L(S); if T≼S, use F⊊L(T). Thus P_C is at-most-one-valued. Its outputs satisfy the missed-cell condition because the supplying selector is valid.

Fix S∈C. For every F⊊L(S), P_C(F,−) and S(F,−) have exactly the same actual extension. Existence follows using S itself; uniqueness follows from the preceding agreement calculation. This remains true for every code coextensive with F. Their ambiguity properties and h-values therefore agree at every such F.

For each G∈Run_S, all its strict predecessors F satisfy F⊊L(S). The defining predecessor-image supremum equation for Run_S is consequently unchanged when h_S is replaced by h_{P_C}. Hence Run_S is an h_{P_C}-chain and is an initial segment of Run_{P_C}.

Put

    A_C(F) := ∃S[C(S) ∧ Run_S(F)].

The union portion of the canonical-chain lemma makes A_C an h_{P_C}-chain: its constituent chains are comparable by initial segment, every represented nonempty subfamily has a least coextension class, and predecessor-image equations transfer. Its material union is U_C, because each L(S) belongs to Run_S and bounds that trajectory.

## 4. Exact terminal value

No input F coextensive with U_C has a P_C-output: such an output would require U_C≈F⊊L(S)⊆U_C. Therefore all its ambiguity ranges are empty, and

    h_{P_C}(U_C)≈U_C.                                      (1)

We show that U_C actually occurs on the canonical trajectory. If A_C already has a greatest coextension class, that class is U_C. If it has no greatest class, then for every F∈A_C there is G∈A_C with F⊊G. The h-chain equation at G gives h_{P_C}(F)⊆G⊆U_C. Conversely any upper bound of h_{P_C}[A_C] bounds A_C, by progressivity, and hence contains U_C. Thus U_C is the actual-inclusion supremum of this predecessor image. Adjoining the entire coextension class of U_C to A_C produces an h_{P_C}-chain, so U_C belongs to Run_{P_C}. For C empty, P_C has no outputs and the empty partial transversal is already fixed, giving the same conclusion directly.

A fixed point on a canonical h-chain is terminal. To check this explicitly, if a later class existed, take its least class V. All its strict predecessors are at or below the fixed point U_C. Outputs at predecessors below U_C lie below U_C by the chain equation there, and outputs at codes coextensive with U_C are coextensive with U_C by congruence and (1). The supremum equation at V then gives V⊆U_C, contradiction.

Hence U_C is the greatest class of Run_{P_C}, proving L(P_C)≈U_C. This verifies the claim without external transfinite recursion, Boolean Completeness, an assumption that chain codes with equal extensions are identical, or a choice of one code for each coextension class.

## 5. A cofinality lemma for the original selector states

Every actual partial transversal T is included in L(S) for some valid selector S. In fact, with Q and one default valid B fixed, an admitted operation T↦S_T suffices.

Let E_T(F)(y):=Ty∧Miss(F,y). When this property is nonempty, let S_T(F,y) hold exactly when Q(E_T(F),y); otherwise use B(F,y). This is actually total, entity-functional, and valid. If F⊊T, every choice at every code coextensive with F lies in T and in a missed cell. Each ambiguity range has at most one member, because T is partial, and at least one range is nonempty. Therefore

    F⊊T  ⇒  F⊊h_{S_T}(F)⊆T.                              (2)

Whenever T⊆F, progressivity gives T⊆h_{S_T}(F). Thus h preserves the property of being comparable with T. Suprema of comparable families whose members are each comparable with T also remain comparable with T. A least-counterexample argument along Run_{S_T}, using its predecessor-image equation, shows that every trajectory member is comparable with T: if all predecessor outputs lie below T then so does their supremum; if one contains T then so does their supremum. This includes the empty predecessor family.

The fixed point L(S_T) is therefore comparable with T. It cannot be strictly below T by (2), so T⊆L(S_T). This is cofinality of the canonical terminal values, not a coextension-invariant choice of selector entities.

## 6. What remains at the boundary

The exact limit P_C intentionally has no output at its terminal coextension class U_C. For a nonfull U_C, choosing one missed point a and putting that point on the **whole** class of U_C extends this particular history coherently. RC can make that choice separately for each partial-graph entity P_C.

The unresolved step is still whether choices attached to different codes of the same actual limiting graph can be made compatible. Two such codes can receive different points in one missed R-cell. The exact-limit construction is invariant under coextension of the family code only up to actual graph coextension, and gives no identity or uniform next choice.

This improves the earlier limit analysis in a specific way: uncontrolled fallback progress can be eliminated, and the exact terminal union is represented. It does not silently turn partial limit graphs into total selectors, establish a least bound in an antisymmetric entity order, or settle RC⇒TC.

## 7. A chain-complete preorder of partial history graphs

There is a useful reformulation which makes compatibility of limits automatic. It also narrows the remaining successor-coherence question to codes of the **same entire history graph**, rather than every history having the same terminal partial transversal.

Call a safe partial graph P **good** when:

1. Its input domain is saturated under actual coextension: if F≈G and P has an output at F, it has an output at G.
2. Every input F at which P has an output is an actual partial transversal and satisfies F⊊L(P).

Safety includes entity-functionality of each defined row and the missed-cell condition. These are admitted formulas about P; L(P) is the operation of §2. Order good graphs by **actual graph inclusion**, not by algebraic entailment. This is a represented preorder whose equivalence is actual coextension of the entire graph. The empty graph is good.

### Terminal monotonicity

If P⊆Q are good, then Run_P is an initial segment of Run_Q, so L(P)⊆L(Q).

For a strict predecessor F of L(P) on Run_P, h_P(F) cannot be coextensive with F: the fixed-point-is-terminal argument of §4 would make F terminal. Hence some ambiguity range is nonempty and P is defined at a code coextensive with F. Domain saturation makes P defined at **every** such code. Graph inclusion and functionality of Q now make the P and Q rows identical at all those codes. Therefore h_P(F)≈h_Q(F). The predecessor-image equations for Run_P transfer, proving the claim by canonical-chain comparison.

This argument uses saturation essentially. Arbitrary graph inclusion does not make the finite-ambiguity construction monotone: adding previously undefined coextensive rows could turn a finite range into an infinite one.

The proof only requires that the upper graph Q be safe; its goodness is not used. This stronger observation is what licenses applying the argument to a chain union before proving that union good, avoiding circularity in the next paragraph.

### Exact least upper bounds of represented chains

Let C be any represented family of good graphs comparable by actual graph inclusion, and let P be their material union. Chain comparability makes P entity-functional. Safety and domain saturation are preserved. Terminal monotonicity makes the L(Q), Q∈C, a comparable family of partial transversals, whose material union is U.

Every P-input F is strictly below some L(Q) and hence strictly below U. In particular P is undefined throughout the coextension class of U, so h_P(U)≈U. The previous row-agreement argument transfers every Run_Q to an h_P-chain: strict predecessor rows are already defined in Q and cannot change in the union. Their represented union has material supremum U. Exactly the proof of §4 then shows that U occurs on Run_P and is its terminal class. Thus

    L(P)≈U=⋃_{Q∈C}L(Q).

It follows that P is good. Since P is the actual union of the graphs, it is their least upper bound for actual graph inclusion. The empty-chain case is the empty graph. This gives **represented chain completeness of the preorder**, not identity-antisymmetry of graph entities.

### A strict progressive operation, with the remaining defect isolated

Use RC_(θ,σ) to obtain a functional K(P,a) choosing a point missed by L(P) whenever P is good and L(P) is nonfull; elsewhere use a fixed default individual of type σ. As before, the empty σ case is trivial. Define, in the active case,

    Ψ(P)(F,y) := P(F,y) ∨ [F≈L(P) ∧ K(P,y)].

Return P in the inactive case. This is an admitted operation on graph entities. For good P with nonfull L(P), the old domain lies strictly below L(P), so the newly added class was wholly undefined. Thus Ψ(P) is functional and has a saturated domain. Its new outputs are safe. All predecessor rows on Run_P are unchanged, while at its terminal class the update adds exactly K's missed point a. Consequently

    L(P)⊊L(Ψ(P)),                 P⊊Ψ(P).

Every old or new defined input lies strictly below the new terminal value, so Ψ(P) is again good. At a full terminal value Ψ fixes P.

Hence RC supplies a strict-unless-full progressive operation on this **chain-complete history preorder**, with exact union limits. What is not established is that Ψ respects equivalence in that preorder: coextensive P and P′ may have different K-outputs. Bourbaki–Witt on a preorder requires that missing congruence, and the corresponding entity order is not antisymmetric.

Different histories with coextensive terminal partial transversals can now remain incomparable; the construction does not need to amalgamate them. The precise obstruction concerns distinct codes with the same actual history graph.

## 8. A finite ambiguity criterion at the history level

The preceding reformulation gives a further conditional closing lemma. Suppose K can be chosen so that for every good P with nonfull terminal value, the represented property

    A_P(a) := ∃Q[Q is actually graph-coextensive with P ∧ K(Q,a)]

is internally Frege-finite. It is nonempty, and every member is missed by L(P), since goodness and the terminal value are invariant under actual graph coextension.

Rigidify A_P using the bare-C finite-representative lemma and use the fixed Q membership chooser (denoted Q_mem here to avoid confusing it with a graph variable) on its unique rigid representative. For coextensive P,P′ these representatives are the **same entity**, so Q_mem chooses the same point. Replacing K by this new functional graph makes Ψ respect actual graph coextension.

The quotient-compatible fixed-point theorem now applies to the chain-complete good-graph preorder of §7. At a fixed point, strictness rules out a nonfull terminal value. Its L-value is therefore a transversal of R.

This is a sufficient condition, **not** a consequence established from RC. Its role is to locate the remaining ambiguity at equal complete history graphs, after both successor extension and exact chain suprema have been proved. The construction does not require histories with merely coextensive terminal states to make the same next choice.

Nor does an arbitrary K satisfy the condition automatically. In the ordinary full two-world S5 model with σ=ℕ and universal R, all graph entities having empty actual extension are good and have empty terminal value. Their other-world graph extensions can encode arbitrary n∈ℕ. A valid K can read that other-world code and choose n at the actual point, defaulting to 0 when no such code is present and outside the active case. Fullness admits its graph. The ambiguity range across codes of the empty actual graph is then all of ℕ, which is not internally finite in that full model. TC nevertheless holds there, and a suitable constant K exists for this example. This refutes automatic finiteness for arbitrary witnesses, not existence of an appropriately chosen witness.
