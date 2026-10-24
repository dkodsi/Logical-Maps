# Strong Possibility: a conditional second-jump theorem

Research note by OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematics; no Lean work and no database edits. All existence, completeness and oracle-capacity conclusions about Strong Possibility below are explicitly conditional on its consistency. The supplied principle record leaves that consistency open. These are session deductions, not claims of literature novelty.

## 1. Fixed meanings and dependencies

Use exactly the original finitary relational-type language and reference theory C from `topics/classicism/topic.yaml` and `background.md`. Let

    Max = C + {¬E : E is a closed pure identity and C does not prove E}.

For a proposition p, write

    Bp := □_≠p := ∃q(q ∧ □(◇q → p)),
    Dp := ◇_≠p := ¬B¬p.

Strong Possibility, denoted SP, is C plus the closed pure instances

    DP whenever Max+P is consistent.                         (SP)

This is the original pure schema, with Max as its unchanged reference theory. The exact definition is `principles/strong-possibility-r.yaml`, citing Bacon–Dorr, *Classicism*, draft of 16 May 2023, §2.6 p. 42. The modal definition is in `background.md` immediately before its hats discussion. C proves that B is a normal reflexive modality; the proofs below mainly use its displayed definition. The recorded implication SP⇒Max is retained.

The companion note `max-degree.md` establishes the following ingredients, with source boundaries stated there:

1. Max is consistent, has a 0′-c.e. axiom set, and Th(Max) is Σ^0_2-complete under ordinary computable many-one reductions. Accordingly Cons(Max+P) is Π^0_2-complete.
2. Fix the e-counting Frege number type ν=(et)t, its number predicate N, and I=◇I*. Max entails I, and C+I interprets PA on N by Goodsell's arithmetic lemma. Impredicative N-induction permits arbitrary additional definable predicates, including modal ones.
3. With h(n) expressing ordinary diagonal halting, the pure predicate

       J1(n) := □(I→h(n))

   is numeralwise correct for 0′ in every Max model.
4. Let H(n,J1) express diagonal halting for an oracle machine with oracle J1, and put Q_n=H(numeral n,J1). The standard-arithmetic coalesced maximalist root gives the exact uniform reduction

       n∈0′′  iff  Max⊢Q_n.                               (1)

   The positive direction verifies a finite genuine computation. For the converse that recorded root has standard N, Sum and Prod and J1=0′ on all its numbers; hence it refutes Q_n for nonhalting n. See `max-degree.md` §§10.1–10.3. This particular formula-level reduction is used below to define one fixed predicate for 0′′.

No new maximalist or Strong Possibility model is constructed in this note.

**Attribution boundary.** The underlying reflection direction is already stated in Bacon–Dorr's [author-hosted draft dated 1 July 2022](https://andrew-bacon.github.io/papers/Classicism.pdf), §2.6, printed p. 42 (PDF page index 41): when a closed P is C-consistent but Max-inconsistent, its distinctness-preserving possibility is Max-inconsistent as well. The immediately following passage defines Strong Possibility and says its consistency is unknown. This is a different draft from the bundle's cited 16 May 2023 version. The session note `maximalism-modal.md` §10 had already written the exact reflection diagram before this degree calculation. Section 2 below supplies the explicit finite-support proof for audit; the arithmetic-degree consequences in §§3–8 are the subsequent session deductions, not an attribution of those degree results to the paper.

## 2. Finite-support persistence of every Max theorem

**Lemma 2.1.** If A is any closed pure sentence and Max⊢A, then Max⊢BA. More precisely, a finite conjunction Q of Max's inequality axioms satisfies

    C⊢Q→A,       C⊢□(◇Q→A).                              (2)

Proof. A finite Max proof uses finitely many extra axioms ¬E_1,…,¬E_k, where each E_i is a closed pure identity not provable in C. Put Q=∧_i¬E_i. By the ordinary deduction theorem,

    C⊢Q→A, hence C⊢¬A→(E_1∨…∨E_k).

Necessity of identity gives C⊢E_i→□E_i. Normal modal reasoning gives

    C⊢(E_1∨…∨E_k)→□(E_1∨…∨E_k),

because each disjunct entails the necessity of the disjunction. Consequently

    C⊢¬A→□¬Q, equivalently C⊢◇Q→A.

This last formula is a genuine C-theorem, so C-theorem necessitation gives the second part of (2). Max proves Q, and the proposition Q therefore witnesses ∃q(q∧□(◇q→A)). Thus Max proves BA. If k=0, take Q=top: C already proves A, so the same conclusion follows immediately. □

This proof never necessitates a Max axiom or an actual optional hypothesis. It first proves the suitable conditional within C. It also makes no claim that Max is closed under ordinary □ necessitation; that stronger statement is false in the intended setting.

**Theorem 2.2 (exact reflection).** For every SP model M and every closed pure A,P,

    M⊨BA  iff  Max⊢A,
    M⊨DP  iff  Max+P is consistent.                        (3)

Proof. If Max⊢A, Lemma 2.1 and SP⇒Max give SP⊢BA. If Max does not prove A, classical deduction gives Cons(Max+¬A), so the defining SP instance is D¬A, namely ¬BA. Thus SP decides BA with precisely the correct external sign. The second equivalence follows by duality and Cons(Max+P) iff Max does not prove ¬P. □

The theorem is syntactic too: each of the correct signed assertions in (3) is a theorem of SP. If SP is inconsistent, it has no model and the model formulation is vacuous; the consistency hypothesis is indispensable for the degree deductions below.

## 3. The exact oracle cone for consistent axiomatizations

Assume Con(SP). For every oracle X, the following are equivalent:

1. There is a consistent X-c.e. theory T whose consequences contain C and every SP instance.
2. 0′′≤_T X.

For 1⇒2, on input a closed pure A enumerate T-proofs of BA and ¬BA in parallel, using X. Exact reflection ensures that one will be found, and consistency ensures that both cannot be found. The sign decides whether Max⊢A. Since Th(Max) is 0′′-complete, X computes 0′′.

For 2⇒1, Cons(Max+P) is decidable in 0′′. Hence X can enumerate all and only the correct SP axioms DP; together with C these give an X-c.e. consistent theory by the standing hypothesis. □

Thus, conditionally, the axiomatization cone rises from the cone above 0′ for Max to the cone above 0′′ for SP. In particular no consistent 0′-c.e. theory can entail SP. This is an effectiveness obstruction, not an inconsistency proof for SP.

## 4. A pure predicate correct for 0′′

Define one fixed pure numerical predicate

    J2(n) := B H(n,J1).                                    (4)

Here B, H and J1 are expanded by their fixed finite definitions; only the numerical variable n remains free. Every type remains admitted, and no individual-output function is introduced.

By (1) and exact reflection (3), for each standard natural number n,

    SP⊢J2(numeral n)       if n∈0′′,
    SP⊢¬J2(numeral n)      if n∉0′′.                       (5)

No assertion is made that J2 has the intended extension on a model's nonstandard numbers. Numeralwise correctness is all the following argument needs.

Let H_b(n,J2), for b∈{0,1}, express diagonal halting of an oracle machine with oracle J2 and output b, using the same interpreted arithmetic convention as in the Max proof. Since SP entails Max and hence I, all the needed arithmetic is available. Full induction for the expanded predicate J2 follows from N's impredicative definition. In particular SP proves that one deterministic computation cannot halt with both output bits.

If the actual 0′′-oracle machine n(n) halts with output b, its finite run asks only finitely many standard oracle questions. The finitely many correct literals (5) verify the run in SP. Thus

    n∈K_b^{0′′}  implies  SP⊢H_b(numeral n,J2).            (6)

This remains valid if the interpreted numerical domain contains nonstandard elements. We verify a particular standard finite run and use internal determinism only to rule out a conflicting output.

## 5. Complete theories and adequate models require PA degree over 0′′

Assume Con(SP). Given a complete consistent pure extension Y of SP, define

    d_Y(n)=1  if H_0(numeral n,J2)∈Y,
           0  otherwise.                                  (7)

If φ_n^{0′′}(n)=0, (6) forces d_Y(n)=1. If φ_n^{0′′}(n)=1, (6) and determinism force ¬H_0 into Y, so d_Y(n)=0. Therefore d_Y is binary DNR relative to 0′′. The conversion is uniform: compile the displayed pure sentence from n and ask one Y-membership question.

In particular no complete SP theory is computable in 0′′. An adequate model code providing uniform closed-term interpretation and truth valuation computes Y by evaluation, so it has the same lower bound. This is a claim about adequate truth-evaluable codes; it is not a claim about bare action/category presentations without an effective valuation or term semantics.

A smaller encoding already gives the degree lower bound. Suppose the code supplies sorted domains, equality, application graphs and actual valuation, but no general term interpreter. Hardcode the finitely many presentation indices of 0_ν, Suc_ν and G=λn.H_0(n,J2). Iterating Suc k times, applying G, and reading the valuation computes (7). Thus such a presentation also has PA degree over 0′′. This reduction is nonuniform in those finitely many unnamed indices; it becomes uniform if their denotations are named. Application and equality without valuation are not covered.

Conversely let d be binary DNR relative to A=0′′. Use a fixed consistent A-c.e. Henkin witness theory T_H for SP, supplied by the same BBK completeness/Henkin construction as in `max-degree.md` §5. Given a finite consistent choice set Δ and the next expanded-language sentence φ, effectively compile an A-oracle program e(Δ,φ) which ignores its input and searches T_H+Δ for proofs of φ and ¬φ, returning 0 for the former and 1 for the latter. Choose φ if d(e)=1, and ¬φ if d(e)=0. Consistency makes the proof-search alternatives disjoint, and DNR forces the consistent choice when one is forced; if neither is forced, both choices are consistent. Iteration yields a complete consistent witnessed theory and its countable BBK term model.

The compilation uses no supplied A oracle. If a subsidiary step needs A itself, d computes it uniformly: compile e(k) to query its oracle's kth bit and return that bit, so A(k)=1−d(e(k)).

Consequently the following conditions on an oracle X are equivalent, assuming Con(SP):

1. X computes a complete consistent pure SP theory.
2. X computes a countable adequate BBK SP model.
3. X computes binary DNR relative to 0′′, that is, has PA degree relative to 0′′.

Moreover the completion/model solution problems are uniformly Medvedev-equivalent to binary DNR relative to 0′′. The transformation produces some solution of the specified theory; it does not preserve the exact theory of a supplied model or assert degree preservation.

The upper construction also gives an application/equality/valuation presentation. Consequently this weaker encoding has the same exact oracle capacity, although the nonuniform finite-index argument does not assert a uniform Medvedev equivalence for arbitrary unnamed codes.

Relative Low Basis supplies examples of adequate SP presentations of degrees d satisfying

    0′′ <_T d <_T 0′′′,       d′=0′′′.                    (8)

These are conditional model-existence conclusions. The same characterization holds after any fixed 0′′-c.e. addition consistent with SP. Exact degree spectra of particular isomorphism types are not claimed.

## 6. Robust Σ^0_3-completeness of theoremhood

**Theorem 6.1.** Every consistent 0′′-c.e. theory T whose consequences contain SP has Σ^0_3-complete pure theoremhood under ordinary computable many-one reductions. In particular, if SP is consistent, Th(SP) has degree exactly 0′′′.

The upper bound holds because T is c.e. in A=0′′. For hardness put

    V_b={n:T⊢H_b(numeral n,J2)},  b=0,1.

These sets are A-c.e., disjoint by consistency and internal determinism, and contain K_b^A by (6).

The parameterized recursion theorem gives an ordinary computable p(n) whose A-oracle program ignores its input and dovetails two searches:

1. If φ_n^A(n) halts, return 0.
2. If p(n) is enumerated into V_0, return 1.

The index-building function p is computable without A; the compiled program queries A. The enumeration index for V_0 is a fixed parameter. Fix any effective tie convention.

If n∉A′ and p(n)∈V_0, the second branch eventually returns 1, so p(n)∈K_1^A⊆V_1, contradicting disjointness. Thus n∉A′ implies p(n)∉V_0. If n∈A′ but p(n)∉V_0, the first branch eventually returns 0, putting p(n) in K_0^A⊆V_0, again a contradiction. Therefore

    n∈0′′′  iff  T⊢H_0(numeral p(n),J2).                  (9)

This is an ordinary computable many-one reduction, not merely a reduction computable in 0′′. It proves the theorem. □

Under the same consistency hypothesis, finite pure extension consistency for SP is Π^0_3-complete, since Cons(SP+P) iff SP does not prove ¬P. The proof establishes this without requiring an SP model whose arithmetic is externally standard.

## 7. Boundaries and comparison

The conditional computational ladder is:

| Fixed theory | Theoremhood | Oracle cone for a consistent c.e.-in-oracle strengthening | Oracle capacity for one complete theory/adequate model |
| --- | --- | --- | --- |
| Positive C/B/F plus weak Infinity | Σ^0_1-complete | Includes computable axiomatizations | PA degrees |
| Old pure Max_C | Σ^0_2-complete | 0′≤_T X | PA degrees over 0′ |
| Original pure SP, **if consistent** | Σ^0_3-complete | 0′′≤_T X | PA degrees over 0′′ |

The first row's exact PA threshold is the finite-trace argument in `positive-effective.md` §16; its positive model upper bounds use the auxiliary Gallin construction there. The second row is `max-degree.md`. The third row is proved here and remains conditional throughout.

Every SP model is already a Max model, so its closed pure identity diagram is still exactly E_C, of degree 0′. The increase to 0′′ occurs in the B-necessity diagram (3), and the further PA-over-0′′ requirement concerns complete actual truth or adequate models. These different diagrams must not be conflated.

The proof does not settle Con(SP), produce an SP construction, infer an inconsistency from non-effectiveness, or change the Maximalism reference theory. It also does not justify iterating an arbitrary modal construction to all finite jumps. Any further step would require a separately defined reference schema, a suitable persistence/reflection lemma, and an independent consistency analysis.

At the level of completion-space coding, the naive external-proof-gate description gives a Π^0_3 upper bound, but §8.3 improves it to an exact absolute Π^0_2 classification. The completion itself carries the requisite finite-jump oracle in effectively designated sentence bits. This special self-certification argument must not be confused with a general relativized Low Basis claim: effective Π^0_2 sets of reals need not be effectively closed relative to 0′. Oracle axiomatization rank and effective-Borel description rank are separate questions.

## 8. Conditional completion-space corollaries

Continue to assume Con(SP), and use the sentence-bit coding and Stone topology of `effective-refinements.md`. The following claims concern pure complete theories, not arbitrary raw model codes.

“Complete C-theory” means a consistent set closed under finitary C-consequence/deduction, with the C theorem set fixed. It does not mean closure under necessitating every optional accepted sentence. Lightface Π/Σ statements below concern effective descriptions in that fixed coding; ordinary topological closedness is stated separately.

### 8.1 Closed, nowhere dense, and perfect

S(SP) is topologically closed inside S(Max): it is the intersection of the clopen sets requiring each licensed SP instance. It is nowhere dense there. Otherwise some nonempty basic set S(Max+P), with P a finite pure condition, would be included in S(SP). By completeness, the consistent 0′-c.e. theory Max+P would entail all SP instances, contrary to §3's exact oracle cone.

More generally, for every consistent 0′-c.e. theory T entailing Max,

    S(T) ∩ S(SP)

is closed and nowhere dense in S(T). It can be empty. If it contained a nonempty basic open subset S(T+P), the same contradiction would apply to T+P. The claim is about this intersection, since S(SP) need not itself be a subset of S(T).

S(SP) has no isolated point. If Y were isolated by a finite pure condition P, SP+P would be a complete consistent 0′′-c.e. theory. One could decide Y in 0′′ by racing proofs of each sentence and its negation, contradicting §5. Thus S(SP) is a nonempty compact perfect zero-dimensional metrizable space, and is homeomorphic to Cantor space.

Every nonempty basic neighborhood S(SP+P) contains a completion Y with

    0′′<_T Y<_T0′′′,       Y′=0′′′.

Indeed apply relative Low Basis over 0′′ to the consistent witnessed theory SP+P and restrict the resulting completion to pure sentences. The restriction remains above 0′′ by §5, so its jump is at least 0′′′; the containing low-relative code bounds that jump by 0′′′. Equality follows, and the strict upper degree bound follows by jump monotonicity. Consequently such low-relative completions are dense in S(SP).

These are conditional structural consequences. Abstract Cantor-space homeomorphism does not erase the strict oracle separation or the nowhere-dense embedding inside S(Max).

### 8.2 An exact relative effective-Borel level

There is a matching pointclass theorem after specifying the oracle correctly:

    S(SP) is Π^0_2(0′), is not Σ^0_2(0′), and
    contains no nonempty Σ^0_2(0′) subclass.                (10)

For the upper bound, S(Max) is effectively closed relative to 0′. Enumerate pure sentences P_i and let R(i,s) be the 0′-decidable predicate that the 0′-proof enumeration of Max has produced a proof of ¬P_i by stage s. Then

    Y∈S(SP)
       iff Y∈S(Max) and
           ∀i [Y(DP_i)=1 or ∃s R(i,s)].                   (11)

If Max+P_i is consistent, the second disjunct never holds and SP requires DP_i. If it is inconsistent, that instance is unlicensed and imposes no extra requirement. Formula (11) is Π^0_2 relative to 0′.

For the negative assertion, a nonempty Σ^0_2(0′) class is a union of uniformly Π^0_1(0′) classes with at least one nonempty component. Relative Low Basis gives a member of that component computable in 0′′. No SP completion is computable in 0′′ by §5. Hence no such subclass exists.

Intersecting with S(Max), which is Π^0_1(0′), preserves Σ^0_2(0′); therefore the same exclusion holds for relatively effective Σ^0_2(0′) subclasses inside S(Max). This is the properly relativized counterpart of the Max pointclass theorem. It does not turn into a claim about all absolute Σ^0_3 subclasses, for the reason stated at the end of §7.

### 8.3 Sharper absolute classification by self-certifying the finite jump

In fact S(SP) is an **absolute effective Π^0_2 class**. Thus, conditionally on Con(SP), it is Π^0_2 but not Σ^0_2, and contains no nonempty Σ^0_2 subclass. The latter assertions follow immediately from its inclusion in S(Max); the new point is the upper bound.

Fix a computable index map g such that, for every oracle Z,

    Z(k)=Z′(g(k)).                                        (12)

For example, g(k) is the index of an oracle program that ignores its input, asks whether k∈Z, and halts exactly if the answer is yes. Given any sentence-bit real Y, define the total computable-from-Y bitmaps

    A_Y(k):=Y(J2(numeral k)),
    B_Y(k):=A_Y(g(k)).                                    (13)

The following conjunction is Π^0_2 as a predicate of Y:

    ∀k [B_Y(k)=1 ↔ ∃s Halt_s(k,k)],
    ∀k [A_Y(k)=1 ↔ ∃s Halt_s^{B_Y}(k,k)].                 (14)

Here a bounded oracle run uses finitely many bits of B_Y and hence finitely many effectively identified Y bits. Each forward implication has the form ∀k∃s of a computable clopen predicate; each reverse implication is Π^0_1. The first line forces B_Y=0′, and the second forces A_Y=B_Y′=0′′. Conversely true A_Y=0′′ gives B_Y=0′ by (12), so (14) is exactly the desired correctness test on the extracted oracle. In particular it is not an appeal to a general ability to decide a quantifier over Y by querying the fixed oracle 0′.

Because SP is 0′′-c.e., fix an oracle machine enumerating its axioms with oracle 0′′. Let Comp_Y(A) be the condition that Y codes a complete consistent pure C-theory and accepts every axiom enumerated by that machine when its oracle is A. Uniformly in Y,A this has a Π^0_1 description: all coherence failures are finite enumerable bit patterns, and an omitted enumerated axiom is witnessed at a finite oracle-enumeration stage. Substituting A=A_Y makes this a Π^0_1 condition on Y, since all oracle answers are individual Y bits.

Now

    Y∈S(SP) iff (14) holds and Comp_Y(A_Y) holds.          (15)

The forward direction uses numeralwise correctness of J2 in every SP completion. For the reverse, (14) certifies the actual oracle 0′′, so Comp_Y(A_Y) really requires all original SP axioms, with unchanged side conditions. The conjunction in (15) is Π^0_2, proving the upper bound.

The same construction works at **every fixed finite stage T_n** of `iterated-possibility-degrees.md`. Extract A_n(k)=Y(J_n(k)), put A_j(k)=A_n(g^(n−j)(k)) for j≤n, and require A_0=∅ and A_(j+1)=A_j′ for each j<n. This is a finite conjunction of Π^0_2 conditions and certifies A_n=0^(n). Add the Π^0_1 condition accepting the 0^(n)-oracle enumeration of T_n. Consequently every consistent finite T_n, n≥1, has an absolute Π^0_2 completion class with no nonempty Σ^0_2 subclass, even though its theoremhood and model-capacity degrees keep rising.

This exposes the limit of reading computational strength directly from effective-Borel rank: these particular classes all occupy the same absolute Π^0_2 level because their own coordinates carry certificates for the appropriate finite jump. The relative exclusion in §8.2 remains valid; a Π^0_2 class need not be Σ^0_2(0′). In particular a blanket claim that S(SP) has no nonempty absolute Σ^0_3 subclass would be false: S(SP) itself is Π^0_2 and hence Σ^0_3.

The positive-model research lane independently audited the bounded-oracle-run coding and finite-jump self-certification above; no blocker was found.
