# Conditional finite iteration of possibility reflection

22 October 2026. Original ordinary mathematical deductions by OpenAI Codex, with independent modal-source checks by the Gallin-comparison research agent. No database or Lean edits. This note defines additional optional theories: it does not silently replace the reference theories in the original Maximalism or Strong Possibility schemata, and proves no new consistency result.

## 1. Modal operators already expressible in the finitary language

Put O_0=Box and define O_(n+1)=hat O_n, where

    (hat X)p := exists q (q and Box(D_X q -> p)),
    D_X q := not X(not q).

Every fixed finite O_n is an ordinary closed pure term of type tt. In particular O_1=Box_ne and O_2 is two-hat necessity. No infinitary syntax or object-language quantification over natural-number indices is being introduced here.

C proves that every O_n is necessarily normal S4 and that O_n <= O_(n+1), in the necessary pointwise ordering. The base normal S4 laws are theorems of C. The NK preservation step is *The Bounds of Possibility*, Appendix D, Proposition D14; the following direct argument supplies the 4 step without assuming Actuality or Barcan.

Suppose X is necessarily normal S4 and H=hat X. If q witnesses Hp, then q and Box(D_X q -> p). At any base-accessible point where D_X q holds, take r=D_X q. The necessary 4 law for X gives Box(D_X D_X q -> D_X q), so r witnesses Hp there. Consequently Box(D_X q -> Hp), and the original true q witnesses HHp. Thus Hp -> HHp. T follows because true q implies D_X q by T for X, so the boxed implication gives p. For the ordering, Box p implies (hat Box)p by taking q=top. Hat is monotone in the operator ordering: X<=Y gives D_Y q<=D_X q and hence hat X<=hat Y. Induct on n.

Primary source checked by the Gallin-comparison agent: Cian Dorr, John Hawthorne, and Juhani Yli-Vakkuri, *The Bounds of Possibility* (2021), Appendix D, definition of hat on p.405 and Proposition D14 on p.406; accessible PDF https://fitelson.org/piksi/piksi_22/the_bounds_of_possibility.pdf. D16–17 (pp.406–407) separately state the normal S4 facts and hat characterization for Box_ne; the finite induction above is the argument used here, rather than an attributed general theorem whose exact wording was not found.

Every finite O_n is bounded above by Box_5. The source's D22 (p.409) makes every necessarily NKB operator a hat fixed point, so hat(Box_5)=Box_5; monotonicity and O_0<=Box_5 inductively give O_n<=Box_5. This supplies no finite stabilization in bare C. The source's D23 collapse of the second and third hats uses the stronger HS4R background, which is not an assumption of the present hierarchy.

## 2. Optional iterated theories and finite-proof reflection

Define metatheoretically

    T_0 := C,
    T_(n+1) := T_n + { D_n P : P closed pure and T_n+P consistent },

where D_n is the dual of O_n. The extra copy of T_n is explicit in this definition. T_1 is the original pure Maximalist Classicism by the recorded equivalence of its Distinctness and Possibility forms. T_2 is the original Strong Possibility theory, since Strong Possibility already implies Maximalism. For n>=2 the displayed recursion introduces a new optional schema, not one of the original records. All subsequent assertions involving T_n models assume the relevant T_n is consistent.

**Finite-proof reflection.** For every n and every closed pure A,

    T_n proves A  ==>  T_n proves O_n A.                 (1)

For n=0 this is legitimate C theorem necessitation. Let n>=1. A finite proof from T_n uses finitely many non-C axioms, each of the form D_j P for some j<n. Let Q be their conjunction; then C proves Q->A and T_n proves Q. Since D_(n-1)<=D_j and D_j D_j P->D_j P by 4, C proves

    D_(n-1) Q -> Q -> A.

Necessitate this actual C theorem. The true Q witnesses

    exists q (q and Box(D_(n-1)q -> A)) = O_n A.

This proof never necessitates an optional premise or changes a side condition. It also works with any finite conjunction of earlier-stage possibility axioms.

**Exact reflection in the next theory.** If T_(n+1) is consistent, every model M of it satisfies

    M satisfies O_n A  iff  T_n proves A,
    M satisfies D_n P  iff  T_n+P is consistent.         (2)

The forward direction of the first equivalence follows contrapositively: if T_n does not prove A, then T_n+not A is consistent and the displayed T_(n+1) axiom is D_n not A=not O_n A. The reverse direction is (1). Duality gives the second equivalence. The n=1 case is the original Strong Possibility exact diagram, as proved in `strong-possibility-degree.md`; its reflection direction is already explicit in Bacon–Dorr's author-hosted 1 July 2022 Classicism draft, section 2.6, printed page 42.

## 3. Conditional arithmetical jump hierarchy

Write 0^(n) for the nth Turing jump, with 0^(0) computable. The following hold for every fixed n>=1 **if T_n is consistent**:

1. T_n has an axiom enumeration computable in 0^(n).
2. Th(T_n) is Sigma^0_(n+1)-complete under ordinary computable many-one reductions.
3. The set of finite pure conditions F consistent with T_n is Pi^0_(n+1)-complete.
4. An oracle X computes an adequate countable Henkin/BBK model of T_n exactly when it computes binary DNR relative to 0^(n), equivalently has PA degree relative to that oracle.
5. A consistent X-c.e. theory can entail T_n exactly when X computes 0^(n).

An adequate model code here includes uniform closed-term interpretation and actual truth valuation. These statements concern the capacity of an oracle to compute some model, not the exact degree spectrum of a fixed model or of a weaker bare algebraic code.

Here are details of the induction, including the uniform-formula point. The n=1 case is established in `max-degree.md`; the n=2 case is established in `strong-possibility-degree.md`. At the induction step, Th(T_(n-1)) is Sigma^0_n, so deciding consistency of T_(n-1)+P uses 0^(n). Thus T_n is 0^(n)-c.e. Formula (2) fixes the O_(n-1) diagram to Th(T_(n-1)), hence to degree 0^(n).

For the stronger model bound, use the arithmetic already interpreted by T_1=Max. Its impredicative definition of N supplies induction for every ambient formula, including predicates with the finitely iterated modalities. A fixed pure numeralwise-correct predicate J_n for 0^(n) is obtained by applying O_(n-1) to a fixed-formula many-one reduction of 0^(n) to Th(T_(n-1)). The n=1 and n=2 predicates are explicitly given in the companion notes. For later n, the recursion-theorem proof below produces an ordinary computable index map p. Represent its total computation arithmetically and quantify its output before the fixed oracle-halting formula. On every standard input k, the finite computation of p(k), together with PA's uniqueness of deterministic computation, proves equivalence to the required indexed sentence. Thus the reduction can again be put into a single formula Q(v), and J_n(v):=O_(n-1)Q(v) is numeralwise correct. This does not require the internal arithmetic to be externally standard.

Every complete theory of T_n computes binary DNR relative to 0^(n): inspect the truth value of the fixed formula asserting that oracle machine k with oracle J_n halts on k with output zero, and choose the opposite output. Actual convergent computations use finitely many correct standard J_n facts; internal deterministic arithmetic excludes the other bit. Conversely binary DNR relative to 0^(n) chooses a path through the 0^(n)-c.e. Henkin completion tree, using the explicit proof-search construction in `max-degree.md` section 9. The same construction gives an adequate countable term model.

For theoremhood hardness, let U be any consistent 0^(n)-c.e. strengthening of T_n. The two sets

    V_b={k: U proves Halt_b(k,J_n)}, b=0,1,

are disjoint 0^(n)-c.e. supersets of the respective actual diagonal oracle-halting sets. The parameterized oracle recursion theorem compiles, by an ordinary computable p(k), a machine which dovetails: output zero if machine k with oracle 0^(n) halts; output one if its own index p(k) enters V_0. Disjointness proves

    k in 0^(n+1)  iff  p(k) in V_0.

The complete two-case argument is the one in `max-degree.md` section 10.4, with the oracle uniformly replaced. This proves the stated Sigma-completeness without an arithmetic-soundness or standard-model assumption. Consistency of finite conditions is the complementary theoremhood problem. Finally, any consistent X-c.e. strengthening of T_n can decide all the O_(n-1) literals forced by (2), by racing its proof searches for a literal and its negation. It therefore computes 0^(n); conversely T_n itself supplies the enumeration when that oracle is available.

Relativized Low Basis further gives adequate models of degrees d with

    0^(n) <_T d <_T 0^(n+1),   d' =_T 0^(n+1).

Their existence is still conditional on Con(T_n). No new consistency result is hidden in these upper-bound constructions.

## 4. Strict finite hats forced by a consistent next stage

If T_(n+1) is consistent, it forces a pure sentence witnessing that O_n and O_(n+1) differ extensionally. Indeed the different theoremhood degrees in section 3 show that T_(n+1) has some theorem A which T_n does not prove. Equation (1) gives T_(n+1) proves O_(n+1)A, whereas (2) gives T_(n+1) proves not O_n A. Hence

    T_(n+1) proves exists p (O_(n+1)p and not O_n p).    (3)

The n=0 instance uses the known strictness of Max over C; subsequent instances use the established jump separation. In particular consistent T_(n+1) forces all adjacent differences through step n, since it includes the earlier theories. It also refutes O_n=O_(n+1) as an identity of operators.

**A third-stage structural consequence.** Conditional on Con(T_3), T_3 proves not Vicinity and hence not Actuality. The proved record `vicinity-implies-five-implies-two-hat`, with its full proof in `topics/classicism/writeups/vicinity-implies-five-implies-two-hat.md`, gives

    Vicinity -> forall p(Box_5 p -> O_2 p).

Since C proves O_2<=O_3<=Box_5, Vicinity would make O_2 and O_3 agree pointwise at the evaluation point, contradicting (3) for n=2. The proved record `actuality-implies-vicinity` supplies the second conclusion. The first supporting record was conjectured by Cian Dorr on 14 October 2026 and is now recorded as proved: Christopher Sun's argument of 19 October 2026, with the preliminary passage to a strongest 5-necessary proposition added in the record by Claude Opus 5.5. The corollary here is a new conditional deduction from that proved record and the present hierarchy. It uses actual Vicinity, not boxed Vicinity. The failure of strong worlds already derived from SP does not itself refute Actuality, which concerns an actual weak atom; no claim that SP alone refutes Vicinity or Actuality is being made here.

If every finite T_n were consistent, compactness would give a model of their union and hence a model in which every finite hat step is strict. This is only a conditional reduction. Even that conclusion would establish the external schema of finite strictness, not automatically the stronger single `No Collapse` sentence requiring an internal hat-closed separating family. Neither the consistency of T_2=SP nor that of the higher stages is established here.

## 5. Topological form

Conditional on Con(T_(n+1)), its completion locus is nonempty, closed, and nowhere dense in the completion space of T_n. A nonempty relative finite condition F gives a consistent 0^(n)-c.e. theory T_n+F. Such a theory cannot entail T_(n+1), whose axiomatization requires 0^(n+1); therefore some added next-stage axiom can consistently be negated. This gives a nonempty relative sub-open set disjoint from the next-stage locus.

For n>=1 each consistent T_n has a perfect completion space: an isolated completion would be the complete theory of T_n+F for some finite F, decidable in 0^(n), contradicting the DNR lower bound. Relative-low completions are dense by applying Low Basis after any consistent finite condition. The abstract spaces are Cantor spaces; the strict nesting and nowhere-density concern their specified embeddings, not distinct abstract homeomorphism types.

## 6. Status

The direct finite-proof reflection argument and degree induction are deductions from the stated modal laws, the already-audited arithmetic interpretation, and the companion computability arguments. Independent audit is requested before incorporating them. Theories T_n for n>=3 are newly defined optional research objects. The decisive unresolved problem remains consistency; computability complexity by itself supplies no evidence either way.

Independent audit by the Max-degree research lane: sections 2–5 pass. In the finite-support argument, each conjunct D_jP is recovered through D_(n−1)Q→D_jQ→D_jD_jP→D_jP. For the fixed-formula induction, use Q(v)=∃w(Comp_p(v,w)∧Halt_0(w,J_(n−1))). For each standard input k with p(k)=m, PA verifies that finite computation and proves uniqueness of its deterministic output, so T_(n−1) proves Q(k) equivalent to Halt_0(m,J_(n−1)). Global PA-provable totality of p is unnecessary. This theoremhood equivalence is established before applying exact reflection, so no internal truth predicate or standard higher-stage arithmetic root is assumed. The strictness and topological conclusions then follow as stated.

Independent Gallin-comparison audit: sections 1–2 and 4 pass. Necessary NK is inherited by the source's D14; the explicit witness r=D_Xq proves the additional 4 step using only base S4 and necessary 4 for X. The finite-conjunction reflection proof preserves the direction of the dual operator order, and the strictness/compactness argument proves only the external all-finite schema. Primary-source authors and locators were checked directly. The actual-Vicinity corollary follows from the cited proved record without necessitating Vicinity.
