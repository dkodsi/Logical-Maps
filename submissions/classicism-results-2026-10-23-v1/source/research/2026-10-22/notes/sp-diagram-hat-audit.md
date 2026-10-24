# Strong Possibility: theorem diagram and finite hats

22 October 2026. Independent audit for the parent research lane. No database or Lean changes. Pure sentences and the original finitary reference C are retained throughout. The consistency of Strong Possibility is not asserted.

## 1. Exact source and attribution check

The directly inspected author-hosted *Classicism* draft is **1 July 2022**, not the database's usual 16 May 2023 version: <https://andrew-bacon.github.io/papers/Classicism.pdf>. Its §2.6, printed p.42 (PDF page index 41), states that a closed sentence incompatible with Maximalist Classicism cannot be distinctness-preservingly possible consistently with Maximalist Classicism. This already states the underlying implication Max proves A implies Max proves Box_ne A, in contrapositive form. The precise diagram and degree bookkeeping should be presented as a sharpening, not as discovery of that underlying implication. The same page leaves Strong Possibility's consistency unresolved; §3.6, printed p.64, gives a sufficient common-injective-model criterion.

The complete primary book *The Bounds of Possibility* is available in a university-course mirror: <https://fitelson.org/piksi/piksi_22/the_bounds_of_possibility.pdf>. Appendix D, Proposition D14 (p.406), proves that hat preserves necessary NK and yields necessary J. D16–17 (pp.406–407) give the specific S4 facts and hat characterization for Box_ne. D22 (p.409) proves that necessarily NKB operators are hat fixed points. D23's collapse after two hats has the stronger HS4R background; it is not an unconditional C collapse.

## 2. Direct finite-axiom proof of the Max reflection direction

Write

    Bp := Box_ne p := exists q(q and Box(Diamond q -> p)),
    Dp := not B not p.

Suppose Max(C) proves a closed pure A. A finite proof uses only finitely many added Max inequalities. Let Q be their conjunction (or top when the list is empty). By the deduction theorem,

    C proves Q -> A.

For any typed terms s,t, NI gives the C-theorem Diamond(s!=t)->s!=t. Normal modal reasoning consequently proves Diamond Q->Q. Combining this with the displayed deduction and necessitating **that C-theorem** gives

    C proves Box(Diamond Q -> A).

Max proves Q, so Q is a witness for BA. Hence

    Max(C) proves A  implies  Max(C) proves BA.

This argument never necessitates an optional Max axiom. It uses the local deduction convention of the fixed framework and only necessitates discharged C-theorems. It also avoids depending on a separate normality theorem for B.

## 3. What Strong Possibility decides, and what it does not

The recorded implication SP=>Max permits use of §2 inside SP. If Max does not prove A, classical deduction says Max+not A is consistent. The SP instance D(not A) is exactly not BA. Thus, conditional on consistency of SP,

    SP proves BA  iff  Max proves A;
    SP proves not BA  iff  Max does not prove A.

In every SP model, the truth diagram A|->BA is consequently exactly the theorem set of Max. The computational classification of that theorem set is supplied by the separate degree lane; this audit does not substitute a complexity argument for consistency.

The reflection premise is essential. It says **Max proves A**, not **SP proves A**. For example, the recorded one-individual argument makes SP prove E1 := forall x,y:e(x=y), whereas the two coalesced roots make both E1 and not E1 consistent with Max. Therefore SP proves E1 and not B E1. This is compatible with the lemma and shows precisely why it cannot simply be upgraded to all SP proofs at the same modality.

Existing SP constraints do not invalidate the argument: failure of ordinary BF and Functionality, failure of truth=>B-truth, and the requirement of one individual are all compatible with its proof. The actual truth of a universal sentence need not be B-persistent, because the modality may bring new entities into the quantifier domain. In particular the known SP=>E1 fact is not a new consistency obstruction.

## 4. General modal facts needed for finite hat iteration

Fix the ordinary base Box of C. For any closed operator X of type tt put D_X p := not X not p and

    H_X p := exists q(q and Box(D_X q -> p)).

All operator properties in the following induction are asserted necessarily, with the quantifiers inside the base Box. This scope supplies the laws at every point used in the proof.

**NK inheritance.** If X is necessarily NK, H_X is necessarily NK. N uses any actual tautology as witness; K combines witnesses q and r into q and r and uses D_X(q and r)->D_Xq and D_Xr. This is the content of the source's D14, which also yields J.

**T inheritance.** If X is necessarily T, then q implies D_Xq. Hence any witness q and Box(D_Xq->p) for H_Xp gives p. Applying the same argument under the base Box yields necessary T for H_X.

**4 inheritance.** If X is necessarily NK4, then H_X is necessarily 4. Suppose q and Box(D_Xq->p). The latter boxed conditional persists by base 4. At any base-accessible point where D_Xq holds, choose r=D_Xq as a witness for H_Xp. The dual of X's 4 gives D_XD_Xq->D_Xq, so that point has Box(D_Xr->p). Therefore the original point has Box(D_Xq->H_Xp). Together with q this witnesses H_XH_Xp. Discharging the assumptions and using the persistence of necessary operator properties yields the necessary version. No BF or Actuality is used.

**Monotonicity.** If Box forall p(Xp->Yp), then Box forall p(H_Xp->H_Yp). The dual inequality is D_Yq->D_Xq, so the same witness for H_Xp witnesses H_Yp. In particular define O_0=Box and O_(n+1)=H_(O_n). The N property gives O_0<=O_1, and monotonicity gives the chain O_n<=O_(n+1). By the preceding inheritance arguments every finite O_n is necessarily NKT4.

All these operators are bounded above by Box_5. Indeed O_0<=Box_5 by N, Box_5 is a hat fixed point by D22, and monotonicity inducts. This bound does not imply that finitely many hats stabilize in C. The stronger source stabilization theorem requires hypotheses not available in the proposed finitary hierarchy.

## 5. The purely modal part of the proposed theory iteration

The parent proposes

    T_0=C;
    T_(n+1)=T_n + {D_n P : P closed pure and Cons(T_n+P)},

where D_n is the dual of O_n. Thus T_1 is ordinary Max, while T_2 is equivalent to Strong Possibility over C. The following checks only the modal reflection mechanism, leaving consistency and complexity to their separate arguments.

For n>=1, every added axiom of T_n has the form D_j P with j<n. Since O_j<=O_(n-1), its dual inequality is D_(n-1)<=D_j. Therefore

    C proves D_(n-1)(D_j P) -> D_j D_j P -> D_j P,

using 4 of O_j. A finite conjunction Q of earlier added axioms is consequently backward persistent: C proves D_(n-1)Q->Q. If T_n proves A, finite proof and deduction give C proves Q->A. The proposition Q now witnesses O_n A=H_(O_(n-1))A, exactly as in §2. At n=0 ordinary theorem necessitation gives the base case. Hence

    T_n proves A implies T_n proves O_n A.

If T_n does not prove A, the next layer contains D_n(not A), namely not O_n A. Therefore **if T_(n+1) is consistent**, its O_n theorem/truth diagram is exactly the theorem set of T_n. This is a conditional hierarchy. Neither the operator induction nor the reflection calculation establishes consistency of SP or any later layer.

## 6. Recovering valuation from Actuality, and reflected valuation from Vicinity

Here an application/equality presentation gives numbered typed objects, computable total application (or decidable graphs from which it can be searched), and decidable equality representing original actual identity. Merely c.e. equality, syntactic equality of arbitrary representatives, and a bare category/action code are not sufficient. The reductions below may use finitely many presentation indices as fixed parameters; their degree conclusions do not assert that those indices are uniformly discoverable.

Let a witness Actuality, namely a and forall p(p→a≤p). Then, at the evaluation point,

    p is true  iff  a≤p  iff  a∧p=a.

The forward direction is the witness property; the reverse uses the true a and T. The final equivalence is the Boolean-algebra/Intensionality characterization of the C entailment order. Thus an application/equality code computes actual valuation by hardcoding a and the conjunction operation. If both indices are explicitly named, this conversion is uniform. Naming a alone suffices only when the logical-operation indices are already part of the presentation format.

This uses exactly the definition in `topics/classicism/principles/actuality.yaml`. The proved records `necessary-plenitude-r-implies-necessary-actuality` and `necessary-actuality-implies-actuality` give Actuality in P=C+□Plenitude, and hence in F. Accordingly the positive application/equality presentations inherit the previously established bounds for application/equality/valuation presentations. With weak Infinity their oracle capacity is exactly PA degree; with external standard Frege arithmetic the nonhyperarithmetical lower bound, and computation of each hyperarithmetical set, apply as well. These claims use fixed predicates and finitely many indices and do not require a general lambda-term interpreter.

For the second lemma let v witness Vicinity, as defined in `topics/classicism/principles/vicinity.yaml`: v is true and every true q satisfies v≤◇q. Then

    Bp  iff  □(◇v→p)  iff  (◇v)∧p=◇v.                 (V)

For the forward direction, choose a true q witnessing Bp, so □(◇q→p). Vicinity gives □(v→◇q); normal modal reasoning and base 4 give □(◇v→◇◇q) and □(◇◇q→◇q). Composing yields □(◇v→p). Conversely, v itself witnesses Bp whenever the latter boxed implication holds. No BF or necessitation of the optional Vicinity premise occurs. This is a direct deduction from the recorded witness form and the base S4 laws, compatible with the principal-necessity calculations used in the source writeup `vicinity-implies-five-implies-two-hat.md`; the code consequence is new here.

Hardcoding v, Diamond and conjunction therefore computes the B-truth predicate on presented proposition objects using application/equality alone. Computing its entire *syntactic* closed-sentence diagram additionally requires a way to interpret arbitrary closed terms. For the degree lower bound this extra uniform interpreter is unnecessary: hardcode the numeral constructors and the fixed pure predicate giving the many-one hardness reduction to Max theoremhood, compute each of its standard instances, and apply (V).

Consequently any application/equality presentation of a model of SP+Vicinity computes 0′′, by SP's exact B diagram. Any such presentation of SP+Actuality has PA degree over 0′′, because Actuality recovers the actual valuation needed for the fixed DNR predicate. Both assertions are conditional statements about models if they exist. Neither Con(SP+Vicinity) nor Con(SP+Actuality) is established. Nor does the Vicinity argument by itself upgrade its 0′′ bound to PA-over-0′′: B-truth and actual truth are distinct predicates.
