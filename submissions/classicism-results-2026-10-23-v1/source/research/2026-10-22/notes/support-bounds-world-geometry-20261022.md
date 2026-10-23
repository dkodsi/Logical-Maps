# Support bounds and world geometry: further Intensional Choice classifications

22 October 2026. Original mathematical analysis by the Gallin-audit agent, incorporating the root agent's proposed constructions and independently checking their support and type details. Metatheory: ZFC. No main records, Lean, named human verification, or novelty claim.

Use an infinite atom set A, G=Sym(A), trivial individual sort E=N, a nonempty G-set W of worlds, and the full hierarchy of functions supported by the stipulated support ideal. Truth is world membership. All worlds are assumed supported by that ideal. The equivariance, parameterized lambda and quantifier proofs in `countable-support-choice-countermodel-20261022.md` apply. Thus C5 and all-type Atomicity hold. If W is infinite, all original domains are infinite and all Frege number domains are standard, so both boxed Frege Infinity axioms hold. The E/o hereditary core is full and standard.

## 1. A common-reservoir theorem

Let mu be an infinite cardinal, assume |A|≥mu^+, and allow supports of cardinality at most mu, equivalently <mu^+. Suppose every world w has a **strong support** L_w of cardinality strictly less than mu:

    Stabilizer_G(w)=Fix(L_w).

Then all-type boxed Intensional Choice holds, with no restriction on the number of world orbits. The strict inequality |L_w|<mu is significant.

Fix F:sigma t with every world fiber nonempty, and a support S for F of size at most mu. Choose R⊆A\S of cardinality mu and put K=S∪R. For each orbit of W under Fix(K), choose a representative w, an eligible output x, and a support T for x of size at most mu.

Choose a permutation g fixing S∪L_w pointwise which maps T\(S∪L_w) into R\L_w. This is possible because |R\L_w|=mu, while the moved domain has size at most mu. The specified partial bijection extends to a permutation: after deleting sets of size at most mu, both complements have cardinality |A|. Put y=gx. The permutation fixes F and w, so y remains eligible. It has support contained in K∪L_w.

If h∈Fix(K) fixes w, strongness gives h∈Fix(L_w); hence h fixes y. Therefore define the chosen output on the entire Fix(K)-orbit of w by h(w)↦h(y). This is well-defined because the representative stabilizer fixes y. Doing this on every orbit gives an external choice map c:W→D_sigma equivariant under Fix(K).

The original graph G(z)={w:c(w)=z} is admitted: each value has support K∪supp(z), and the curried graph has support K. It is a global singleton-fiber subrelation of F and witnesses the exact IC formula. This holds at every evaluation world. The arbitrary set of orbit choices is made in the stated ZFC metatheory.

For mu=aleph_0, this covers every world G-set whose worlds have finite strong supports, even with infinitely or uncountably many orbits and with no fixed finite bound on their support sizes. Thus the finite-support infinite-orbit obstruction disappears when countable supports are admitted at the higher types.

## 2. Ordered infinite tuples give a sharp obstruction

For an infinite cardinal mu, keep supports of size at most mu and |A|≥mu^+. Let W=A^{#mu}, the set of injective functions from the ordinal mu into A, with coordinatewise action. The range of w is a strong support of size mu. In this model IC_t fails.

Underlying atoms a∈A are not themselves original propositions or world atoms. Encode them by the admitted **star propositions**

    p_a={w∈W:a∈range(w)}.

The map a↦p_a is injective and equivariant, and p_a has support {a}. To distinguish p_a from p_b, choose a mu-tuple whose range includes a and excludes b; |A|≥mu^+ makes this possible.

Define the admitted empty-supported property F:t t by

    F(p_a)=W\p_a,
    F(p)=empty if p is not any star p_a.

Its eligibility condition at w is exactly that the output be p_a for an atom a outside range(w). Every fiber is nonempty, since |range(w)|=mu<|A|.

Suppose an IC selector graph G has support S, |S|≤mu. Choose w whose range includes S and has cardinality mu. Its unique selected output is p_a for a∉range(w). Choose b outside range(w) distinct from a. The transposition (a b) fixes S and w, hence preserves G and its unique output there, but sends p_a to the distinct p_b. Contradiction.

In particular countably supported models with W=A^{#omega} refute IC_t although every world is strongly supported. The obstacle is the size of the world support, not a local permutation symmetry of its coordinates.

Together with §1 this gives the exact statement, for each cardinal lambda≤mu,

    W=A^{#lambda}, supports≤mu: IC_t iff all-type Box IC iff lambda<mu.

Here lambda=0 gives the singleton world. The theorem makes no assertion about tuple lengths larger than mu, whose worlds would fail the required support bound.

## 3. A star-union lemma for finite-support worlds

The remaining classification assumes every world has a **finite** support, although higher-type objects may have supports <kappa for an arbitrary infinite kappa. Assume |A|≥kappa. Finite least supports of worlds exist by the ordinary finite-support intersection argument. Every orbit has the form A^{#k}/H for a finite k and H≤Sym(k). A world is strong exactly when its local H is trivial.

Fix one moving orbit O_* with support size k>0 and define p_a only on O_* by

    p_a={w∈O_*:a∈supp(w)}.

For every B⊆A of cardinality <kappa put

    p_B=union_{a∈B} p_a.

Then p_B is supported by B, the map B↦p_B is injective, and every allowed support T for p_B contains B. This special exact-support statement does not invoke an intersection theorem for arbitrary infinite supports.

For injectivity, if a∈B\C, choose a k-element world support containing a and disjoint from C, and a world on that support. It belongs to p_B but not p_C. There are enough fresh atoms because |C|<kappa≤|A|. For the support assertion, if a∈B\T, choose b outside B∪T. The transposition (a b) fixes T but replaces B by (B\{a})∪{b}; injectivity proves it moves p_B, a contradiction. Thus B⊆T.

## 4. Exact classification when every world has finite support

Assume |A|≥kappa, supports at all higher types have cardinality <kappa, and every world has finite support. The following classification holds in ZFC.

- If the G-action on W is wholly trivial, all-type boxed IC holds for every infinite kappa.
- Otherwise, if kappa is an uncountable successor cardinal, all-type boxed IC holds exactly when every world is strong; the number of orbits is unrestricted.
- Otherwise, if kappa is a regular limit cardinal, including aleph_0, all-type boxed IC holds exactly when every world is strong and W has fewer than kappa G-orbits.
- If kappa is singular and W has a moving orbit, IC_t fails.

In each positive case all types satisfy boxed IC. In each negative case the failure is already IC_t. These are claims about this specified support family, not global C equivalences.

### 4.1 Wholly trivial action and local symmetry

For wholly trivial W, E and o are also trivial, so the entire hierarchy is full with trivial action and ordinary metatheoretic choice supplies IC.

For a nonstrong world orbit O=A^{#k}/H, choose a nonsingleton H-orbit I of coordinate positions. At w=[a_1,...,a_k], permit exactly the stars p_a with a among the coordinates indexed by I; outside O permit bottom. This is an invariant admitted relation with all fibers nonempty. Given a proposed selector support S<kappa, choose all k coordinates outside S. A local permutation in H fixes w and S but moves the chosen eligible star. This contradicts uniqueness. The star encoding is injective as above. Thus any local symmetry is an obstruction regardless of kappa.

### 4.2 Successor supports

Write kappa=mu^+ with mu infinite. Every finite strong world support has size <mu. The common-reservoir theorem of §1 applies verbatim, giving the claimed sufficiency with arbitrary many orbits. The local obstruction gives necessity.

### 4.3 Regular limit: sufficiency

First take uncountable regular kappa. Suppose every world is strong and there are theta<kappa G-orbits. For F with support S<kappa, the number of Fix(S)-orbits of worlds is <kappa. Indeed, on each finite ordered-tuple orbit, a Fix(S)-orbit is specified by which coordinates lie in S and their values there. Summing over theta orbits gives at most max(theta,|S|,aleph_0)<kappa possibilities.

Choose a witness x_i on each such orbit representative. Regularity bounds the union of their <kappa supports below kappa. Choose an infinite cardinal mu<kappa bounding |S| and their support sizes, and a reservoir R of size mu disjoint from S. Every world has a witness with support size at most mu: transport the representative witness by a permutation fixing S. The orbit-by-orbit construction of §1 now works with K=S∪R, since every finite world support leaves mu reservoir points available. K has size <kappa.

For kappa=aleph_0 the preceding maximum-with-aleph_0 estimate cannot be used. There are finitely many G-orbits and finitely many Fix(S)-orbits; take the finite maximum r of the witness support sizes and finite maximum k of world support sizes. A reservoir of size r+k suffices. The same stabilizer argument gives the finite-supported selector. This is exactly the finite-orbit ordered-tuple proof from the companion classification.

### 4.4 Regular limit: too many orbits

Assume a moving orbit exists and W has at least kappa G-orbits. Choose distinct O_i for i<kappa and positive cardinals lambda_i<kappa cofinal in kappa; for kappa=aleph_0 use unbounded positive finite sizes. Use the star-union coding of §3.

At w∈O_i permit precisely the outputs p_B with

    |B|=lambda_i and B disjoint from supp(w).

Outside all selected O_i permit bottom. This gives an equivariant admitted F:t t. For a fixed p_B, its value is supported by B, since the orbit label is invariant and the disjointness condition transports with B. For bottom take the invariant complement of the selected orbits. Every fiber is nonempty because each world support is finite and the required size is <kappa≤|A|.

If G were a selector supported by S<kappa, its unique output p_B at w would be fixed by Fix(S∪supp(w)). The exact-support lemma gives B⊆S∪supp(w), and eligibility gives B disjoint supp(w), so B⊆S. Choose i with lambda_i>|S| and any w∈O_i. This is impossible.

The disjointness clause is necessary for a uniform argument including kappa=aleph_0, where the finite support sizes of different world orbits need not have a common bound.

### 4.5 Singular supports: a marked-world obstruction

Let kappa be singular, mu=cf(kappa)<kappa, and fix a moving finite-support orbit O_*. Choose mu distinct worlds w_i in that orbit whose finite supports have union S of size <kappa. Explicitly, fix k-1 atoms and let the last coordinate range over mu fresh atoms in an A^{#k}/H presentation; the resulting least-support sets differ, so the worlds are distinct. The set S has cardinality mu.

Choose infinite cardinals kappa_i<kappa cofinal in kappa. At w_i permit outputs p_B with |B|=kappa_i and B disjoint supp(w_i). At every other world permit bottom. This F is supported by S: Fix(S) fixes every marked world and its support pointwise, preserves the cardinality/disjointness rules under B-transport, and preserves the complement of the marked worlds. Each value F(p_B), being a subset of the marked worlds, is itself supported by S. All fibers are nonempty.

For any selector support T<kappa, uniqueness at w_i and the exact-support lemma imply B⊆T∪supp(w_i). Eligibility then gives B⊆T. Choose i with kappa_i>|T|. Contradiction. The use of fewer than kappa marked worlds is legitimate at singular kappa; their required output sizes are what become cofinal and defeat a common support.

## 5. Additional columns and limits

For the finite-support-world family in §4, Functional Choice and Relational Choice hold exactly when the world action is wholly trivial. If there is a moving orbit, choose two worlds in it with disjoint finite supports fresh from a proposed selector support. A coordinatewise block-swap fixes their two-element proposition and interchanges its only possible singleton-atom outputs. This is the same pair obstruction as in the companion notes. For Relational Choice also include the actual world's finite support among the fixed parameters.

For every uncountable kappa and infinite W in this family, D_t is Dedekind-infinite: choose countably many distinct worlds, shift their singleton propositions, and fix all other propositions. The union of those worlds' finite supports is countable and therefore <kappa. If W is finite, D_t is finite. At kappa=aleph_0 the earlier exact criterion remains: D_t is Dedekind-infinite exactly when W has infinitely many G-orbits.

The large-world-support example of §2 lies outside §4's finite-world-support hypothesis. It shows why that hypothesis cannot be silently dropped from the successor-cardinal clause. No classification is asserted here for arbitrary infinite world supports at regular limit kappa.
