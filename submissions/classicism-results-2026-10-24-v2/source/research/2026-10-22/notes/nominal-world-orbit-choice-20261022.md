# Finite-support world actions separate Intensional Choice

22 October 2026. Original mathematical construction and proofs by the Gallin-audit research agent, with the ordered-tuple reservoir extension independently suggested by the parent research agent. No human verification, Lean verification, main-database edit, or literature-novelty claim. This develops the finite-support construction audited in `.reproduction/classicism-research/audit-gallin-20261022.md`; exact source principles are those in the bundle, especially Intensional Choice and the quantified Frege Infinity axioms.

## 1. A common construction and its stable positive theory

Let A be countably infinite, G=Sym(A), and E=N with trivial G-action. Let W be any nonempty infinite G-set whose every element has finite support in A. In the cases below W is a set of finite tuples or finite subsets of A. Set D_t to **all finitely supported subsets of W**. At every original arrow σ→τ take all finitely supported functions D_σ→D_τ under conjugation. Evaluate p:t at w∈W by membership. Equality has value W/∅. An auxiliary full-Gallin-type expansion is obtained by bases E,W,o={0,1}, all supported functions at every arrow, and the same actions.

The proofs in the audit report apply unchanged:

- Boolean operations, equality, quantification and λ-interpretation are equivariant; intersections defining admitted quantifiers have the support of their argument. Thus H and C, with the exact H-theoremhood restriction on Logical Equivalence, are sound.
- Equality is rigid, so C5 holds.
- Every nonzero relational object contains a world/argument point. Its singleton-point relation has the union of the finite supports of that tuple and world, and is an atom. Thus all-type Atomicity holds at every world.
- At every original type the Frege numeral objects have empty support. The characteristic predicate of their external set is admitted and inductive; hence the impredicative Frege numbers are exactly the external standard numeral objects. Every D_σ is infinite, so all quantified Frege Infinity axioms hold, including AI_e and AI_t, at all worlds. Sum and Prod have their standard values.
- Every auxiliary type generated only from E and o has trivial action and its **full external** function domain. Thus the ordinary full standard finite-type mathematical hierarchy is retained. The original C language interprets it by the supported hereditary rigid codes described in the audit report, with core-restricted quantifiers.

Write P=C5+Atomicity, equivalently C+□Plenitude. Each example below therefore satisfies P, both boxed quantified Infinity axioms, and the same full standard E/o mathematical core. The common construction is available in ZF; Choice for arbitrary relations inside the full core is a further valid observation in ambient ZFC.

The acting group is a tool for constructing domains. Empty support does **not** mean that an object is denoted by a closed pure C term. In particular the star and orbit predicates below need no pure definition: the original Choice principles universally quantify over all admitted predicate objects, so an explicit admitted witness suffices to refute them.

## 2. Unordered pairs of atoms as worlds: Intensional Choice fails

Take

    W=[A]^2={ {a,b}:a,b∈A, a≠b }

with the induced G-action. This is not the full Sym(W) action used in the one-atom-world model. D_t is therefore not the finite/cofinite algebra of W. It contains, for each a∈A, the **star proposition**

    p_a={w∈[A]^2:a∈w}.

The singleton {a} supports p_a. The propositions p_a are pairwise distinct: for a≠b choose c outside {a,b}; then {a,c} belongs to p_a but not p_b. Also g·p_a=p_(ga).

Define an admitted property F:t→t by

    F(p)=p if p=p_a for some a∈A,
    F(p)=∅ otherwise.

The set of stars is invariant, so F has empty support. Its output at an eligible star is an admitted proposition; all other outputs are ∅. At the world {a,b}, exactly p_a and p_b are F-instances. Thus the original antecedent □∃p Fp is true.

Suppose G_0:t→t witnesses Intensional Choice for F. Then G_0≤F and □∃!p G_0p. Let S be a finite support of G_0, and choose distinct a,b outside S. The transposition g=(a b) fixes S and the world w={a,b}, while exchanging p_a and p_b. Equivariance gives

    w∈G_0(p_a) iff w∈G_0(p_b).

Since F has exactly these two instances at w, G_0 cannot have exactly one instance there. This contradiction proves failure of the original σ=t instance of Intensional Choice. It fails at every designated world because the claimed G_0 must select at **all** worlds. Hence the model satisfies the boxed negation of that closed instance.

The distinction between fixing a world and fixing every atom in its support is the mechanism. The transposition fixes the unordered world {a,b} even though it does not fix a and b individually. The finite-exception proof of Intensional Choice for W=A therefore cannot be transferred to this W.

This yields the direct ZFC consistency separation

    P + AI_e + AI_t + ¬IntensionalChoice_t,

while the W=A construction yields

    P + AI_e + AI_t + □IntensionalChoice_(all types).

Both have a full standard mathematical core. They differ in Intensional Choice without changing arithmetic standardness or requiring a choiceless metatheory.

### Ordinary Choice also fails

The original pair-of-Boolean-atoms relation U(p,q), choosing one atom below every p that is a union of exactly two atoms, is again serial. Given a purported supported selector, choose disjoint fresh worlds u={a,b} and v={c,d}. The permutation swapping a with c and b with d fixes {u,v} as an input proposition but exchanges its two singleton-world outputs. This refutes Functional Choice at (t,t). For a selecting relation at a designated world, include that world's finite support in the fixed finite set before choosing a,b,c,d; the same existence/uniqueness contradiction refutes Relational Choice.

### This does not refute individual-output Intensional Choice

At any finite support S, Fix(S) has only finitely many orbits on [A]^2: individual pairs inside S, one orbit of pairs {s,a} for each s∈S and a outside S, and the orbit of pairs wholly outside S. For a supported necessarily inhabited F:e→t, its individual-output fiber is constant on each such orbit because G acts trivially on E. Choose one individual from each of these finitely many nonempty fibers. The resulting section has finite support S and its graph is admitted. Thus Intensional Choice at e holds. The same reasoning works when the allowed witnesses range over any of the empty-supported full-core fields. The all-type failure genuinely uses world-dependent proposition objects.

## 3. Fixed-length ordered tuples as worlds: all Intensional Choice holds

Fix a positive integer k and take

    W=A^{#k}={ (a_1,...,a_k):the coordinates are pairwise distinct }.

The one-coordinate case is the original W=A model. We prove all-type Intensional Choice for every fixed k.

Let F:σ→t have finite support S, and suppose every w∈W has an F-instance. There are only finitely many Fix(S)-orbits of W: the orbit is determined by which coordinate positions contain which members of S; the remaining coordinates are distinct fresh atoms and are interchangeable. For each orbit i choose a representative w_i and an F-instance x_i at w_i. Choose a finite support T_i of x_i. Write C_i for the coordinate set of w_i and

    E_i=T_i\(S∪C_i),  r_i=|E_i|,  r=max_i r_i.

Choose a fixed finite reservoir R⊆A\S of cardinality r+k, with a fixed ordering; also fix an ordering of each E_i. These are finite choices.

For w in orbit i, define an injective finite partial map as follows:

1. Fix every atom of S.
2. Send each coordinate of the ordered tuple w_i to the corresponding coordinate of w.
3. Send the r_i ordered atoms of E_i to the first r_i atoms of R outside the coordinate set of w.

This map is consistent because w and w_i lie in the same Fix(S)-orbit. Its third set of target points is disjoint from S and the coordinates of w. There are enough such points since |R|=r+k and w has only k coordinates. Thus it is injective. It extends to a permutation g of A fixing S; a finite injective partial bijection with equally sized finite domain and range can be completed on their finite union and taken to be the identity elsewhere. Define

    h(w)=g·x_i.

This is independent of the extension g because the partial map specifies g on all of T_i, a support of x_i. Since g fixes S and sends w_i to w, equivariance of F shows w∈F(h(w)).

Now let q fix S∪R pointwise. It preserves each Fix(S)-orbit. The chosen ordered reservoir list outside the coordinates of qw is the same as for w, because q fixes R. Hence the prescribed partial map for qw agrees on T_i with q composed with the prescribed map for w. It follows that h(qw)=q h(w). Thus h has finite support S∪R.

As in the original audit, define the allowed original predicate

    G_0(x)={w:h(w)=x}.

Each value has support contained in S∪R∪supp(x); the whole function has support S∪R. Its graph is therefore admitted, G_0≤F, and each world has exactly one G_0-instance. This proves all-type Intensional Choice, including individual witnesses without a forbidden e-returning operation. The proof works at every designated world, so □Intensional Choice holds.

Ordinary Functional and Relational Choice still fail. Choose two ordered worlds with disjoint fresh coordinate sets, and use the permutation swapping the corresponding coordinates of those worlds. It fixes their unordered two-element set, hence fixes the input proposition to the same pair-of-Boolean-atoms relation, but exchanges its eligible outputs. The contradiction is identical to §2.

Thus every fixed-length ordered-tuple model strengthens the original separation:

    P + AI_e + AI_t + □Intensional Choice + ¬FunctionalChoice_(t,t).

No bound on the sizes of witnesses' supports was assumed in advance; the finite reservoir is chosen from the finitely many orbit witnesses relevant to the particular F.

## 4. Unbounded ordered tuples: Intensional Choice can fail again

Let W be the disjoint union of A^{#k} for all finite k≥0, with tuples of different lengths distinct. Every world still has finite support, but the coordinate lengths are unbounded. Define p_a={w:a occurs as a coordinate of w}. These star propositions are distinct and supported by {a}. Define

    F(p_a)=W\p_a,
    F(p)=∅ for nonstars p.

This is well-defined and equivariant. Every world is a finite tuple, so there is always a fresh a outside its coordinates; hence □∃p Fp holds.

Suppose G_0 selects one F-instance at each world and has finite support S. Choose a tuple w listing every member of S exactly once (the empty tuple if S is empty). Any eligible selected object is p_a for some a outside S. Choose b outside S∪{a}. The transposition (a b) fixes S and fixes the ordered tuple w pointwise, but exchanges p_a and p_b. Equivariance contradicts uniqueness of G_0 at w. Therefore Intensional Choice at t fails.

Unlike the fixed-length cases, this failure does not come from an internal permutation of the selected world's coordinates: all coordinates are fixed. It comes from the lack of a finite reservoir that stays fresh for worlds of every finite length. This shows that removing the unordered symmetry alone is not enough; bounded support size and finitely many orbit patterns were substantive in §3.

This model also distinguishes Dedekind behavior. Let q_n be the proposition that the world tuple has length n. Every q_n has empty support, and these propositions are pairwise distinct. The map shifting q_n to q_(n+1) and fixing all other propositions is an admitted equivariant injective nonsurjection of D_t. Thus D_t is internally Dedekind-infinite here, although Intensional Choice still fails. No closed pure term defining the sequence q_n is claimed; its equivariant semantic graph suffices for the existential statement.

## 5. Fixed-point finiteness and the numerical-choice obstruction

For W=[A]^2 and finite S, the number of Fix(S)-orbits on W is

    binomial(|S|,2)+|S|+1.

Therefore D_t has exactly 2 raised to this finite number of elements fixed by Fix(S). For fixed-length ordered worlds there are likewise finitely many Fix(S)-orbits, hence only finitely many fixed propositions. The consequences proved for W=A carry over:

- Every supported map from a standard empty-supported Frege number field into D_t has finite range.
- D_t and the world-atom field are internally Dedekind-finite, despite satisfying the quantified Frege Infinity assertions.
- An admitted actually countable family of propositions has externally finite actual extension, by the source Ctbl definition and the fixed-point argument.
- There is no selector for the pure numerically indexed relation that, at numeral z_n, asks for a proposition with exactly n atoms below it. Any supported selector would have finite range but would need infinitely many distinct finite cardinalities.

The first three bullets do **not** automatically transfer to the unbounded-length model; §4 explicitly refutes its Dedekind-finiteness. All models still have standard Frege arithmetic and the full ordinary E/o sector.

## 6. Scope table

| World action | All-type Intensional Choice | Functional Choice (t,t) | Proposition domain Dedekind-infinite | Full standard E/o core |
|---|---:|---:|---:|---:|
| A, natural full permutation action | holds | fails | no | yes |
| A^{#k}, fixed positive ordered length | holds | fails | no | yes |
| [A]^2, induced unordered-pair action | fails at t; holds at e | fails | no | yes |
| Disjoint union of all finite distinct ordered tuples | fails at t | fails | yes | yes |

All rows satisfy P and both quantified original Infinity axioms, with their boxed forms. The table lists only independently proved assertions. It makes no claim that these are new in the literature or a complete classification of all nominal world actions.

## 7. A purity guardrail: the acting group is not the whole automorphism group

The preceding orbit distinctions must not be mistaken for pure definable distinctions between evaluation worlds. If u,v∈W, the transposition π of just those two worlds has support contained in supp(u)∪supp(v) as a map on W. Any original g fixing that finite set fixes u,v and commutes with π. Extend π to original typed domains by the identity on E, direct image on propositions, and recursive conjugation on function types. By induction it commutes with all g fixing that finite set; an element supported by T is sent to one supported by T∪supp(u)∪supp(v). Thus each typed domain is preserved. The extension is a bijection at every sort and preserves application, Boolean operations, equality, quantification, and λ-interpretation.

Consequently π is an isomorphism between the original pointed models at u and v. All evaluation points have the same closed pure theory, consistently with the recorded No Pure Contingency consequence of P. An object can have empty support for the initially chosen G and still be moved by these additional semantic automorphisms. In particular the stars and length propositions are not thereby proved pure-definable. This also explains why their use as universally quantified Choice counterexamples is legitimate without producing a pure sentence that singles out a world orbit.

## 8. An exact independence square: Intensional Choice versus Dedekind Infinity

Let B denote the original object-language theory

    C + □Plenitude + □AI_e + □AI_t,

and let IC denote all-type Intensional Choice. Define the single original pure sentence

    DedInf_t := ∃f^(tt) [
        ∀p^t q^t ((fp=fq)→p=q)
        ∧ ∃r^t ∀p^t (fp≠r)
    ].

All arrows here are allowed. This is operational Dedekind Infinity at the proposition type; it must not be substituted for the source's Frege Infinity axiom.

The preceding constructions and one standard full model realize all four combinations:

| | ¬DedInf_t | DedInf_t |
|---|---|---|
| **All-type □IC** | Finite-support model with W=A | Full Gallin model with E=W=N |
| **¬IC_t** | Finite-support model with W=[A]^2 | Finite-support model with W=all finite distinct ordered tuples |

Every displayed model satisfies B, and every displayed model has an interpreted ordinary mathematical core that is the full standard hierarchy over N and two truth values. The latter is an additional **semantic restriction on these witnesses**, not a claim that external fullness is expressed by one original C axiom.

Only the upper-right entry has not been fully spelled out above. In the full Gallin model take D_t=P(N) and all allowed external functions at every arrow type. It satisfies B and all-type □IC in ZFC: at each world choose one witness for a necessarily inhabited property, and fullness admits its graph. Define f:P(N)→P(N) by

    f(p)={n+1:n∈p}.

This is an available operation of original type tt. It is injective; it is not onto because no output contains 0. Hence DedInf_t holds. As throughout, equality and the other displayed conditions are world-invariant, so each verdict holds at every world.

For the lower-right entry, the admitted map q_n↦q_(n+1), identity off {q_n:n∈N}, is a genuine injection of the **whole** proposition domain into itself with q_0 omitted. It is not merely an injection of a subfamily or an external countability observation. The lower-left and upper-left failures of DedInf_t were likewise proved for every admitted operation, using finite fixed-point sets.

Consequently neither IC nor its failure determines DedInf_t, and neither DedInf_t nor its failure determines IC, over B. More precisely, the lower row refutes the specific t-instance of IC, while the upper row satisfies the whole schema. The square remains realized under the strong semantic restriction to a full standard ordinary mathematical core. It is therefore not explained by nonstandard arithmetic, missing ordinary subsets of N, or a metatheoretic failure of Choice.

This is a relative-consistency/independence statement furnished by explicit models in ZFC. It is not a claim that either principle has no other known consequences, or that the square is novel in the literature.
