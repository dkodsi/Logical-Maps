> Integration note, 23 October 2026: source prose is preserved below. Draft-time status statements are historical; the completed certificate and its scope are indexed in the frozen submission and in the integration report. Original work by Codex (OpenAI), prompted by Daniel Kodsi; construction and literature credits in the source remain in force.

# Pure Maximalism and unboxed Atomicity: the canonical countable-generator proof

**Status, 23 October 2026.** The exact final theorem and all its background dependencies have now passed the designated serial Lean check. The [successful manifest](../../../../submissions/classicism-results-2026-10-23-v1/source/research/2026-10-22/lean-formalization/checks/20261023T054730505817Z-9a834f08.json) reports exit code 0 and matching current source hashes; the [final axiom report](../../../../submissions/classicism-results-2026-10-23-v1/source/research/2026-10-22/lean-formalization/logs/runs/20261023T054730505817Z-9a834f08/Classicism_Results_Research_MaxAtomicityInconsistency.log) lists only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom mathematical axiom. See the [certificate index](../../../../submissions/classicism-results-2026-10-23-v1/source/research/2026-10-22/lean-formalization/max-background-certificates.md) and complete package. No mathematical database verdict or registry verification flag is changed by this note.

This proof is separate from the earlier [constructible-universe proof](../../../../submissions/classicism-results-2026-10-23-v1/source/research/2026-10-22/lean-formalization/max-atomicity-inconsistency-proof.md). It uses a particular countably generated rigid complete Boolean algebra and its canonical natural-number-indexed generating sequence. It does not use a constructible well-order, an assumption that the ambient universe is L, or an L-restricted function domain.

The exact target is

\[
\neg\operatorname{Consistent}\bigl(\operatorname{Max}(C)
       +\operatorname{Atomicity}_t\bigr),
\tag{T}
\]

where Max is the original **pure**, finitary Distinctness schema, its reference theory is **bare C**, and Atomicity is **unboxed** and only at type t. The final source statement is

```lean
¬ AxiomSet.Consistent (AxiomSet.maximalist ∪ P.AtomicityT.schema)
```

in [MaxAtomicityInconsistency.lean][final], theorem `maximalism_atomicity_inconsistent`. Its proof expression supplies actual constructions for the semantic and syntactic obligations; it has no rigidity, definability, selector, non-theoremhood, or inconsistency assumption as a theorem parameter. That expression has now elaborated successfully; the exact theorem type and transitive axiom report are linked above.

## 1. Framework and the reduction to one pure sentence

The fixed language has base types e and t and function types σ→τ only when τ is relational, so every non-base type ends in t. The standing logic is C, including Logical Equivalence with its original theoremhood restriction. See [the framework](../../../topics/classicism/background.md), [pure Maximalism](../../../topics/classicism/principles/distinctness-schema-r.yaml), and [Atomicity at t](../../../topics/classicism/principles/atomicity-t.yaml). Those records cite Bacon and Dorr, *Classicism*, draft of 16 May 2023, respectively §1.3, §2.4 pp. 35–36, and §2.2 p. 24. These are the map's formulation locators, not a claim that the present new proof occurs there.

Write 0 and 1 for bottom and top, and use the algebraic order on propositions. For a closed pure term F:t→t define the literal finite sentence

\[
S_F:=\forall p^t\bigl[p\ne0\ \to\
 ((p\wedge Fp)\ne0\ \wedge\ (p\wedge\neg Fp)\ne0)\bigr].
\tag{1}
\]

The two obligations are:

1. Construct a closed pure F, using only closed admitted types, and a sound interpretation of **bare C** in which S_F has value 1. This proves C ⊬ S_F=0.
2. Derive C+Atomicity_t ⊢ S_F=0 for every such F, without necessitating Atomicity or applying Logical Equivalence under that extra hypothesis.

Max then supplies S_F≠0, contradicting the second obligation. Notice that constructing an arbitrary external splitting operation would not discharge the first obligation: F must be a particular term in the empty nonlogical signature. Sections 2–9 construct that term and compute its value. Section 10 gives the object-language derivation.

All set theory and cardinal arithmetic below are external classical metatheory. They are used to construct a model and prove a syntactic non-theorem. They are not added as object-language axioms. In particular, no Choice schema, GCH, C5, boxed Atomicity, infinitary connective, or named algebra is added to C.

## 2. The actual Boolean algebra and its canonical generators

### 2.1 Source and concrete construction

The external construction is Thomas Jech and Saharon Shelah, [*A Complete Boolean Algebra That Has No Proper Atomless Complete Subalgebra*](https://shelah.logic.at/files/95558/566.pdf), *Journal of Algebra* **182** (1996), pp. **748–755**. The theorem and countable-generation corollary are on p. 749; the growth/tree definitions are on pp. 749–750; amalgamation and fusion are on pp. 750–751; rigidity is proved on pp. 752–754. The minimality argument on pp. 751–752 is not needed here. The finite coding, full-domain interpretation, pure selector, and Max/Atomicity deduction below are original work, `misc`, 22–23 October 2026, unpaginated; they are not attributed to that paper.

Here is the actual construction used by the source modules. Define natural-number sequences

\[
P_0=N_0=1,\qquad P_{k+1}=P_kN_k,\qquad
N_{k+1}=2^{P_{k+1}},\qquad
o_k=1+\sum_{j<k}N_j.
\tag{2}
\]

Thus P_k=∏_{j<k}N_j. Define the master tree and node index recursively:

\[
\operatorname{ind}(\varnothing)=0,\qquad
\operatorname{ind}(s^\frown i)=o_{\operatorname{ind}(s)}+i,
\quad i<N_{\operatorname{ind}(s)}.
\tag{3}
\]

The child blocks [o_k,o_k+N_k) partition the positive integers. Each parent index is smaller than its child indices. Induction on indices gives a bijection from master nodes to ℕ. Its inverse is `indexedNode`; no choice of an encoding of finite lists is used in the final generator graph.

A condition is a nonempty prefix-closed subtree T of the master tree satisfying

\[
\forall s\in T\ \forall m\in\mathbb N\ \exists t\in T\,
 [s\text{ is a strict prefix of }t\ \wedge\
   |\operatorname{Succ}_T(t)|\ge P_{\operatorname{ind}(t)}^m].
\tag{4}
\]

The order is inclusion, with smaller trees stronger. For s∈T, restriction T↾s retains the nodes comparable with s and is again a condition. To see separativity, if Q⊈T choose s∈Q\T. The condition Q↾s is incompatible with T: a common condition would have arbitrarily long nodes comparable with s, hence a node extending s, which would force s∈T by prefix closure. Incompatible restrictions at a sufficiently splitting node give two incompatible strengthenings of every condition.

The implementation is [Trees][trees], with the bijection proved in [Enumeration][enumeration].

### 2.2 Regular lower sets and density

Let \(\mathbb P\) be this actual set of conditions. For a lower subset X⊆\(\mathbb P\), put

\[
X^*:=\{p\in\mathbb P: \forall q\le p,\ q\notin X\}.
\]

Take

\[
B:=\{X\subseteq\mathbb P:X\text{ is lower and }X=X^{**}\}.
\tag{5}
\]

These are the regular elements of the complete Heyting algebra of lower sets. Their order is inclusion, complement is *, and arbitrary joins are the double pseudocomplement of unions. Write ι(T) for the regularization of ↓T. Separativity makes ι an order embedding; ι(T) is nonzero; and the image of ι is dense in B. Indeed, for nonzero regular X choose T∈X; then ι(T)⊆X. Incompatible strengthenings show B is atomless. It is therefore nontrivial and infinite. Set κ=|B|.

These facts are supplied by [RegularCompletion][completion], including `condition_ne_bot`, `condition_dense`, `condition_le_iff`, and `completion_atomless`, instantiated by `forcing_separative` and `forcing_completion_atomless` in [Trees][trees]. They concern the actual regular-lower-set algebra, not an unspecified completion.

For a master node s define its cylinder by

\[
c_s:=\iota(\mathbb T\mathbin{\upharpoonright}s),\qquad
g_n:=c_{\operatorname{indexedNode}(n)}.
\tag{6}
\]

Cylinders at distinct nodes on the same level are disjoint. For every condition T,

\[
\iota(T)=\bigwedge_{\ell<\omega}
           \bigvee_{s\in T,\ |s|=\ell}c_s.
\tag{7}
\]

The forward inequality follows by restricting densely below T to a node on level ℓ. For the reverse, a condition Q outside T has a node s∈Q\T. Restricting Q to s gives a nonzero element below c_s and disjoint from the level-|s| join for T. Density excludes any nonzero part of the proposed right side outside ι(T). Finally,

\[
b=\bigvee\{\iota(T):\iota(T)\le b\}
\tag{8}
\]

by density. Consequently the sequence (g_n) completely generates B. These are `condition_eq_iInf_levelJoin` and `eq_iSup_conditions` in [Cylinders][cylinders], followed by `indexedGenerator_completely_generates` in [IndexedGenerators][indexed-generators].

### 2.3 A least splitting index exists

For p≠0, let

\[
\mathcal N_p:=\{a\in B:p\le a\text{ or }p\le\neg a\}.
\]

This set contains 0 and is closed under complement and arbitrary joins. For a join of its members, if some member contains p, the join contains p; otherwise p lies below every member's complement and hence below the complement of the join. Thus \(\mathcal N_p\) is a complete Boolean subalgebra. If no g_n split p, every g_n would belong to \(\mathcal N_p\), so complete generation would give \(\mathcal N_p=B\). An element strictly between 0 and p, supplied by atomlessness, contradicts this. Therefore there is a least natural number n(p) such that

\[
p\wedge g_{n(p)}\ne0,\qquad p\wedge\neg g_{n(p)}\ne0.
\tag{9}
\]

The source proof is [CountableGenerator][countable-generator], `nonSplit_completeClosed`, `exists_generator_splits`, and the least-index specification. This is still an external algebraic construction; pure definability will follow only after coding and rigidity.

## 3. Rigidity, including the local fusion obligation

The implementation uses actual Boolean values, so the quantifiers needed for the rigidity argument can be inspected directly.

A bounded name is a family x=(x_{k,i}) with i<N_k such that each row is a pairwise disjoint partition of 1. A slalom u assigns a finite subset u(k)⊆N_k with |u(k)|≤P_k. For A⊆ℕ define

\[
\begin{aligned}
\operatorname{cap}_A(x,u)&=\bigwedge_{k\in A}\bigvee_{i\in u(k)}x_{k,i},\\
\operatorname{cover}_A(x)&=\bigvee_u\operatorname{cap}_A(x,u),\\
v_A&=\bigvee_x\neg\operatorname{cover}_A(x).
\end{aligned}
\tag{10}
\]

Every actual order automorphism of B preserves arbitrary joins, meets, and complements. Applying it to every row is a bijection of bounded names, and it does not change the external index set of slaloms. Hence it fixes v_A. This reindexing proof is `automorphism_fixes_invariant` in [SlalomInvariance][slalom]. It does not assume that an automorphism already preserves a named generating sequence.

For T∈\(\mathbb P\), put A_T={ind(s):s∈T}. The two substantive estimates are

\[
\iota(T)\le v_{A_T},
\tag{11}
\]

and

\[
Q\nleq T\ \Longrightarrow\
\exists R\le Q\quad \iota(R)\le\neg v_{A_T}.
\tag{12}
\]

For (11), the branch name has, on a parent cylinder, the child cylinders as its row entries; the complement of the parent cylinder is assigned to digit 0, so every row really sums to 1. Given a slalom, densely below T choose a sufficiently large split with at least P_k² children, where k∈A_T and P_k>1. A child digit outside the at most P_k slalom digits yields a restriction disjoint from that capture value. Thus ι(T) is disjoint from every capture value of the branch name, proving (11). See [Branch][branch], `escape_slalom`, `branch_inf_capture`, and `condition_le_marker`.

For (12), choose a forbidden node b∈Q\T of length at least 2 and set R=Q↾b. Fix an arbitrary bounded name x. The local fusion construction proves:

\[
\forall S\le R\ \exists S'\le S\ \exists u\quad
\iota(S')\le\operatorname{cap}_{A_T}(x,u).
\tag{13}
\]

Its invariants are a finite front, an increasing coordinate cutoff, decisions of every coordinate below that cutoff by the front restrictions, and two cardinal bounds. Coordinates in A_T already passed have at most P_k retained values. For future coordinates in A_T, the current front size is strictly below P_k. All nodes above the chosen front extend b; their indices are outside A_T, since a node of T extending b would put b in T.

At stage n, choose K∈A_T above the current cutoff and a chosen front restriction, then extend its stem to a splitting node with index m>K and m≥n+2. This index is outside A_T. Choose P_m^{n+1} children and refine below each to decide all coordinates k<m. There are exactly

\[
\prod_{k<m}N_k=P_m
\]

possible full decision vectors. Finite pigeonhole therefore retains P_m^n children with the same vector. The other old front restrictions each contribute one retained piece. Amalgamation preserves the old front and the scheduled split. New coordinates from A_T below m have at most the old-front size many values; earlier value bounds persist because two decisions of one partition row below a common nonzero condition must agree.

For the future bound, if the old-front size is L<P_K≤P_m, the chosen growth bounds imply

\[
L+P_m^n<P_m+N_m\le P_mN_m=P_{m+1}\le P_k
\quad(k>m).
\tag{14}
\]

The hypotheses ensure P_m,N_m≥2 and P_m^n≤N_m. Since m∉A_T, the relevant later coordinates satisfy k>m. The recursion schedules the node of index n at stage n and retains its required P^n split below the next protected front. Thus the intersection satisfies the scheduled version of (4) and is a condition. The eventual finite decision sets constitute a genuine slalom, giving (13).

The finite counting lemma is `thin_power`/`thin_growth` in [SlalomThinning][thinning]; finite decisions are in [FiniteRefinement][finite-refinement]; the actual step is `advance` in [LocalStage][local-stage]. [Amalgamation][amalgamation], [Fusion][fusion], and [SlalomLimit][slalom-limit] verify the preservation and limit claims. [LocalFusion][local-fusion] constructs the initial stage, the entire tower, and its readout, rather than assuming the stage or fusion step.

For this fixed x, (13) and density imply ι(R)≤cover_{A_T}(x). The same fixed R works for every x, with a different dense refinement construction for each x. Consequently

\[
\iota(R)\le\bigwedge_x\operatorname{cover}_{A_T}(x)
            =\neg v_{A_T}.
\]

This order of quantifiers matters: no one condition is claimed to decide or capture all names simultaneously. It is exactly `local_separation` in [LocalFusion][local-fusion].

Equations (11) and (12), with density and separativity, imply v_{A_T}=ι(T). Every automorphism fixes every ι(T), hence every element of B by (8). This is `actual_rigid`, using [RigidityCriterion][rigidity-criterion]. Here rigidity means every actual `B ≃o B` is the identity. It is a theorem about the Boolean algebra without a chosen truth ultrafilter.

## 4. A genuine hereditary-size universe on the exact type U=t→t

### 4.1 Full Boolean-valued interpretation

Use the actual algebra B above and the full interpretation

\[
D_e=\{*\},\quad D_t=B,\quad
D_{\sigma\to\tau}=D_\tau^{D_\sigma}
\]

at every admitted function type. Equality is the crisp value 1 for actual equality and 0 otherwise; connectives are Boolean operations; universal and existential quantification are respectively meets and joins over the full domains. Lambda abstraction and application are ordinary functions. The soundness theorem is `C_sound` in [BooleanValuedSoundness][soundness], instantiated in [ConcreteModel][concrete]. No L-full versus ambient-full domain change is involved.

Let U=t→t, so D_U=B→B. The auxiliary types U→t, U→U→t, and t→U are all admitted closed relational types. They are respectively used for subset predicates, membership relations, and maps from B to coded algebra elements.

### 4.2 The universe is constructed as a set

A set x is **hereditarily B-small** when its member set embeds into B and the same is true recursively of every member. Denote the class by H_B. The implementation uses this precise hereditary predicate, not an assumed package of axioms for an unspecified H_κ.

Construct the W-type

\[
W_B=W\bigl(s\mapsto s\ :\ s\subseteq B\bigr).
\]

Decode a node with children (w_i)_{i∈s} to the set {decode(w_i):i∈s}. Induction on trees shows every decoded set is hereditarily B-small. Conversely, membership induction on x∈H_B, using an actual embedding of its member set into B, produces such a tree. Therefore

\[
H_B=\operatorname{range}(\operatorname{decode})
\tag{15}
\]

is an actual set, and it is transitive. These are `hereditary_range`, `decode_hereditary`, `hereditary_has_tree`, `mem_universeSet`, and `universeSet_transitive` in [HereditaryUniverse][universe]. Repetition in an indexed family causes no problem: a right inverse to its surjection onto the range supplies the member-set embedding.

The W-type cardinal bound is proved using the bound at μ=2^κ:

\[
\sum_{s\subseteq B}\mu^{|s|}
 \le 2^\kappa\,(2^\kappa)^\kappa=2^\kappa.
\]

This yields |H_B|≤2^κ. For the converse, well-order B externally and collapse the order to distinct hereditary-small element codes; coding subsets of these elements injects P(B) into H_B. Hence

\[
|H_B|=2^\kappa=\kappa^\kappa=|B\to B|.
\tag{16}
\]

`presentationEquiv` in [HereditaryUniverse][universe] therefore supplies an actual bijection π:D_U≃H_B. Its chosen value is only external machinery for showing a code exists. The final pure term quantifies over every eligible code, so π is not a nonlogical constant. In ordinary ZFC this hereditary-size universe has the familiar H_{κ⁺} description; neither the construction nor the proof below requires that additional identification to have been formalized.

### 4.3 The finite HCode formula has exactly the needed meaning

For X:U→t put

\[
\begin{aligned}
\operatorname{Crisp}(X)&:=\forall x\,(Xx=0\vee Xx=1),\\
\operatorname{Small}(X)&:=\exists f^{U\to t}\ \forall x,y\,
 [(Xx\wedge Xy\wedge fx=fy)\to x=y].
\end{aligned}
\tag{17}
\]

The witness f is **not** required to be crisp: its range is all of B. For crisp X, Small(X) has value 1 exactly when its extension embeds into B. An embedding extends to a total B-valued function by assigning 0 off that extension. This is `small_iff_embedding` and `eval_small` in [HCodeSemantics][hcode-semantics].

HCode(E), for E:U→U→t, is the finite conjunction of:

- E is crisp;
- E is extensional in its predecessor rows;
- every nonempty crisp subset predicate has an E-minimal member;
- every crisp small subset predicate is exactly one predecessor row;
- every predecessor row is small.

The literal formulas occur in [Syntax][hcode-base] and [HCodeSyntax][hcode-syntax]. In the full interpretation, every external subset has a characteristic predicate. Hence these clauses say precisely that R(x,y) iff E(x,y)=1 is well-founded, extensional, fills all subsets of size at most κ, and has all rows of size at most κ.

The guards are essential. Noncrisp predicates X are quantified over too, but their Crisp antecedents are 0 in the well-foundedness and filling clauses. Noncrisp E makes the first conjunct, and hence the whole HCode, 0. No argument treats all predicates in a full function domain as automatically crisp. The exact evaluation is proved in `eval_hCode_exact` in [HCodeSemantics][hcode-semantics].

Given a successful E, Mostowski collapse is an injection preserving membership and identifying each predecessor row with the members of its collapsed image. Row smallness and well-founded induction put its range inside H_B. Conversely, for x∈H_B, inductively take preimages of its members. They form a small subset of D_U; the filling clause supplies a row consisting exactly of these preimages, whose collapse is x. Thus the range is **all** of H_B. See [Mostowski][mostowski], [HereditaryCover][hereditary-cover], and `good_collapseRange`/`collapseEquiv` in [HCodeCharacterization][hcode-characterization].

Pulling actual membership back along π gives one successful E. Consequently every successful code is isomorphic, by an actual bijection, to this canonical membership structure. [HCodeExistence][hcode-existence] proves existence; `canonicalChange_membership` in [HCodeCharacterization][hcode-characterization] gives the change of presentation. Satisfaction of finite membership formulas is invariant under it by structural induction, including the quantified cases using surjectivity.

## 5. Closure witnesses and their genuine sizes

The construction needs actual members of H_B for its coded objects. It does not infer arbitrary powerset closure from transitivity. The central lemma is `hereditary_range`: a family of hereditary-small sets indexed by a type embedding into B has hereditary-small range. Pair and graph closure are built from this lemma in [HereditaryGraphs][graphs].

| Required object | Actual index bound and justification |
| --- | --- |
| A natural numeral; an ordered pair | Finite hereditary sets; finite indices embed into infinite B. |
| ω; a real I⊆ℕ; a tree's node-index set | At most countable; ℕ embeds into B. |
| Unary arithmetic graphs and graphs on ℕ² | At most countable; pair entries are hereditary-small. |
| The set of all condition codes | Conditions embed into B by the separative map ι. Conditions are **not** asserted countable. |
| Any one subset of the condition poset | Its members are indexed by a subset of Conditions, hence by at most κ elements. |
| The condition-order graph | At most |Conditions|²≤κ²=κ ordered pairs. |
| A coded regular open b | One subset of the poset, therefore at most κ members. |
| The algebra carrier, containing all coded b∈B | Indexed by B itself, hence κ members, each already hereditary-small. |
| The graph n↦code(g_n) | Countably many ordered pairs with hereditary-small entries. |
| A finite injection witnessing a successor count | A finite graph between finite natural ordinals and natural node indices. |

In particular, **every subset** of the poset is separately represented, as required by the double-pseudocomplement definition. The set of all subsets of the poset is never required to be a member of H_B. The algebra carrier is smaller than an arbitrary such powerset for the relevant reason: it is indexed by the already constructed set B.

The explicit codes are in [SetCodes][set-codes]. Natural numerals are the collapse of the ordinary well-order on ℕ; `realCode I` is the range of those numerals for i∈I; `treeCode T` uses the indices of nodes of T. Master-index injectivity gives injectivity and order reflection of tree coding. `codeOpen b` is the set of tree codes belonging to the underlying lower set of b, and `algebraCode` is its range over b∈B. [HereditaryGraphs][graphs] supplies the order graph, generator graph, and arithmetic graphs with their membership and hereditary-size proofs.

## 6. The literal finite membership formula JSCode(c,w,G)

The code is an actual value of the finite datatype `SetFormula 3`, defined in [JechShelahSyntax][js-syntax]. Its three free variables, in order, are the algebra carrier c, the natural-number set w, and the generator graph G. There is no infinitary scheme hidden in this assertion of definability.

For clarity, the following displays use finite first-order abbreviations. They expand using [SetFormulaTools][set-tools]:

\[
\begin{aligned}
\operatorname{Empty}(a)&\equiv\forall x\,x\notin a,\\
a\subseteq b&\equiv\forall x(x\in a\to x\in b),\\
\operatorname{Pair}(x,y,z)&\equiv z=\{\{x\},\{x,y\}\},\\
\operatorname{App}(f,x,y)&\equiv\exists z(\operatorname{Pair}(x,y,z)\wedge z\in f),\\
\operatorname{Succ}(a,b)&\equiv\forall x[x\in b\leftrightarrow(x\in a\vee x=a)].
\end{aligned}
\tag{18}
\]

The pair display expands by quantifying the singleton and unordered pair and giving their exact membership biconditionals. FunctionGraph says every member is an ordered pair and outputs are unique. GraphDomain(f,r) says its inputs are exactly the members of r. App₂(f,x,y,z) uses an ordered pair (x,y) as the input. UnaryOn and BinaryOn give exact domains, totality, and natural-valued outputs; RelationOn says all graph members are pairs of naturals. Thus a graph cannot satisfy the intended clauses while carrying unrelated extra elements.

### 6.1 Arithmetic and ancestry

Inductive(w) says w contains an empty set and is closed under successor. Define

\[
\operatorname{Omega}(w):=\operatorname{Inductive}(w)\wedge
 \forall I(\operatorname{Inductive}(I)\to w\subseteq I).
\tag{19}
\]

JSCode existentially quantifies twelve witnesses

\[
z,\ 1_c,\ 2_c,\ A,\ M,\ E,\ p,\ n,\ o,\ a,\ P,\ O.
\]

Here E in this list is the exponentiation **graph**, distinct from the higher-order membership relation used elsewhere. The subformula Arithmetic says z is empty, 1_c is its successor, 2_c is the successor of 1_c, all belong to w, Omega(w) holds, and the arithmetic graphs satisfy their finite recursion laws. Written on their decoded inputs these laws are

\[
\begin{array}{lll}
A(x,0)=x,&A(x,y+1)=A(x,y)+1,\\
M(x,0)=0,&M(x,y+1)=A(M(x,y),x),\\
E(x,0)=1,&E(x,y+1)=M(E(x,y),x).
\end{array}
\tag{20}
\]

Each second equation is an App₂ biconditional with an existential previous value and a successor or graph clause, exactly as in `addRecursion`, `mulRecursion`, and `powRecursion`. No arithmetic function symbol is added. The unary graphs p,n,o start at 1 and satisfy

\[
p(k+1)=p(k)n(k),\quad n(k+1)=2^{p(k+1)},\quad o(k+1)=o(k)+n(k).
\tag{21}
\]

Using equality-or-membership for ≤ on finite ordinals, define Child(k,j) by o(k)≤j<o(k)+n(k). The ancestry graph has only pairs from w and satisfies the one finite clause

\[
a(i,j)\ \leftrightarrow\ i=j\ \vee\
   \exists k\in w\,[\operatorname{Child}(k,j)\wedge a(i,k)].
\tag{22}
\]

### 6.2 Conditions, order, completion, and generators

ManyChildren(T,u,r) says there exists an injective function graph with **exact domain r**, every output of which is a child of u lying in T. Its witnesses are sets, not external cardinal comparisons. ConditionCode(T) says:

1. T⊆w and z∈T;
2. T is closed downward under a;
3. for i∈T and m∈w, some u∈T has i≠u, a(i,u), and ManyChildren(T,u,r), where p(u) and exponentiation give r=p(u)^m.

PosetCarrier(P) is ∀T[T∈P↔ConditionCode(T)]. InclusionGraph(P,O) says the members of O are exactly pairs (X,Y) with X,Y∈P and X⊆Y.

The finite regular-lower-set formulas from [RegularOpenCode][regular-code] are

\[
\begin{aligned}
\operatorname{Lower}(P,O,X)&\equiv X\subseteq P\ \wedge\
 \forall p\in X\ \forall q\in P\,[O(q,p)\to q\in X],\\
\operatorname{PC}(P,O,X,Y)&\equiv
 \forall p[p\in Y\leftrightarrow
 (p\in P\wedge\forall q\in P(O(q,p)\to q\notin X))],\\
\operatorname{Regular}(P,O,X)&\equiv\operatorname{Lower}(P,O,X)\wedge
 \exists Y[\operatorname{PC}(P,O,X,Y)\wedge\operatorname{PC}(P,O,Y,X)],\\
\operatorname{AlgebraCarrier}(P,O,c)&\equiv
 \forall X[X\in c\leftrightarrow\operatorname{Regular}(P,O,X)].
\end{aligned}
\tag{23}
\]

Finally,

\[
\operatorname{GeneratorOpen}(i,X)\equiv
\forall T[T\in X\leftrightarrow
 (T\in P\wedge\forall j\in T(a(j,i)\vee a(i,j)))].
\tag{24}
\]

GeneratorGraph(G) says G is a function graph of exact domain w and
∀i∈w ∀X[App(G,i,X)↔GeneratorOpen(i,X)]. JSCode is the existential closure of Arithmetic, PosetCarrier, InclusionGraph, AlgebraCarrier, and GeneratorGraph over the twelve witnesses above. `satisfies_JSCode` in [JechShelahSyntax][js-syntax] proves the exact ordinary satisfaction equivalence for this actual syntax tree.

## 7. Standardness and exact adequacy of JSCode

### 7.1 No nonstandard omega or arithmetic is admitted

Work first in the canonical membership presentation π. The actual set of natural codes belongs to H_B by Section 5 and is inductive. If w satisfies (19), leastness gives w⊆ω. Conversely external induction on ordinary n proves every inductive set contains the code of n, so ω⊆w. Thus w is exactly the canonical natural set. This is `omega_iff` in [ArithmeticSemantics][arithmetic-semantics]. It uses the actual available ω witness; it does not infer external standardness from an internal induction axiom alone.

Having identified w, totality and functionality let the arithmetic graphs be decoded into actual functions on ℕ or ℕ². External induction in the second argument proves (20) has precisely the usual addition, multiplication, and exponentiation values. Ordinary induction proves (21) has exactly the sequences (2). For ancestry, every immediate parent index is smaller than its child; strong induction on the second index makes (22) unique and identifies it with prefix of indexed master nodes. [IndexCoding][index-coding] proves these recursion uniqueness statements; `arithmetic_decoded` in [ArithmeticSemantics][arithmetic-semantics] assembles them.

Existence is separate from uniqueness. Actual unary, binary, and relational natural graphs are hereditary-small by Section 5. They therefore supply all Arithmetic witnesses, including the entire ancestry graph, in the membership universe. This is the unconditional `canonical_arithmetic_exists` in [ArithmeticExistence][arithmetic-existence].

### 7.2 The condition formula has both directions

For X⊆ω put I_X={n:the code of n belongs to X}. Decoded ManyChildren is exactly an injection from Fin(P_u^m) to the retained child indices of u. The forward conversion evaluates the coded finite graph; the reverse constructs that finite graph and uses its hereditary-size witness.

An actual condition T yields I_T={ind(s):s∈T}, and satisfies all these clauses. Conversely, from a set I satisfying the indexed clauses reconstruct

\[
T_I:=\{s\text{ a master node}:\operatorname{ind}(s)\in I\}.
\]

It is nonempty because 0∈I. Ancestry closure gives prefix closure. For a required split, the formula supplies a strict ancestor pair i,u and distinct retained child indices. Prefix plus unequal indices gives a **strict** extension of nodes; every index in the block of u uniquely equals o_u+j for j<N_u, so the finite injection gives distinct actual immediate successors. This proves (4), not merely an informal resemblance to it. The inverse node-index equations then identify X with the actual tree code. See `indexCondition_iff` in [IndexCoding][index-coding] and `manyChildren_iff`, `conditionCode_iff_indices`, and `conditionCode_iff_tree` in [ConditionSemantics][condition-semantics].

Extensionality now makes P the actual set of all condition codes. Pair absoluteness and inclusion make O the actual order graph. The exact-domain and no-junk clauses matter here.

### 7.3 The completion and generator graph are canonical

Every subset of the actual condition poset is represented in H_B. Thus the coded lower-set and pseudocomplement clauses (23) range over exactly the subsets needed to compute the actual regular-lower-set completion. `posetCoding_full` and `regular_iff_carrier` in [CanonicalCompletion][canonical-completion] identify the regular codes with the images of actual b∈B. `algebraCarrier_unique` gives c=canonicalCarrier.

For i∈ℕ, all nodes of a condition T are comparable with indexedNode(i) exactly when T≤\(\mathbb T\)↾indexedNode(i). Separativity gives

\[
\iota(T)\le g_i\ \leftrightarrow\
T\le\mathbb T\mathbin{\upharpoonright}\operatorname{indexedNode}(i).
\]

Membership of T in the regular lower set g_i has the same meaning. Therefore (24) picks out precisely codeOpen(g_i). FunctionGraph, exact domain, and output uniqueness make G exactly the actual natural-indexed generator graph, with no extra pairs. These are `canonical_generatorOpen`, `generatorOpen_iff`, and `generatorGraph_unique` in [ConditionSemantics][condition-semantics].

Consequently `canonical_sound` proves that every canonical-membership triple satisfying JSCode is exactly (canonicalCarrier, canonicalNaturals, canonicalGraph). Conversely, the actual codes and the arithmetic witnesses satisfy every clause; `canonical_exists_of_arithmetic` applies to the unconditional arithmetic existence theorem.

### 7.4 Transport to arbitrary successful membership codes

The collapse bijection from Section 4 transports finite membership satisfaction, subset, and graph application. [SetCodeAbsoluteness][absoluteness] proves the primitive absolute meanings in the canonical code and constructs its actual presentation. [SelectorTransport][selector-transport], `adequate_of_canonical`, transports that presentation to any successful E.

Concretely, every successful JSCode supplies:

- an embedding j:B↪D_U with image exactly the members of c;
- j(b)⊆_E j(d) iff b≤d;
- an embedding ν:ℕ↪D_U with image exactly the members of w;
- a∈_Eν(k) iff a=ν(i) for some i<k;
- App_E(G,ν(k),a) iff a=j(g_k).

One such successful code exists. These are the exact fields of `Presentation` and `Adequate` in [PureSelector][pure-selector]. The theorem `canonical_adequacy` in [the final assembly][final] discharges this interface for the particular literal JSCode and actual indexedGenerator. It does not leave formula correctness as an assumption.

## 8. The closed pure selector and its crucial guard

Use only the following closed relational types:

\[
U=t\to t,\quad ER=U\to U\to t,\quad HU=t\to U.
\]

For propositions p,q, let Splits(p,q) be the conjunction of the two nonzero identities in (1). Let Iso(E,c,h), for h:HU, assert that h has image in c, is onto c, and reflects and preserves the order:

\[
p\le q\ \leftrightarrow\ h(p)\subseteq_E h(q).
\]

All three conditions are literal quantified formulas. Order reflection gives injectivity when c has the identified subset order.

For six witnesses E,c,w,G,h,n define Raw to be the finite conjunction

\[
\begin{aligned}
&\operatorname{HCode}(E),\quad\operatorname{JSCode}^{E}(c,w,G),\quad
 \operatorname{Iso}(E,c,h),\quad n\in_Ew,\\
&\operatorname{App}_E(G,n,h(q)),\quad\operatorname{Splits}(p,q),\\
&\forall m\in_En\ \forall r^t\,
 [\operatorname{App}_E(G,m,h(r))\to\neg\operatorname{Splits}(p,r)].
\end{aligned}
\tag{25}
\]

Here JSCode^E is the actual inductive translation of finite membership syntax to pure higher-order syntax. `eval_translate` in [SetSemantics][set-semantics] is proved by induction, including its environments, variable lifting, and binders.

Now put

\[
\begin{aligned}
\operatorname{Guard}(E,c,w,G,h,n;p,q)&:=(\operatorname{Raw}=1),\\
\operatorname{Sel}(p,q)&:=\exists E,c,w,G,h,n\ \operatorname{Guard},\\
F&:=\lambda p^t.\ \exists q^t\,[\operatorname{Sel}(p,q)\wedge q].
\end{aligned}
\tag{26}
\]

The equality-to-top test is applied **to each witness's Raw formula before the six existential quantifiers**. This is not an exchangeable placement. In a general complete Boolean algebra a join can equal 1 without one summand equalling 1. In (26), each guard is already 0 or 1. Its join is therefore 1 exactly when an actual successful witness exists, and otherwise 0. A noncrisp or otherwise invalid E gives guard 0; no spurious partly true presentation contributes a Boolean fragment to F.

The syntax, purity, and closed-type proofs are `selector`, `selector_pure`, and `selector_closedTypes` in [PureSelector][pure-selector]. This term is finite. Every code, map, and index in (25) is bound; the only supplied datum is the finite syntax tree JSCode, which itself contains no nonlogical symbols.

For p≠0 and a successful witness, adequacy gives j and ν as in Section 7. The quantified h is an order isomorphism from B onto the same coded carrier as j. Consequently j⁻¹∘h is an order automorphism of B. Rigidity forces h=j. This is a consequence of actual rigidity, not an assumption that presentations are already uniquely labelled; see [RigidTransport][rigid-transport] and `Presentation.iso_eq_carrier` in [PureSelector][pure-selector].

The graph clause then says q=g_k where n=ν(k). The last clause of (25), using the exact predecessor description of ν(k), says no earlier generator splits p. Thus k=n(p) and q=g_{n(p)}. Conversely, choose a successful presentation, h=j, and n=ν(n(p)); all clauses hold. Hence

\[
\llbracket\operatorname{Sel}(p,q)\rrbracket=
\begin{cases}1,&q=g_{n(p)},\\0,&\text{otherwise},\end{cases}
\quad(p\ne0).
\]

Finally the outer existential in F is genuinely Boolean-valued:

\[
\llbracket F\rrbracket(p)
 =\bigvee_{q\in B}\bigl(\llbracket\operatorname{Sel}(p,q)\rrbracket\wedge q\bigr)
 =g_{n(p)}.
\tag{27}
\]

All eligible presentations yield the same element, so taking their existential join does not change the selected value. The value at p=0 is immaterial. The source theorems are `eval_witnessGuard`, `eval_selects`, `selected_least`, `least_selected`, `eval_selector_eq_least`, and `eval_selector_splits` in [PureSelector][pure-selector].

## 9. The exact non-theorem of bare C

Take F=`selector JSCode`. Equations (9) and (27) say that it splits every nonzero p in the actual B interpretation. All identities and nonidentities in (1) have crisp values, so every instance of its universal implication is 1. Therefore

\[
\llbracket S_F\rrbracket=1,
\qquad\llbracket S_F=0\rrbracket=0
\tag{28}
\]

because B is nontrivial. C soundness implies

\[
C\nvdash S_F=0.
\tag{29}
\]

This conclusion uses the exact original language and the exact C side condition. The fact that this full model validates additional principles is harmless: only its soundness for C is needed to refute C-theoremhood. No satisfiability-to-consistency converse or completeness theorem is invoked.

[SplitSemantics][split-semantics] proves `eval_split` and the resulting `split_identity_not_C_theorem`. [The final assembly][final] supplies the actual F, `F_closedTypes`, `F_pure`, and `F_splits`, then obtains (29). The pure term is what closes the definability gap left by a merely external rigid-algebra argument.

## 10. Why unboxed Atomicity proves the stronger zero identity

It is not enough to show Atomicity implies ¬S_F: Max supplies S_F≠0, which is a different assertion in C. The required conclusion is the actual entity identity S_F=0. The bounded argument establishes it without boxing Atomicity.

Define

\[
\operatorname{Split}(b,F):=\forall p[(p\ne0\wedge p\le b)\to
 ((p\wedge Fp)\ne0\wedge(p\wedge\neg Fp)\ne0)].
\]

Bare C proves

\[
\operatorname{Split}(b\wedge\operatorname{Split}(b,F),F).
\tag{30}
\]

For the proof take nonzero p≤b∧Split(b,F). It follows that p≤b and p≤Split(b,F). The C order/modal laws and the closed logical implication expressing universal instantiation give

\[
\Box\bigl(p\to[(p\wedge Fp)\ne0\wedge
                         (p\wedge\neg Fp)\ne0]\bigr).
\]

Since p≠0, the displayed conjunction is possible. Each nonidentity is therefore possible, and C's necessity of identity yields the corresponding actual nonidentity by contraposition: ◇(a≠b) implies a≠b. This proves (30). Only bare-C theorems are necessitated in this reasoning. This is `split_guard` in [BoundedSplitter][bounded-splitter].

If a current atom w lies below a split bound b, then w≠0, so Split(b,F) says both parts w∧Fw and w∧¬Fw are nonzero. But the atom law gives w≤Fw or w≤¬Fw; the corresponding other part is 0. Thus no atom lies below a split bound. Unboxed Atomicity applied to that bound says it is 0. Applying this to (30) proves

\[
C+\operatorname{Atomicity}_t\vdash
 b\wedge\operatorname{Split}(b,F)=0.
\tag{31}
\]

These are `split_excludes_atom`, `atomicity_split_bound_zero`, and `atomicity_guard_zero` in [BoundedSplitter][bounded-splitter]. The original Atomicity formula allows the bound itself to be bottom or supplies an atom below it; no boxed form is substituted.

At b=1, bare C identifies the left term in (31) with S_F. The bridge is a closed Logical Equivalence instance with F as its term parameter; no Atomicity hypothesis occurs in the equivalence proof. [SplitCertificate][split-certificate] instantiates the generated object-language certificate `atomicity_guard_zero.derivable` at 1 and the actual closed term F, uses the Atomicity schema axiom, and composes with `guard_eq_split.derivable`. Its theorem is exactly

\[
\operatorname{Theorem}(C.\mathrm{axioms}\cup\operatorname{Atomicity}_t.\mathrm{schema},
                       S_F=0).
\tag{32}
\]

This is an object-language derivation, not a semantic obstruction inserted as a premise. Finally F and S_F have no free object variables, type variables, or nonlogical constants. By (29), the Max(C) instance for S_F=0 is S_F≠0. Combining it with (32) yields (T). [MaxAtomicityReduction][reduction] handles this last schema membership and contradiction; [the final module][final] supplies both required certificates.

## 11. Verification boundaries and direct dependency map

The proof above separates the substantive mathematical obligations from compiler status. The implemented final composition has discharged, in source, the previously explicit premises of formula adequacy, actual rigidity, arithmetic witness existence, and pure splitting. Its validity as a Lean certificate still requires the serial checker to compile the full dependency chain and inspect the final theorem's transitive axiom list, excluding `sorryAx` and any custom assumption serving as the missing result. Ordinary Lean metatheoretic axioms must be distinguished from object-language C axioms; in particular, the object-language equivalence/necessitation gate must certify the bounded-splitter derivation rather than importing a stronger untracked rule.

| Obligation | Direct source endpoint |
| --- | --- |
| Sound full interpretation of C | [BooleanValuedSoundness][soundness], `C_sound`; [ConcreteModel][concrete]. |
| Actual atomless completion | [Trees][trees], `forcing_completion_atomless`; [RegularCompletion][completion]. |
| Actual canonical countable generators | [IndexedGenerators][indexed-generators], `indexedGenerator_completely_generates`. |
| Rigidity, with both slalom estimates | [LocalFusion][local-fusion], `actual_rigid`. |
| Actual hereditary universe and its cardinality | [HereditaryUniverse][universe], `universeSet`, `presentationEquiv`. |
| Exact HCode semantics and existence | [HCodeSemantics][hcode-semantics], `eval_hCode_exact`; [HCodeExistence][hcode-existence]. |
| Collapse onto the whole hereditary universe | [HCodeCharacterization][hcode-characterization], `good_collapseRange`, `canonicalChange_membership`. |
| Literal finite membership formula | [JechShelahSyntax][js-syntax], `JSCode`, `satisfies_JSCode`. |
| Standard omega and arithmetic identification | [ArithmeticSemantics][arithmetic-semantics], `omega_iff`, `arithmetic_decoded`. |
| Actual arithmetic witness existence | [ArithmeticExistence][arithmetic-existence], `canonical_arithmetic_exists`. |
| Condition/order/completion/generator exactness | [ConditionSemantics][condition-semantics], `canonical_sound`, `canonical_exists_of_arithmetic`; [CanonicalCompletion][canonical-completion]. |
| Adequacy in every good membership presentation | [SelectorTransport][selector-transport], `adequate_of_canonical`; [final assembly][final], `canonical_adequacy`. |
| Literal pure selector and its evaluated splitting | [PureSelector][pure-selector], `selector_closedTypes`, `eval_selector_splits`; [final assembly][final], `F_splits`. |
| Exact C non-theorem | [final assembly][final], `split_identity_not_C_theorem`. |
| Actual Atomicity-to-zero derivation | [SplitCertificate][split-certificate], `split_zero_under_atomicity`. |
| Exact target, with no supplied construction premise | [final assembly][final], `maximalism_atomicity_inconsistent`. |

No result in this table is marked Lean-verified by this prose note. The older L-route proof remains a separate document. Repository validation after this note checks the map's data constraints only; it does not discharge any of the mathematical or compiler obligations described here.

[final]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityInconsistency.lean
[trees]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahTrees.lean
[enumeration]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahEnumeration.lean
[completion]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityRegularCompletion.lean
[cylinders]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahCylinders.lean
[indexed-generators]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahIndexedGenerators.lean
[countable-generator]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityCountableGenerator.lean
[slalom]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySlalomInvariance.lean
[branch]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahBranch.lean
[thinning]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySlalomThinning.lean
[finite-refinement]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahFiniteRefinement.lean
[local-stage]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahLocalStage.lean
[amalgamation]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahAmalgamation.lean
[fusion]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahFusion.lean
[slalom-limit]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySlalomLimit.lean
[local-fusion]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahLocalFusion.lean
[rigidity-criterion]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahRigidityCriterion.lean
[soundness]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Semantics/BooleanValuedSoundness.lean
[concrete]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityConcreteModel.lean
[universe]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityHereditaryUniverse.lean
[hcode-base]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySyntax.lean
[hcode-syntax]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityHCodeSyntax.lean
[hcode-semantics]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityHCodeSemantics.lean
[mostowski]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityMostowski.lean
[hereditary-cover]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityHereditaryCover.lean
[hcode-characterization]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityHCodeCharacterization.lean
[hcode-existence]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityHCodeExistence.lean
[graphs]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityHereditaryGraphs.lean
[set-codes]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahSetCodes.lean
[js-syntax]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahSyntax.lean
[set-tools]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySetFormulaTools.lean
[regular-code]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityRegularOpenCode.lean
[index-coding]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahIndexCoding.lean
[arithmetic-semantics]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahArithmeticSemantics.lean
[arithmetic-existence]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahArithmeticExistence.lean
[condition-semantics]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityJechShelahConditionSemantics.lean
[canonical-completion]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityCanonicalCompletion.lean
[absoluteness]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySetCodeAbsoluteness.lean
[selector-transport]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySelectorTransport.lean
[pure-selector]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityPureSelector.lean
[rigid-transport]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityRigidTransport.lean
[set-semantics]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySetSemantics.lean
[split-semantics]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySplitSemantics.lean
[bounded-splitter]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/BoundedSplitter.lean
[split-certificate]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicitySplitCertificate.lean
[reduction]: ../../../../submissions/classicism-results-2026-10-23-v1/source/topics/classicism/lean/Classicism/Results/Research/MaxAtomicityReduction.lean
