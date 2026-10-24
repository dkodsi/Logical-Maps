# Homogeneity, finite parameter locality, and modal amalgamation

Research notes, 22 October 2026. Original arguments by this research agent; not human checked, not Lean formalized, and no database records changed. These are ordinary mathematical arguments over the fixed relational language of C. The principal benchmark is now T = C + □Functional Choice. Most positive results use only C + □Plenitude; where only C5 is used this is stated. No assertion of literature novelty is made.

## Ranked reading index

1. **Finite information is preserved by pure definition** (§§1–5, especially Theorem 3). Under □Plenitude, arbitrary higher-order definitions using n proposition parameters and rigid first-order parameters stay in their finite Boolean algebra. Equivalent forms are whole-cell decision and atom indiscernibility. Consequences include the sharp n-individual bound for an extension-universal unary relation defined from n contingent bits.
2. **Natural infinitary resources preserve purity, while a logical choice witness can destroy it** (§§17–19). Existing Boolean meets/joins and canonical descriptions preserve the automorphism proof of NPC. Naming event-indexed choice and extending purity to that name makes NPC collapse contingency. Finite full models have the exact residual-symmetry criterion.
3. **Definable choice has a sharp finite bound and a genuinely independent countable case** (§§13–16, 24, 26). Finite proposition parameters define an atom selector exactly when they separate atoms. Countable separation suffices at countably many worlds; at Cantor-many worlds the specified countable-coordinate definability assertion holds in V=L and fails in the Cohen extension, while both full models satisfy □FC. These are ambient-relative semantic results, not a new incompleteness claim for C.
4. **Exact infinitary modal amalgamation is rectangularity of realized profiles** (§25). Finite independence recovers the old finite result; finite-pattern independence of countable blocks is insufficient, with an explicit full-T missing-corner countermodel. Countable quantification can even define a non-Borel truth set (§24).
5. **Maximalism has honest unboxed homogeneity enrichments** (§§7–8). The pinned Maximalist root satisfies IH; another Maximalist root fails it. Finite Maximalist roots can instead be pointwise pure-definable. This prevents an unrestricted claim that Maximalism has no natural consistent strengthening.
6. **Existing rigidity question: still unresolved here** (§§20–23). Tame Rigidity + Rigid Power ⇒ Weakly Rigid Power reduces exactly to scoped future tameness. Finite bounds satisfy the conclusion in bare C; bounded pointwise infinitary closure settles correspondingly small bounds. The free-root obstruction rules out a simple predecessor countermodel. No new settlement of that conjecture is claimed.

All theorem numbers below refer to this scratch report. Statements about added syntax or full-model definability retain their explicit semantics; they are not silently imported into original C.

## Source and evidence boundary

The starting source is the local proof `topics/classicism/writeups/c5-and-atomicity-imply-no-pure-contingency.md`: its atom transposition and conjugation proof follows Cian Dorr's sketch, as that write-up explains; its source locator is Classicism §2.2, p. 27 (16 May 2023 draft). The extensions below are new arguments, not attributed to that source. The framework is `topic.yaml` and `background.md`: types ending in e are NOT available, so no operation e→e is introduced.

For models use `models/full-infinite-s5.yaml` and the full action construction, Classicism §3.5, pp. 58–61. The Maximalist symmetry model is `models/coalesced-pinned-interpretations-root.yaml` and its write-up: Cian Dorr's 19 October 2026 construction, with the landing condition added in discussion with Claude Opus 5.5. Its local verification expressly lacks a second-reader check. The new free-root lemma below is proved directly; it is not silently attributed to Appendix E.

A proved-only `scripts.pmap.load_topic` / `Engine` query, with optional premises in the query rather than engine background, confirms: □Plenitude entails C5, Atomicity, □BF, Boolean Completeness, and No Pure Contingency. It does not entail Relational Choice: recorded choiceless full-S5 variants separate these. The new benchmark □Functional Choice supplies □Plenitude and choice. No conjectured record was used.

All assertions involving arbitrary automorphisms, infinite sequences, or cardinalities distinguish internal represented objects from external metatheory. The infinitary section adds semantics explicitly; it is not a theorem of an unspecified infinitary C.

## 1. General Boolean automorphism extension (C5 suffices)

**Theorem 1.** In C5, suppose f,g:t→t are mutually inverse Boolean algebra automorphisms of the propositions. For every relational type τ there are explicitly defined inverse operations F_τ,G_τ:τ→τ extending f,g, preserving application, logical constants, and quantification. For every pure term A, the transformed value is the value obtained by transforming all its free parameters. Individual parameters are unchanged.

At type e, “F_e x=x” is only metanotation: no term of type ee is claimed. Put F_t=f and G_t=g. Recursively, when σ is relational set

    F_(στ)(X) = λx. F_τ(X(G_σ x)),
    G_(στ)(X) = λx. G_τ(X(F_σ x)).

When σ=e, omit the nonexistent G_e/F_e and use λx.F_τ(Xx), respectively λx.G_τ(Xx). Every displayed operation has an admitted type.

**Proof details.** C5 gives ND and BF at all relevant types. Consequently equality propositions are bivalent (top or bottom), and any formula built from equality by Boolean connectives and quantifiers is bivalent. In particular the equations saying f,g are inverse Boolean automorphisms form a rigid hypothesis. Under such a hypothesis, necessitation of the DISCHARGED implication, K, and Modalized Functionality justify passing equations under λ. One does not apply Logical Equivalence to an optional-hypothesis equivalence.

BF and CBF give the exact infimum law

    q ≤ ∀x.Px  iff  ∀x.(q ≤ Px).

Indeed the left side is □∀x(q→Px), and BF/CBF exchange this with ∀x□(q→Px). A Boolean order isomorphism preserves every infimum that exists: if b=inf_x Px, then f b is a lower bound of all f(Px); any lower bound c pulls back by g to a lower bound of all Px, so c≤f b. Thus

    f(∀x.Px) = ∀x.f(Px).

No Boolean Completeness axiom is needed here: this particular infimum already exists as the quantified proposition.

Induction on types gives F_τG_τ=G_τF_τ=id and application equivariance. Equality constants are fixed because f fixes top/bottom and every F_τ is injective; the individual identity relation is fixed for the same reason. Quantifier constants are fixed by the displayed infimum law and bijective change of bound variable. Boolean constants are fixed because f is a Boolean automorphism. The modal operator is preserved as well: C proves that □p is equivalent to p=top, and C5 makes this proposition bivalent. Since f fixes top/bottom and fp=top iff p=top, f(□p)=□(fp). Structural induction on terms, using the inverse transformation in the abstraction case, proves equivariance. This generalizes the particular atom transposition in the existing write-up.

The theorem concerns automorphisms preserving logical denotations, not a claim that every such automorphism preserves the designated truth ultrafilter. Moving a world atom changes which propositions are true there.

## 2. Every represented permutation of world atoms extends (□Plenitude)

Let At(a) abbreviate Atom_t(a). A binary relation R:ttt is an *actual atom permutation* when its actual extension restricts to a bijection from At onto At. Values outside At×At are irrelevant.

**Theorem 2.** C+□Plenitude proves that every such R is the restriction of a unique Boolean automorphism f:t→t. Thus the represented Boolean automorphisms and represented atom permutations are mutually recoverable. Each f extends through the whole relational hierarchy by Theorem 1.

**Proof.** Atomicity, Boolean Completeness and Plenitude are available. For each p form the property

    Y_p(b) := At(b) ∧ ∃a(At(a) ∧ a≤p ∧ R(a,b)).

Boolean Completeness supplies q=∨Y_p. For every atom b,

    b≤q iff Y_p(b).

The forward nontrivial direction: if ¬Y_p(b), every Y_p-atom c differs from b and hence lies below ¬b. Therefore q≤¬b, contradicting b≤q. The LUB is unique. Plenitude represents the resulting unique assignment p↦q by f. The reverse permutation similarly supplies g.

The atom-support characterization shows f preserves top, bottom, meet and complement. For example an atom b is below f(p∧r) exactly when its unique R-predecessor lies below both p and r, exactly when b≤fp∧fr. Atomicity turns agreement on all atoms into equality. The same argument gives gf p=p and fg p=p. Actual equations may be boxed using C5; function identities follow from BF and Modalized Functionality. Uniqueness follows because a Boolean automorphism sends the atoms below p exactly onto the atoms below fp.

This uses no choice of representatives. It is NOT an additional strengthening of □Plenitude or □Functional Choice. It also does not assert that every external, unrepresented set-theoretic permutation is named by a relation in every Henkin model.

## 3. Finite Boolean locality: clean equivalent formulations

A first-order relation A of type e⋯et is *pointwise rigid* here when

    ∀x̄ (□A[x̄] ∨ □¬A[x̄]).

This explicit condition avoids silently substituting an unverified version of the database's general Rigid predicate.

Fix finitely many arbitrary propositional parameters p_1,…,p_n, any finite tuple of individual parameters, and any finite tuple of pointwise-rigid first-order relation parameters. Let φ be pure apart from those parameters. It may use unrestricted higher-order quantification and λ-abstraction. For ε∈{0,1}^n put c_ε=∧_i p_i^{ε_i}, with p^1=p and p^0=¬p. For n=0 the unique cell is top.

**Theorem 3 (finite locality).** Under C+□Plenitude, φ belongs to the finite Boolean subalgebra generated by p_1,…,p_n. Equivalent, more perspicuous formulations are:

1. **Whole-cell formulation:** each c_ε lies wholly below φ or wholly below ¬φ.
2. **Atom formulation:** any two atoms agreeing on all p_i agree on φ.
3. **Finite normal form:** φ is a join of some of the nonempty c_ε.

Under Atomicity(t), these formulations are equivalent as elementary Boolean-algebra statements. The new substantive claim is that the allowed pure formulas satisfy them.

For n=0 this is bivalence (and yields No Pure Contingency and its individual/rigid-first-order-parameter extension). For n=1 it says simply

    φ ∈ {bottom, top, p, ¬p}.

**Proof.** Take atoms a,b in the same cell. Their transposition fixes every p_i. By Theorems 1–2 it extends through the relational hierarchy, leaving individual parameters unchanged. It fixes every pointwise-rigid first-order parameter A: the transformed A[x̄] is f(A[x̄]), equal to A[x̄] because each value is top or bottom. Consequently the term-equivariance theorem fixes φ. Since a is exchanged with b, they agree on φ.

If a cell c had nonzero intersections with both φ and ¬φ, Atomicity would supply atoms a≤c∧φ and b≤c∧¬φ, contradiction. Hence every cell is decided. Their finite disjoint join is top, which proves the normal form.

An explicit normal-form coefficient is the bivalent proposition c_ε≤φ:

    φ = ∨_ε [c_ε ∧ □(c_ε→φ)].

This is a characterization, not an algorithm eliminating quantifiers: the displayed coefficients themselves refer to φ. The finite-subalgebra and whole-cell formulations are cleaner principle definitions.

## 4. Matrix normal form and the universal-profile obstruction

Let R:e^k t be defined by such a pure formula with the n propositional parameters. Set

    X_ε[x̄] := □(c_ε→R[x̄]).

Each X_ε is pointwise rigid. Theorem 3 and C5's BF/Modalized Functionality yield the relation identity

    R = λx̄. ∨_ε (c_ε ∧ X_ε[x̄]).

Thus R has at most 2^n different extensional profiles across worlds, indeed at most the number of nonempty cells. This is a uniform relation identity, not merely a separate pointwise claim.

**Corollary 4.** Suppose k=1 and R has the extension-universality property

    ∀X:et [PointwiseRigid(X) → ◇∀x(Rx↔Xx)].

If R is pure-definable from n propositional parameters, individual parameters, and pointwise-rigid first-order parameters, there are at most n individuals.

**Proof.** At a world in c_ε, R has the rigid profile X_ε. If R agrees there with a rigid X, that agreement is rigid (C5 and BF), so X equals X_ε already. Every rigid unary property is therefore one of at most 2^n possibilities. If n+1 distinct individuals existed, their 2^(n+1) finite haecceity unions would be distinct pointwise-rigid properties. Finite pigeonhole gives a contradiction. No external infinite cardinal arithmetic is needed.

The bound is sharp. In full S5 take D_e={1,…,n}, W=P(D_e), p_i={S:i∈S}, and

    R(x) := ∨_(i=1)^n (x=i ∧ p_i),

where the i are individual parameters. Every subset profile occurs, all 2^n cells occur, and □Functional Choice holds in the usual ZFC full construction. Thus a universal-profile witness with infinitely many individuals cannot be pure-definable from any finite list of propositions plus the allowed rigid parameters. The witness's existence is not contradicted: it requires more contingent information than those parameters supply.

## 5. Modal amalgamation preserved by pure definability

For two finite propositional tuples p̄,q̄ define **Boolean independence** by

    (◇c_ε(p̄) ∧ ◇d_η(q̄)) → ◇(c_ε(p̄)∧d_η(q̄))

for every ε,η. Empty cells are ignored. Equivalently, every nonzero element of the first generated finite Boolean algebra meets every nonzero element of the second. This is weaker and cleaner than requiring all Boolean cells of each tuple to be nonempty.

**Theorem 5.** Under □Plenitude, Boolean independence is preserved by the pure definitions permitted in Theorem 3. If φ depends on p̄ and ψ depends on q̄ (also on arbitrary allowed rigid/individual parameters), then

    ◇φ ∧ ◇ψ → ◇(φ∧ψ).

**Proof.** Theorem 3 makes φ and ψ unions of their respective cells. Nonzero φ contains a nonempty p-cell, and nonzero ψ a nonempty q-cell. Independence makes their intersection nonempty. The argument extends to any finite number of independent families.

The raw parameter-independence hypothesis is essential. In a full three-world S5 model let p={u}, q={u,v}. Then p≠q, both p and ¬q are possible, and p∧¬q is impossible. Syntactic disjointness of variables, or even actual distinctness of their denotations, supplies no amalgamation. This is an explicit □Functional Choice countermodel to that tempting strengthening.

## 6. Sharp limit of rigid-parameter stability

The restriction to first-order rigid relation parameters is essential. In the two-world full S5 model, take a contingent p and the higher-order haecceity H_p:=λq.(q=p), of type tt. Its membership is pointwise rigid by ND. Nevertheless

    ∃q(H_p q ∧ q)

is p and is contingent. Thus replacing “pointwise-rigid first-order parameters” with “arbitrary pointwise-rigid higher-order parameters” makes Theorem 3 false already with n=0, in a model of □Functional Choice. This is not a subtle failure of choice or completeness: the higher-order rigid parameter can name a contingent proposition.

Indeed a blanket stability schema for formulas with arbitrary such higher-order rigid parameters collapses all propositions to bivalence by this same haecceity instance. It therefore excludes ordinary nontrivial full-S5 models.

## 7. Pure individual homogeneity, and exact scope

Let IH be the following UNBOXED schema. For a pure formula φ(x̄) with only individual free variables, any two tuples having the same equality pattern agree materially on φ. Unary IH says every pure unary predicate is currently empty or universal.

**Theorem 6.** C5 proves the intensional version: equal-pattern tuples have identical φ-propositions. Under □Plenitude, every pure n-ary relation on individuals is one of the unions of equality-pattern classes; it is rigid. In particular each pure binary relation is one of bottom, equality, inequality, and top (with coincidences if the individual domain is a singleton).

**Proof of the extra individual symmetry.** Any finite permutation of individuals has a graph built from equality with finitely many individual parameters. Under C5 this graph is pointwise rigid. It can be lifted through all relational types without any ee operation. More generally, given a rigid bijection graph J on individuals, define transformations inductively on flattened relational types τ=σ_1⋯σ_k t. At arguments of type e use J as the graph; at relational argument types use the already constructed bijection. Send X to

    λȳ. ∃x̄ [∧_i Graph_i(x_i,y_i) ∧ X[x̄]].

Every graph fibre has one member and is rigid. The inverse graph gives the inverse operation; C5/BF lift the pointwise equations to identities. Application is preserved by construction, equality by injectivity, and quantifiers by bijective change of variables. Pure-term induction gives invariance. A finite partial bijection matching two equal-pattern tuples extends to a finite permutation (close its finitely many paths into cycles), proving the claim.

For a partition π of {1,…,n}, let δ_π be its equality-pattern formula and let A_π:=∃x̄(δ_π(x̄)∧φ(x̄)). C5 yields

    φ(x̄) = ∨_π [δ_π(x̄) ∧ A_π].

Under □Plenitude each closed pure A_π is bivalent, giving the asserted union of patterns. Under C5 alone the A_π may be contingent: do not erase the Atomicity/No-Pure-Contingency step.

There is a stronger, identity-level unary homogeneity schema

    (λx.φ(x)) = (λx.∀y.φ(y)).

C5 implies it. Pure Maximalism refutes at least one instance, because the finite C countermodel in the next section shows that instance is not a C theorem. This illustrates a real asymmetry for stable structural identities. It must not be confused with the unboxed IH schema, which is consistently addable to Maximalism.

## 8. A strict consistent homogeneity strengthening of pure Maximalism

**Theorem 7.** Pure Maximalism + IH is model-backed consistent relative to the accepted pinned-interpretations-root construction. IH is not a consequence of pure Maximalism: a new explicit free-root model below refutes even unary IH. Thus unboxed homogeneity is a genuine consistent strengthening, not merely an unverified proposed addition.

### 8.1 The positive model

Use `coalesced-pinned-interpretations-root`. Its root individuals are the countably many individual names in Σ+. Any permutation π of those names extends to an automorphism fixing the root and component objects, sending an interpretation arrow <V,I> to <V,I∘π^{-1}> (π fixes the other typed names). Component entities are unchanged. At the root, transform relational extensions by the induced permutations on argument domains, and reindex their component intensions by the arrow permutation.

Finite pinning is preserved: a finite support S goes to πS. The landing condition is preserved because the transported component is simply the old one at the reindexed interpretation. The counterpart condition holds since (I∘π^{-1})(πc)=I(c). Inverses are supplied by π^{-1}; application, logical constants, and satisfaction commute with the transformation. Hence equal-pattern finite individual tuples are automorphic at the root and satisfy the same pure formulas. This proves IH there. The source model already verifies pure Maximalism, BF, Actuality, and Relational Choice. This argument adds IH, not a claim that IH persists at the component worlds.

### 8.2 Free-root lemma (new direct construction)

Let B_1,…,B_r be C action models with distinguished objects, let D be any nonempty set, and choose maps h_j:D→D_e(B_j). Add a fresh root A with arrows to those distinguished objects and all their composites, no arrows back. Put D_e(A)=D. Recursively, for τ=σ_1⋯σ_k t, set

    D_τ(A)=P(D_σ1(A)×⋯×D_σk(A)) × ∏_j D_τ(B_j).

For t the first coordinate is a truth bit. Transport to B_j is projection to the j-th component (and at e is h_j). Application slices the root extension at the actual argument and applies the j-th component to the transported argument. Quantifiers have their ordinary root extension and the corresponding component quantifiers. Equality has actual equality at A and component equality in each B_j.

This is a model of C. β and η follow componentwise and by slicing. Every H axiom holds at A because truth, quantifiers and genuine equality there satisfy the ordinary rules, and at components by assumption. A λ-denotation is its arbitrary root truth set paired with the component λ-denotations, so it lies in the specified domain. If H proves a formula equivalence, the root truth sets of its abstractions agree and their component denotations agree by C in every B_j, proving Logical Equivalence. This proof uses only admitted relational types. It is the familiar free-root shape but permits an arbitrary specified e-map; no surjectivity or injectivity of h_j is required by C.

If some B_j satisfies pure Maximalism, so does A: each C-consistent pure sentence is true somewhere accessible from B_j and thus from A. No necessity of Maximalism is asserted.

### 8.3 Three-individual countermodel to IH

Let B be the pinned Maximalist model, whose distinguished individual domain is infinite. Add a free root A with D={a,b,c}, h(a)=h(c)≠h(b). Let Q be the closed pure sentence “there are at least four individuals,” and define

    E(x,y):=□(Q→x=y),
    φ(x):=∀y(E(x,y)→x=y).

Q is false at A and true at B. If h(x)=h(y), NI in B makes equality persist through every later world, so E(x,y) holds at A. If h(x)≠h(y), B itself falsifies Q→x=y. Thus E at A is exactly ker h, with classes {a,c} and {b}. Consequently φ(b) is true and φ(a),φ(c) false. A satisfies pure Maximalism but fails IH.

The same finite pure formula has an ordinary C countermodel using a four-individual full Henkin B instead. Hence its identity-level homogeneity instance is not a theorem of C, and Maximalism entails that identity's inequality. No dubious necessitation of an unboxed premise occurs.

### 8.4 Stronger root-engineering consequence

Any finite individual set D of size m≥3 can be made pointwise definable by pure formulas at a Maximalist root. For each a∈D choose a distinct integer k_a>m and a free root B_a with k_a individuals above a copy of the pinned Maximalist model; map ALL B_a individuals to one individual of that model. At A map a to one B_a individual and D\{a} to a different one. Let Q_a say “exactly k_a individuals,” and E_a(x,y)=□(Q_a→x=y).

At A, Q_a is false. At the immediate B_b worlds it holds exactly when b=a. Beyond every B_b all A-individuals have coalesced and hence remain equal. Therefore E_a at A has exactly the classes {a} and D\{a}. Its singleton-class formula φ_a uniquely defines a. Thus every finite relation on D is definable there by a finite Boolean combination of the φ_a. The model is still pure Maximalist through each B_a.

This is a substantive warning against deriving an absolute “few/no enrichments” conclusion merely from Maximalism's anti-necessitation behavior. It permits both a completely homogeneous actual individual domain and finite actual domains whose members are individually definable by pure modal formulas. Stable identity-level principles are a different matter.

## 9. Infinitary extensions: what changes and what does not

These are semantic extensions, not unqualified theorems of original C. Enrich formulas with specified countable meets/joins, interpreted as their actual Boolean infima/suprema, whenever the relevant model domains contain them. For pure-term induction, their denotations must be included in the allowed language/domain closure; merely having a metalinguistic conjunction of axioms does not add a proposition.

### 9.1 Countably many propositional parameters

The automorphism argument still shows: if two atoms agree on EVERY propositional parameter used by an infinitary formula, they agree on its value, provided the new connectives are interpreted by infima/suprema. Boolean automorphisms preserve existing infima/suprema. Thus a relation definable from a countable sequence of propositions has no more than 2^ℵ0 different world profiles externally.

Do NOT replace the finite Boolean-subalgebra conclusion by “belongs to the Boolean σ-algebra generated by the parameters” without further proof. With countably many parameters, equality of full truth vectors describes fibres; a fibre-saturated set may require an uncountable union of fibres. On W=2^N the coordinate propositions separate all worlds, so every subset is fibre-saturated, whereas only continuum many subsets belong to the generated Borel σ-algebra and P(W) has strictly larger cardinality. This explains the gap; it does not claim a particular non-Borel set is definable in an unspecified infinitary language.

For countably many individuals c_n, the countably infinitary definition

    R(x)=∨_n (x=c_n ∧ p_n)

does produce an extension-universal R in the full S5 model W=2^N, D_e=N, with p_n the coordinate propositions and the c_n rigid names. Hence the finite-parameter obstruction in Corollary 4 is exact: countably many contingent bits suffice for countably many individuals. The names/sequence and the infinitary connective are added resources, not a finitary pure term of C.

### 9.2 Compactness with finite parameter support

If a countable family of formulas all use the SAME finite propositional parameters and allowed rigid first-order parameters, Theorem 3 puts all their values in a common finite Boolean algebra. Consequently finite joint possibility implies joint possibility of the countable conjunction, whenever that conjunction is admitted and interpreted as its meet. A family of subsets of a finite set of nonempty cells with the finite-intersection property has nonempty total intersection. This is a genuine finite-support modal compactness theorem, even if the formulas have unbounded higher-order complexity.

Unrestricted countable modal compactness for arbitrary propositions is radically stronger and fails in every infinite full-S5 model in ZFC. Choose distinct atoms a_n and let p_n=∨_{k≥n}a_k. Every finite meet is nonzero, but their total meet is zero. This example works in an uncountable world set too: the p_n only use the selected countable subset. Conversely finite full-S5 models satisfy unrestricted compactness. Thus it is not an attractive way to require infinitely rich possibility: in full atomic models with ordinary choice it enforces finiteness of the world set.

## 10. Status and open points

Theorems 1–7 and the free-root/root-engineering arguments are proposed proved mathematical results, with full proof arguments above, not recorded database theorems. The final infinitary claims are explicitly semantic. No theorem says □Functional Choice is literally a maximal consistent theory or Maximalism literally a bottom element. These two theories remain incompatible, and the strict unboxed IH enrichment of Maximalism is positive counterevidence to an unrestricted “no natural consistent strengthening” claim.

The strongest new structural package is: represented atom permutations extend throughout the hierarchy; finite contingent parameter sets cannot generate new world distinctions under pure definition; Boolean independence therefore survives arbitrary pure higher-order definitions; universal profile witnesses need enough independent contingent information. The cleanest definitions are whole-cell decision and atom indiscernibility, rather than a circular normal-form coefficient formula.

## 11. Exact classification of pure propositional operations at finitely many worlds

This goes beyond locality. It is a semantic theorem about a model of C+□Plenitude with exactly m propositional atoms, where 1≤m<ω. No assumption that the rest of the hierarchy is externally full is needed. Atomicity and finite Boolean joins identify D_t with P(W), where W is its m-element atom set. C5 Functionality identifies a propositional operation with its ordinary function on those domains.

**Theorem 8.** The interpretations of closed pure terms of type t⋯tt (n propositional arguments) are EXACTLY the Sym(W)-equivariant functions P(W)^n→P(W).

Necessity follows from Theorems 1–2: every permutation of the finite atom set is represented by a finite equality-defined graph, extends to a Boolean automorphism, and extends throughout the hierarchy fixing all pure terms. Such a pure operation therefore commutes with every world permutation.

For sufficiency, an n-tuple of propositions partitions W into r=2^n Boolean cells c_ε. The orbit of the tuple under Sym(W) is exactly the vector of cell cardinalities s=(s_ε), with each s_ε≥0 and Σs_ε=m. An equivariant output must be fixed by the stabilizer of the tuple. That stabilizer contains every permutation within each cell, so its fixed subsets are precisely the unions of whole cells. Equivariance then says that the selected set of cells depends only on the size vector s.

Each size vector has a finite PURE test K_s(p̄): each cell has exactly s_ε atoms below it. “Exactly k” is expressed by k distinct atom witnesses below the cell and the assertion that every atom below it is among those witnesses. At k=0 it says the cell is bottom. These tests are equality-built and hence bivalent under C5. There are finitely many size vectors. If an equivariant function selects I_s⊆{ε:s_ε>0} at vector s, it is denoted by the closed pure term

    λp̄. ∨_s [K_s(p̄) ∧ ∨_(ε∈I_s)c_ε(p̄)].

This finite formula has no world names or nonlogical constants. Thus every equivariant map is pure-definable in this model.

**Exact count.** For a vector s there are 2^{|{ε:s_ε>0}|} output choices. Therefore the total number is

    2^{ Σ_(s_1+⋯+s_r=m) |{i:s_i>0}| }
    = 2^{ r · binom(m+r−2,r−1) },  where r=2^n.

The second equality counts a positive marked coordinate: for each of r choices there are binom(m+r−2,r−1) weak compositions with that coordinate positive. For n=0 this gives two pure propositions. For n=1 it gives 4^m pure unary operations. In the two-world model there are consequently 16 pure unary propositional operations among the 4^4=256 raw unary operations. The four extensional core operations of the separate quotient report are a different set; do not conflate that core with all pure operations.

## 12. Countably infinitary logic completes the countable-world classification

Work now in the FULL S5 model with countably infinite world set W, and add countable conjunctions/disjunctions under λ, interpreted as their Boolean meets/joins. Fullness ensures that every external permutation of W is represented and all the required connective denotations exist. Countable atom cardinality in an arbitrary Henkin model alone would not justify arbitrary external permutation invariance; one would additionally need all such permutations represented (for example from countable parameter-family closure). This restriction is deliberate.

**Theorem 9.** In this extension, the pure n-ary propositional operations are exactly the Sym(W)-equivariant functions, for every finite n.

Necessity is unchanged: automorphisms preserve the new meets/joins. For sufficiency, the orbit of a finite tuple is determined by the cardinality of each of its finitely many Boolean cells, now in N∪{aleph_0}. There are countably many such vectors. A finite size is tested as above; an infinite cell is tested by the countable conjunction of “at least k atoms below this cell,” k=1,2,…. As W is countable this distinguishes all possible cell sizes. A countable disjunction of the corresponding size tests, each paired with the selected union of cells, defines any equivariant function.

This is a strict expressive increase over finitary purity. The finitary pure language is countable and thus has only countably many closed terms. There are continuum many distinct equivariant unary operations. Explicitly, for each S⊆N_{>0}, define

    f_S(p) := p ∧ (∨_(n∈S) Exactly_n_Atoms_Below(p)).

If S≠S', choose n in their symmetric difference and a proposition consisting of exactly n atoms; the outputs differ. The infinitary syntax can therefore encode any subset of N without a nonlogical constant. This must be acknowledged when enlarging “pure” Maximalism: the class of pure identities itself changes, not just a convenient notation for a fixed finitary class.

The theorem does not say an arbitrary infinitary pure sentence can distinguish world atoms. With no parameters, every pure sentence still has only the values top or bottom. Countable syntax adds cardinality-sensitive operations while retaining the full world-permutation symmetry.

## 13. Exact parameter cost of choosing a world atom

Write AS(S), for S:tt, for

    ∀p(p≠bottom → At(Sp) ∧ Sp≤p).

□Functional Choice supplies such an S: apply Functional Choice to the serial relation choosing an atom below each nonzero p and bottom at p=bottom.

**Theorem 10.** Fix n propositional parameters p̄ and any allowed individual/pointwise-rigid first-order parameters. An atom selector is pure-definable from those parameters if and only if every nonempty Boolean cell of p̄ is itself an atom. Equivalently, p̄ separates every pair of distinct world atoms.

Necessity is stronger than a failure to choose a pure single atom. Let C be a nonempty parameter cell. For a pure definition of S, locality applied to S(C) uses only the original p̄, because C is already their Boolean term. Hence S(C) is a union of parameter cells. AS(S) makes it a nonzero atom below C; the only nonzero union of parameter cells below C is C itself. Thus C is an atom.

For sufficiency, fix a finite order on the 2^n cells. Given q, return its intersection with the first cell it meets. The test that an intersection is nonzero is bivalent under C5, so a finite Boolean case-definition is a pure term with the parameters p̄. Every nonempty cell is a singleton atom, so the selected intersection is an atom. At q=bottom return bottom.

Consequently a model with exactly m finite world atoms requires at least ceil(log_2 m) propositional parameters for such a pure definition; this bound is attained by binary labels on the atoms. With infinitely many atoms no finite list of contingent propositional parameters suffices, even though Functional Choice supplies an unparameterized EXISTENTIAL witness S. Arbitrarily complicated pure higher-order quantification does not overcome this finite-information bound. Infinitary syntax using the SAME finite parameters does not overcome it either, since atom-swap invariance remains.

**Automorphism-invariant choice.** A particularly clean canonicalization proposal is

    ∃S [AS(S) ∧ ∀f(BAAut(f) → ∀p.S(fp)=f(Sp))].

Under □Plenitude this is equivalent to the propositional algebra having one atom. If there are two atoms, apply S to top and swap its chosen atom with another: equivariance requires the chosen atom both to remain fixed and to move. Conversely with one atom, S=id works. Thus this seemingly natural global canonicalization collapses the nontrivial modality; it is not a new intermediate enrichment of the strong benchmark.

## 14. Countable parameters: separation versus definable selection

This section uses a specified extension of the language: countable well-founded formulas, countable conjunctions/disjunctions interpreted as meets/joins, and those formulas permitted inside λ-abstractions. Countably many named propositional PARAMETERS are permitted. Naming them as constants avoids any convention in L_(ω1,ω) that the set of free variables of a formula must be finite. Each individual formula still has a countable syntax tree. There are no arbitrary uncountable conjunctions and no uncountable parameter family in this section.

Work first in a full S5 model, with world set W and propositions P(W). A family (p_i) separates worlds when any distinct u,v differ on membership in some p_i. Equivalently it separates proposition atoms. Every definable atom selector requires separation: if distinct world atoms agree on all parameters, their transposition fixes the entire parameter family and hence every well-founded pure infinitary term, but cannot fix the selector's value on the union of those two atoms.

**Theorem 11 (countable positive case).** If W is nonempty and at most countable, countably many propositional parameters admit a countably-infinitary pure definition of an atom selector exactly when they separate W.

Only sufficiency is new. Fix an external enumeration w_0,w_1,... of W, permitting repetitions in the finite case. For the binary parameter code s_k of w_k, put

    c_k = ∧_i p_i^(s_k(i)).

Separation gives c_k={w_k}. For q:t define

    S(q) = ∨_(k<ω) [c_k ∧ (c_k≤q) ∧ ∧_(j<k) ¬(c_j≤q)].

The order tests are bivalent. For nonzero q the set of indices k with c_k≤q is nonempty and has a least member; exactly its summand survives. At zero all summands vanish. This is a countable well-founded formula under λq. The enumeration and its binary codes are encoded in the syntax; they are not extra semantic object parameters. Necessity does not depend on countability.

**Theorem 12 (unbounded infinitary positive case).** In a ZFC metatheory, if arbitrary set-sized conjunctions/disjunctions under λ are permitted, any separating SET of propositional parameters admits such a definition, for any set W.

Well-order W as (w_ξ:ξ<α). Form the atom c_ξ from the complete parameter code of w_ξ, then use the same displayed priority formula with k replaced by ξ and j<k by η<ξ. Each index set is a set. This is a definition in the stronger language, not an original-C theorem or a countable-syntax result. The external well-order can have uncountable information and is encoded in the syntax. If working without metatheoretic Choice, this proof requires a well-order of W; separation alone does not supply one.

For an arbitrary uncountable W, countable parameters can separate W only if |W|≤2^ℵ0. Even when they do, Theorem 11 does NOT extend automatically to countable syntax. The following theorem establishes a relative-consistency obstruction rather than merely observing a gap in the priority construction.

## 15. A full □Functional Choice model with separating countable parameters but no countably-infinitary definable selector

**Theorem 13 (relative consistency).** Relative to ZFC, there is a set-theoretic universe V in which the following full S5 model exists: W=2^ω, D_e a singleton, and the full relational type hierarchy over D_t=P(W). This model satisfies □Functional Choice. Its countable coordinate propositions

    p_n={w∈2^ω:w(n)=1}

separate every pair of atoms. Nevertheless, no pure countably-infinitary term using only these parameters defines an atom selector. The syntax here is precisely the countable well-founded syntax of §14, with no extra nonlogical parameters. The conclusion remains true after allowing an additional COUNTABLE named parameter family whose indexing and entire interpretation are definable from a real. More generally it suffices that the used symbol labels and their interpretations are jointly real-coded/real-definable. An arbitrary definable family with uncountable labels is not covered: a single label could itself encode a parameter not definable from a real. This qualification was identified in the parent agent's audit.

**Set-theoretic construction and proof.** Start with a ground universe L satisfying ZFC and force with Add(ω,ω1): finite partial functions from ω1×ω to 2, ordered by extension. Let V=L[G]. This is the ordinary forcing extension, which retains Choice; it is NOT the symmetric Cohen model.

1. Every real r∈V belongs to L[G↾I] for some countable I⊆ω1 belonging to L. For each n choose in L a maximal antichain deciding n∈r's name. The forcing is ccc: an uncountable family of finite conditions has an uncountable Δ-system subfamily with a common assignment on the finite root, and therefore pairwise compatible members. Each chosen antichain is consequently countable. The union of the coordinate supports of the countably many antichains is a countable I in L; a name using only these antichains is an Add(ω,I)-name for r.

2. Put M=L[G↾I]. The remaining forcing Q=Add(ω,ω1\I) is weakly homogeneous over M. Given finite p,q, a coordinate permutation moving the finitely many first coordinates of p away from those of q makes the transformed p compatible with q. Such forcing automorphisms fix the canonical names of every member of M. Thus every sentence of the forcing language with ground parameters is decided by the top condition: if some p forces it, move p to compatibility with any proposed condition forcing its negation.

3. Every real ordinal-definable from r in V belongs to M. Suppose y is the unique real satisfying θ(y,r,ᾱ), where ᾱ is a finite tuple of ordinals. Both r and the ordinals are in M. Weak homogeneity decides, for each n, the ground-parameter sentence “the unique such y contains n.” The forcing relation in M therefore defines the set of all n whose membership sentence is forced by the top condition. That set is in M and equals y. The same argument first decides and affirms the unique-existence assertion, since it holds in the actual generic extension.

4. At least one coordinate ξ∉I remains, and the corresponding Cohen real c_ξ is not in M. Hence some real is not ordinal-definable from r. Since r was arbitrary, V has NO well-order of its reals definable from any real parameter: if < were defined from r, every real y would be definable from r and the ordinal order type of its <-predecessors.

5. In V, construct the stated full S5 model. Its types, interpretations of logical symbols, and sequence (p_n) are definable without parameters in set theory: W=P(ω), individuals a fixed singleton, propositions P(W), and relational types full function sets. The usual full-model proof of Functional Choice uses set-theoretic Choice, available in V. Constant full domains make it true at every world.

6. A countable well-founded syntax tree over the countable type alphabet and the names p_n can be coded by a real r. Recursive interpretation of this set-sized tree in the definable full model makes the denotation of the term definable in V from r. There is no semantic actual-world parameter needed for a term's intension; even if one is included in a presentation of the semantics, that world is itself a real and can be joined to r.

7. If such a term denoted an atom selector S, then X↦the unique w∈S(X) would be a choice function on every nonempty subset of W, definable from r. Transfinite recursion repeatedly choosing from the remaining elements canonically well-orders W: at stage α choose S(W\{w_β:β<α}) whenever this remainder is nonempty. Hartogs' theorem guarantees termination, since continuing to the Hartogs ordinal of W would give an injection of that ordinal into W. Replacement and the uniqueness of the recursion make the resulting well-order definable from r. This contradicts step 4.

This proves the theorem. In the customary relative-consistency reading, forcing gives Con(ZFC)⇒Con(ZFC+the stated model/definability assertion). A concrete transitive-ground presentation is sufficient if that stronger metatheoretic hypothesis is preferred. “Full” throughout means full relative to the ambient universe V in which the model and formulas are being considered; no absoluteness to arbitrary outer universes is asserted.

**Primary source boundary.** The forcing facts used here are standard and the argument is supplied above. A checked primary exposition is Asaf Karagila, *Forcing & Symmetric Extensions*, https://karagila.org/files/Forcing-2023.pdf, Chapter 11, Proposition 11.4, printed p. 53 (PDF p. 55): weak homogeneity decides every sentence with ground-model parameters. The present application to pure infinitary atom selection is our argument, not a result attributed to those notes. No literature-novelty claim is made.

The precise distinction is: □Functional Choice supplies existential selectors, while homogeneity and coding constraints restrict selectors that can be DEFINED purely from a prescribed information source. The full model has many selectors, and every pair of worlds already has a different countable parameter code. Definable selection can still fail because selecting uniformly from ALL subsets requires a definable global well-order, not merely distinct codes.

## 16. A clearer exact criterion: a definable world well-order

In full S5, relative to any specified parameter family, pure definability of an atom selector is equivalent to pure definability of a rigid well-order of the atoms, provided the language includes ordinary higher-order quantification (as C does) and the proposed parameters/terms are available. This is an exact improvement over “the parameters separate atoms,” which is only a necessary condition outside the finite/countable positive cases.

The implication from an atom well-order to a selector takes the least atom below the input proposition. Unique comprehension represents that atom-valued assignment. More explicitly, a tt-term can be written as the join of those atoms that are least below q; since there is exactly one for q≠bottom, this join is that atom. At bottom choose bottom.

For the reverse implication one can avoid adding an ordinal sort or a transfinite recursion symbol to the logical language. Given S, call a pair (B,R) a **compatible choice chain** when B is a rigid set of atoms, R is a rigid strict well-order of B, and each a∈B equals

    S(¬∃b[B(b) ∧ R(b,a) ∧ b]).

The existentially quantified proposition inside the complement is the join of the predecessors of a. All required types—tt for B, ttt for R—are relational and admitted. Well-order means that every nonempty subset of B has an R-least member; in the FULL model the higher-order quantifier ranges over all such subsets.

Any two compatible choice chains agree as long as both continue. Formally, identify each with its unique ordinal-indexed enumeration. At the least index at which they could disagree, both must choose S of the complement of precisely the same preceding set, contradiction. Thus one chain is an initial segment of the other. The union of all compatible choice chains is consequently a well-order and remains compatible: the predecessor set of an existing element does not change when its chain is extended. If an atom were omitted from its domain, S of the nonempty complement would append a new last element, contradicting the definition of this union. Hence the union well-orders all atoms.

Its order relation has a FINITARY higher-order definition from S:

    a <_S b  iff  ∃B∃R [CompatibleChain_S(B,R) ∧ R(a,b)].

Rigid versions of the relations are expressed by □B(a), □R(a,b), or by explicit pointwise-rigidity clauses. The displayed construction thus stays in the original relational TYPE system. Its present justification is for full S5 semantics; no unproved Henkin-model external-well-foundedness claim is being made. Substituting an infinitary definition of S preserves the relevant bound on syntax size.

This logical construction also explains why adding a named rigid well-order of world atoms solves the selector problem immediately. Such a higher-order parameter contains much more than countably many proposition labels. It is outside the first-order rigid-parameter allowance of the finite-locality theorem.

## 17. Which new logical resources preserve purity?

The definitions of “pure” and the class of logical constants matter mathematically. This is sharper than the familiar warning that adding a new axiom can change a theory. An EXISTENTIAL choice theorem need not admit a named LOGICAL witness while preserving a purity-indexed schema.

The parent's report `.reproduction/classicism-research/world-indexed-choice-gallin.md` proves that T supplies an event-indexed choice operation ε of type t(τt)τ, for relational τ, satisfying

    □∀a,P [Inhab(a,P) → Sat(a,P,ε(a,P))],

where Sat(a,P,y) means a≤Py and Inhab(a,P) means ∃y Sat(a,P,y). Unlike its world-only version, this law permits every event a, including top.

**Theorem 14 (logical choice plus expanded purity collapses contingency).** Add a constant ε of this kind at output type t and designate it logical, so its occurrences are allowed in pure terms. If No Pure Contingency is extended to this enlarged pure language, T implies Extensionality at every relational type.

Indeed let b=ε(top,Atom_t). Atomicity supplies some atom, and C5 settles the atom predicate, so Inhab(top,Atom_t). The choice law gives Atom_t(b). Now b is a closed sentence of the enlarged pure language. Apply NPC both to b and to ¬b; excluded middle gives □b∨□¬b. The second alternative would make b=bottom, impossible for an atom. Hence b=top and top is an atom. Every proposition is therefore bottom or top. At type t, actual equivalence implies identity; at a higher relational type, pointwise equivalence consequently implies pointwise identity, and global collapse makes the universal identity statement necessary. Modalized Functionality gives identity of the relations.

Naming an ε witness with its displayed law is conservative for OLD-language T: every model of T has such a witness and expands by interpreting the new constant as one. Extending the NPC schema to the newly designated logical constant is the additional nonconservative step. Treating that step as automatic would be wrong. No claim is made that the old definition of C already includes ε, or that changing its proof rules is merely notational.

**Canonical unique description behaves differently.** For flattened relational output τ=σ̄t, write Unique(a,P) for ∃y[Sat(a,P,y)∧∀v(Sat(a,P,v)→v=y)]. The parent supplied the following OLD-language pure term, whose verification is included here:

    D(a,P) := λz̄ [Unique(a,P) ∧ ∀y(Sat(a,P,y)→y[z̄])].

For τ=t the tuple z̄ is empty. Under C5, Unique and Sat are settled. If y* is the unique witness, it remains the unique witness necessarily; each matrix value of D is therefore necessarily equivalent to y*[z̄]. Modalized Fregean identity at t and BF/Modalized Functionality at higher relational types yield D(a,P)=y*. If Unique is false, its negation is settled and the same reasoning gives D(a,P)=bottom_τ. Thus C5 already proves that this explicit term is the canonical event-indexed unique-description operator with bottom as its default. No choice of an unspecified witness operator is needed.

Naming D is an actual definitional extension. Every expression involving it can be expanded into a pure old-language expression, so the corresponding NPC instances are preserved. This distinguishes three resources cleanly: event-indexed choice exists under □Functional Choice; canonical event-indexed unique description is already pure term-definable under C5; a logical choice constant combined with expanded NPC collapses contingency. The difference between arbitrary selection and unique description survives the move to explicit event arguments.

## 18. Complete finite-model criterion with arbitrary typed parameters

The finite-bit result admits a broader exact formulation, covering higher-order rigid parameters as well as proposition labels. Work in a FULL S5 model with nonempty FINITE individual set D and finite world set W. All relational type domains are then finite. Let G=Sym(D)×Sym(W), acting recursively on types by application-preserving conjugation. Every element of G preserves the logical interpretation. Conversely every automorphism of the UNPOINTED full typed logical structure is determined by its action on D and on the world atoms, so this is its complete automorphism group. As in §1, an automorphism may move the designated world; it is not required to preserve actual truth at that world.

**Theorem 15 (finite typed definability).** Given any finite tuple p̄ of parameters of arbitrary admitted types, a relational entity v is pure-definable from p̄ exactly when every member of G fixing p̄ fixes v.

Necessity is term equivariance. Here is a direct sufficiency proof, avoiding an appeal to an abstract definability theorem. Enumerate D by x_1,...,x_d and W's atoms by a_1,...,a_m. Every entity of every relational type has a finite table. Recursively on types, that table has a term using these base parameters: for an input tuple, test equality with each listed input tuple and return the join of the named atoms specified by the table. Relational inputs themselves have such terms by the earlier stages of the type recursion; individual inputs use the x_i. Equality tests are bivalent. Thus each of p̄ and v has a finite pure table term T_p̄(x̄,ā) and T_v(x̄,ā).

Quantify over all enumerations x̄,ā of the individual domain and atom set whose table terms T_p̄ equal the GIVEN parameters p̄. Such enumerations exist. Any two satisfying enumerations differ by a member of G fixing p̄, hence give the same T_v because of the assumed invariance. For v of flattened relational type σ̄t, the defining term is

    λz̄. ∃x̄∃ā [Enum_D(x̄) ∧ Enum_Atoms(ā)
                    ∧ T_p̄(x̄,ā)=p̄ ∧ T_v(x̄,ā)[z̄]].

All guard formulas are bivalent, and all surviving values are v, so the term denotes v. Every displayed conjunction and quantifier block is finite. This argument concerns a fixed finite model; its table formula may depend on that model's finite sizes and on v's finite table. It is not a uniform syntax theorem across all cardinalities.

**Corollary 16 (exact finite selection criterion).** In this finite full model, the parameters p̄ admit a pure definition of an atom selector exactly when every automorphism fixing p̄ fixes EACH world atom.

For necessity, if the stabilizer moves an atom, take a nonsingleton orbit O of its action on W. The proposition O is fixed by the stabilizer. An equivariant selector would choose a singleton inside O fixed by the entire stabilizer, contradicting transitivity of the orbit. For sufficiency, if the stabilizer fixes every world, it fixes every proposition and every function P(W)→P(W), including any atom selector. Apply Theorem 15. This recovers the finite propositional-parameter criterion because the stabilizer of p_1,...,p_n contains precisely all within-cell world permutations. For higher-order parameters, “rigid” alone is inadequate; the correct condition is that their stabilizer have trivial action on the world atoms.

This supplies another clean formulation of the infinite obstruction. In the Cohen example of §15 the coordinate parameters already have TRIVIAL world stabilizer, yet countable pure definability still fails. Automorphism invariance is necessary in every case, sufficient in the full finite case, and insufficient in that infinite setting. No conflation of invariance with definability is needed.

## 19. Infinitary purity preservation in Henkin models

**Theorem 17 (semantic closure theorem).** Let M be a Henkin model of T, or more generally of the assumptions of §§1–3. Keep its type domains fixed. Extend its pure syntax by any specified well-founded set-sized conjunctions and disjunctions, assuming: (i) each admitted connective denotes the existing Boolean meet/join of its operand denotations in D_t; (ii) every admitted λ-abstraction has a denotation in the specified type domain and obeys the usual β/application semantics; and (iii) no new constants are introduced unless their denotations are fixed by the atom-transposition extensions. Then every closed pure sentence in the extended language denotes bottom or top. The parameter versions of NPC and finite Boolean locality from §3 also persist.

**Proof.** The internal transposition of any two atoms extends to inverse maps F_τ on EVERY type domain by §§1–2. An external Boolean order isomorphism preserves any existing set-indexed infimum or supremum. This is a purely order-theoretic assertion: the image of a greatest lower bound is a lower bound, and every other lower bound pulls back to a smaller one. The family of operands need not itself be represented by an internal relation or indexed object.

Well-founded induction on the extended syntax therefore proves the same covariance equation as in Theorem 1. At a conjunction/disjunction node use preservation of its existing meet/join; at λ use the stated β/application semantics, the inverse transformation of the bound variable, and C5 Functionality. The original quantifiers are already preserved by Theorem 1. Every closed pure proposition is fixed by every atom transposition. If it and its complement were both nonzero, Atomicity would supply an atom on each side, whose transposition would move the proposition. Thus its value is bottom or top. If there are finite propositional parameters, restrict to swaps within their cells; the whole-cell conclusion follows exactly as before. Individual and pointwise-rigid first-order parameters remain fixed.

These are precise MODEL assumptions, not an unspecified infinitary proof calculus. One cannot enlarge a Henkin model's domains to accommodate new terms and silently assume its old automorphisms extend; the theorem begins with a fixed model whose domains meet the stated closure requirements. Full S5 models automatically provide the needed denotations for set-sized Boolean connectives and admitted λ-abstractions. No external fullness of a general Henkin model, and no external completeness beyond the particular admitted meets/joins, is assumed.

The same argument applies to a further logical operation whenever its semantic interpretation commutes with these transformations. It does not assert that arbitrary generalized quantifiers have that property. Canonical descriptions of §17 satisfy the condition because they expand into old pure terms. The event-choice constant of that section fails it: its value at (top,Atom_t) singles out an atom.

The sufficient invariance condition is stronger than necessary. In the finite full models of §18 there is an exact criterion: after designating a finite tuple of typed constants logical, expanded NPC holds if and only if their stabilizer in G acts transitively on W. Transitivity forces every definable proposition to be empty or all of W. Conversely a proper world orbit is stabilizer-invariant, so Theorem 15 defines it purely in the expanded language; either it or its complement is an actually true contingent sentence.

For example let |W|=m≥3 and designate the Boolean automorphism induced by a fixed m-cycle as a logical constant. Its centralizer contains the transitive cyclic group, so expanded NPC still holds. This constant is not old-language pure-definable: it fails to commute with all world permutations. Thus some noncanonical added structure is compatible with purity, provided it preserves enough world symmetry. A designated atom selector is not: its chosen atom below top is fixed by the stabilizer, which prevents transitivity unless there is only one world. The general semantic closure theorem applies to every admitted well-founded infinitary formula; this finite example uses only the residual transitive symmetry and therefore also survives invariant infinitary connectives.

## 20. Follow-up on existing rigidity conjectures: exact status and a scoped reformulation

At the parent's request, the lane briefly examined `rigid-rigidity-implies-rigid-power`. That conjecture is ALREADY REFUTED by the recorded `coalesced-two-extensional-arithmetics-root`; no new-settlement claim is made. The record's old conjecture text alone is not its current derived status. The generic obstruction is a root with independent component projections: every component rigid relation can lift by a cylinder, while a rigid root graph can force an attempted subrelation lift to have a forbidden projection in the other component.

The subsequent target is `tame-rigidity-and-rigid-power-imply-weakly-rigid-power`. A fresh proved-only Engine query, with Tame Rigidity and Rigid Power as the queried premises, reports no entailment, no exclusion, and no recorded separating model for Weakly Rigid Power. It likewise gives no entailment or separation for □Tame Rigidity. This is a report of local derived evidence, not a literature-open claim.

Put W(Y)=WeaklyRigid(Y), R(Y)=Rigid(Y). Define the scoped principle

    ST := ∀F [R(F) → □∀Y((W(Y) ∧ Y≤F)→R(Y))].

This says: every future weakly rigid subrelation of a presently rigid bound is rigid. The occurrences of F inside the box are transported in the usual way.

**Lemma 18.** Over C, Weakly Rigid Power implies Tame Rigidity, Rigid Power, and ST; conversely Tame Rigidity + Rigid Power + ST implies Weakly Rigid Power.

The first two implications are recorded. For ST, the proof of `weakly-rigid-power-implies-rigid-power` shows that for a rigid F, P_F:=λY(W(Y)∧Y≤F) and R_F:=λY(R(Y)∧Y≤F) are identical: Weakly Rigid Power makes P_F weakly rigid, its implication to Tame Rigidity at this HIGHER type makes P_F rigid, and persistence then gives P_F≤R_F. Equality of these properties is precisely the needed scoped implication. Conversely a weakly rigid F becomes rigid by Tame Rigidity. ST gives necessary coextension of P_F and R_F, hence their identity in C. Rigid Power makes R_F rigid and therefore weakly rigid, proving the desired conclusion.

Thus the unresolved implication is exactly the question whether its two premises already give ST. □Tame Rigidity is sufficient, but without BF it is unnecessarily global. The recorded `ultralimit-fork` satisfies □Rigid Power and □BF while failing Tame Rigidity, so Rigid Power alone does NOT even ensure Tame Rigidity below rigid bounds: its universal relations are rigid by □BF.

Type wording needs care. For a NULLARY proposition p:t, C proves

    WeaklyRigid(p) ↔ (□p∨□¬p),

and consequently Tame Rigidity for nullary propositions is a C theorem. If p is actually false, weak inextensibility tested against bottom forces □¬p; if actually true, weak persistence forces □p. Conversely either alternative gives both weak conditions, and 4 makes them necessary. This does not settle Tame Rigidity for unary properties of propositions (type tt), or other relational argument types. A phrase such as “failure at type t” must distinguish these two uses.

## 21. Finite extensions already have tame powers in C

For a tuple ā define its haecceity H_ā(x̄):=∧_i(x_i=a_i). C proves every such haecceity rigid, and finite disjunctions of rigid relations rigid. Weakly rigid relations with the same ACTUAL extension are identical: persistence of one and inextensibility of the other give both algebraic entailments.

**Lemma 19 (finite case, original C).** If a weakly rigid F has a finite actual extension {ā_1,...,ā_n}, it is rigid. Moreover its weak power P_F is rigid, so the Weakly Rigid Power conclusion holds for this F without assuming Tame Rigidity or Rigid Power.

Let H=∨_(i≤n)H_ā_i. It is rigid and coextensive with F, so F=H. At every future world F's extension is exactly the images of this finite list. Any weakly rigid Y≤F there has a finite actual extension, hence by the same argument equals the disjunction of the haecceities of some subset of the transported list. Conversely every such finite disjunction is rigid and below F. Therefore, necessarily,

    P_F = ∨_(I⊆{1,...,n}) H_(∨_(i∈I)H_ā_i),

where the outer H is the haecceity of a relational entity. More formally this display abbreviates necessary pointwise coextension, which gives relation identity in C. There are only finitely many subsets I, so the right side is a finite disjunction of rigid haecceities. This proves the claim. Repeated list entries and future identifications cause no problem; a subset of the image list is always the image of a subset of its indices.

The assertion is a schema for explicitly finite lists, with an empty list allowed; no unverified internal notion of finiteness is substituted. It gives a useful lower bound for any countermodel to the existing conjecture: its failing weak power must have an infinite actual bound.

## 22. Pointwise infinitary haecceity joins settle the rigidity package in the enriched semantics

This is an added-language MODEL theorem, not a proof of the original finitary conjecture. Work with ordinary intensional action semantics. Assume that at every object, for every SET E of actual argument tuples, the expression

    H_E := λx̄.∨_(ā∈E) ∧_i(x_i=a_i)

is admitted with the indicated actual parameters, and the disjunction is evaluated POINTWISE at every future object. Existing domains must contain its denotation. Thus along an arrow h its extension is exactly hE. These conditions are stronger than saying the Boolean algebra has an order-theoretic join of the haecceities.

**Theorem 20.** Under this unbounded parameterized pointwise λ-closure, every actual extension has a rigid coextension H_E. Hence □Rigid Comprehension and □Tame Rigidity hold. Rigid Power and Weakly Rigid Power hold at every world as well.

The exact-image relation h↦hE is persistent. At a future object reached by h, suppose a test relation Z necessarily holds of each member of hE. Every later extension of H_E is k(hE), so it is contained in Z there. This proves inextensibility at that object, and the argument applies at every h. Thus H_E is rigid.

Every weakly rigid relation is identical to the H_E of its actual extension by the coextension argument in §21, proving Tame Rigidity. Every rigid relation is likewise an exact-image relation.

For Rigid Power, let F=H_E, let h be an arrow, and let X≤hF be rigid at its target. Write D for X's extension there. Then D⊆hE and X=H_D. Put

    A={ā∈E:h(ā)∈D}.

Its exact-image relation H_A is rigid, lies below F, and transports to H_D=X. No choice of preimages is needed: take ALL preimages in E. Thus every future rigid subrelation of hF is the image of a current rigid subrelation of F. The definable power property consequently has exact-image extensions and is itself rigid. The argument works at every object. With □Tame Rigidity this also gives □Weakly Rigid Power by the recorded implication.

**Bounded version.** If only countable pointwise haecceity joins with countably many named parameters are guaranteed, the same proof establishes the Weakly Rigid Power conclusion for every weakly rigid F with at most countable actual extension. Its exact-image representation is available; all future subrelations of it have at most countable extensions; and the preimage A above is a subset of the original countable E. The power property's OWN actual extension can be uncountable, but its denotation is already supplied by the old finitary definition. Its exact-image property directly proves rigidity, so an uncountable disjunction defining that power property is not required. The finite version is Lemma 19.

**Choice boundary.** In a ZFC metatheory, unbounded closure also gives □Relational Choice and □Transversal Choice directly in these models: choose an actual functional graph or transversal SET at an object and take its haecceity disjunction, obtaining a relation with exactly that actual extension. Repeating the argument at every object yields the boxed schemata. This is a semantic consequence of external Choice plus the stated representation closure, not a bare-C syntactic proof of Choice.

The ultralimit fork explains why the word POINTWISE is essential. Its Boolean order joins recompute the ultralimit coordinate; an infinite join need not equal the pointwise union at that coordinate. A countable witness already suffices: choose root propositions p_n that are true only at terminal world n and false at s,u and other terminals. The pointwise union of their haecceities has only the false proposition in its extension at u, whereas at every terminal n its extension contains both truth values. The ultralimit domain condition would therefore require both values at u. This pointwise haecceity union is absent. The available algebraic join inserts the extra value at u and is weakly rigid but not rigid at s. Thus Boolean Completeness, even boxed and with Atomicity and BF, does not license the infinitary semantics used in this theorem.

## 23. Free roots cannot hide a later failure of Tame Rigidity

For the free-root construction of §8.2, with any finite nonempty family of components B_j and arbitrary individual maps, there is an exact obstruction:

**Lemma 21.** Tame Rigidity holds at the free root A if and only if it holds at every distinguished component B_j (and hence for every weakly rigid relation there, with its actual meaning of rigidity). This is a semantic result for that construction, not a general modal equivalence in C.

First observe a coding fact valid in C. Send an argument tuple ā to its tuple haecceity H_ā of relational type ρ. For Y of that tuple type put

    Y^(Q):=∃ā(Y[ā]∧Q=H_ā).

Then Y is weakly rigid iff Y^ is weakly rigid, and Y is rigid iff Y^ is rigid. The forward weak direction uses persistence and transports witnesses; for inextensibility pull a test Z(Q) back to Z(H_ā). For the reverse direction, a test Z(ā) is pushed to

    Z^(Q):=∀ā(Q=H_ā→Z[ā]).

Injectivity of haecceity coding and NI make this test necessarily true of a coded member whenever the original test is necessarily true of its tuple. Weak inextensibility pushes back to the original Y. Apply the weak equivalence at every future point for rigidity. No forbidden function into e is introduced.

Suppose some B_j has a weakly rigid but nonrigid Y. Code it as Y^ with one RELATIONAL argument type ρ. Its extension is nonempty, since an empty weakly rigid relation is bottom. At the free root, the component projections D_ρ(A)→D_ρ(B_k) are jointly surjective, independently of the individual maps. Let E consist of those root ρ-entities whose j-component belongs to Y^'s actual extension and whose other components are fixed bottom entities. Let F at A have root extension E, j-component Y^, and at each other component the haecceity of its fixed bottom entity. These choices are allowed by the free-root domain definition.

F is weakly rigid. Its members transport into the indicated component extensions. Any test necessarily holding of its root members necessarily holds of every member of each component extension, since those extensions are EXACTLY the projections of E. Weak inextensibility of the component relations then puts F below the test. If Tame Rigidity held at A, F would be rigid and its j-transport Y^ rigid, contradiction. Thus Tame Rigidity at A forces it at all B_j.

Conversely let F be weakly rigid at A. Each component F_j is weakly rigid: its weak persistence follows from the persistence of F; for inextensibility, extend a component test to a root test with top at the other components and a root extension containing F's current members. The component hypothesis covers all images of those members, so root weak inextensibility gives the desired entailment at B_j. If all B_j satisfy Tame Rigidity, every F_j is rigid. Together with weak rigidity already true at A this is exactly rigidity of F throughout the generated future cone. Hence A satisfies Tame Rigidity.

This blocks the straightforward strategy of adding a free/coalesced root above the ultralimit fork and declaring the new root tame. A successful separation by a predecessor must change the Henkin restrictions enough to obstruct the weak lifts in this proof. Merely choosing a small individual domain or a non-surjective individual map does not do so: relational haecceity coding bypasses that restriction.

## 24. Countable propositional parameters can define a non-Borel truth set

Section 9's warning about Boolean sigma-algebras can be strengthened to a concrete positive example. No special generalized quantifier, individual parameters, or higher relational parameter is needed. Countable Boolean connectives together with the EXISTING quantifier over propositions suffice in a full S5 model.

Let W=2^(N×N), the space of all binary relations on N, with the usual product topology. Take a full S5 hierarchy with one individual. For m,n in N name the coordinate proposition p_mn={R:m R n}. Define, using countable conjunction,

    c_k := p_kk ∧ ∧_{(m,n)≠(k,k)} ¬p_mn.

This is the singleton proposition whose sole world is the relation {(k,k)}. The c_k are pairwise distinct atoms. For a proposition variable q set b_k(q):=(c_k≤q). Each b_k(q) is bivalent, and, because the proposition domain is the full P(W), the map q↦{k:b_k(q)} ranges over EVERY subset of N. Explicitly q=⋃_{k∈A}c_k realizes A; this is a semantic witness, not an extra named parameter.

Now form the countable infinitary formula

    Φ := ∀q [ (∨_n b_n(q)) →
              ∨_n (b_n(q) ∧ ∧_m(b_m(q)→¬p_mn)) ].

At the evaluation world R, this says exactly that every nonempty subset A of N has an R-minimal member. Thus Φ denotes the set WFrel of well-founded relations on N. All countable conjunctions and disjunctions have well-founded, countable syntax. The only named parameters are the countably many coordinate propositions p_mn; the c_k are displayed abbreviations for terms in those parameters.

WFrel is not Borel. To reduce the standard set WF of well-founded trees on N to it, fix an enumeration of N^{<N} and send a tree T to the relation on its coded nodes in which m R_T n iff both nodes belong to T and node m is a proper extension of node n. Nodes outside T are isolated. Each coordinate of R_T depends on two membership bits of T, so this map is continuous. An infinite branch gives an infinite descending R_T-chain; conversely an infinite descending chain of proper extensions gives an infinite branch. In ZFC, therefore R_T is well-founded iff T is well-founded. The classical non-Borelness of WF is stated, with its normal-form proof, in David Marker, *Descriptive Set Theory*, Fall 2002 notes, Theorem 5.3 and Corollary 5.4, printed p.44 (PDF page 44), https://www.math.uic.edu/~marker/math512/dst.pdf. The translation into the present modal language is the new argument here; no novelty is claimed for the descriptive-set-theoretic theorem.

Every coordinate proposition is clopen, and they generate the Borel sigma-algebra of W. Hence Φ's denotation lies strictly outside that generated sigma-algebra. This directly refutes a countable-parameter sigma-algebra analogue of the finite Boolean normal-form theorem. It leaves atom-fibre invariance intact: the coordinates separate every pair of worlds, so every subset of W is fibre-saturated. It also leaves the Cohen no-definable-selector theorem intact: defining a particular non-Borel set is much weaker than defining a selector on ALL nonempty subsets.

More generally the same coding interprets quantification over subsets of N by proposition quantification, with external natural-number quantifiers expanded as countable conjunctions/disjunctions. Thus every projective truth set on the coordinate real can be represented by a countable infinitary formula using only these proposition parameters (a real parameter, when desired, can be encoded in the countable syntax). This is a lower bound on expressiveness, not a claim that unrestricted higher-type quantification yields only projective sets.

## 25. Exact infinitary modal amalgamation is rectangularity of realized profiles

This extends the finite independence theorem of §5 and distinguishes two meanings of independence once infinitely many parameters are available. Work in a model satisfying the atom-transposition assumptions of §§1–3, with the invariant infinitary syntax of §19. Let (p_i)_{i∈I} and (q_j)_{j∈J} be proposition-parameter families; shared individual parameters and pointwise-rigid first-order relations are harmless. Assume every full profile conjunction for the two index sets is admitted and denotes its Boolean meet. In a full S5 model this assumption is automatic for set-sized conjunctions; countable I,J need only the countable extension.

Write α(a) and β(a) for the p-profile and q-profile of a world atom a. Let A and B be the sets of profiles actually realized by atoms. The following two conditions are equivalent:

1. For every admitted pure definition φ using only the p-family and the allowed rigid parameters, and every such ψ using only the q-family, ◇φ and ◇ψ imply ◇(φ∧ψ).
2. Every pair of individually realized profiles has a joint realization: {(α(a),β(a)):a an atom}=A×B.

Condition 2 is a simpler semantic definition of the required amalgamation property: the set of joint realized profiles is a rectangle. It is not a new assertion that arbitrary propositions are compatible.

For 2⇒1, choose atoms a≤φ and b≤ψ, using Atomicity. Rectangularity gives an atom c with α(c)=α(a) and β(c)=β(b). The infinitary fibre-locality theorem makes φ agree on a,c and ψ agree on b,c. Hence c≤φ∧ψ. For 1⇒2, for each realized profile u∈A form its p-cell C_u=∧_i p_i^{u_i}, and likewise D_v for v∈B. Each is nonzero because the profile is realized. Apply condition 1 to these two admitted formulas; an atom below their nonzero intersection realizes the pair (u,v). No representation of the whole set A or B as an internal object is needed.

For finite I,J, the condition is exactly ordinary Boolean independence of the two generated finite Boolean subalgebras, recovering §5. For infinite families, requiring only compatibility of finite patterns is strictly weaker. A concrete full-S5 T countermodel is

    W=(2^N×2^N) \ {(0^N,0^N)},
    p_i(x,y) iff x_i=1,     q_j(x,y) iff y_j=1.

Every finite assignment to the combined coordinates is realized: if the forbidden pair meets that assignment, change some still-unspecified coordinate. Each whole block separately realizes every binary sequence. Yet the admitted countable formulas ∧_i¬p_i and ∧_j¬q_j are individually possible and jointly impossible. Thus finite-pattern independence does not survive arbitrary countable definitions even under □Functional Choice. The stronger rectangularity condition does survive every admitted invariant definition, including quantified definitions such as §24's non-Borel one.

This gives a precise resource-sensitive version of modal amalgamation. It is an equivalence in the stated model semantics, not a general Craig-interpolation theorem for C and not a claim that every pair of independent parameter blocks supplied by a model is rectangular. The full product W=2^N×2^N supplies the corresponding consistent positive example with infinite profiles.

## 26. The countable-coordinate selector question is independent of ZFC

There is a positive counterpart to §15 in the SAME full-model format. This sharpens the result from a one-sided obstruction to a relative independence statement about definability in full S5 models. Continue to use W=2^N, one individual, all relational domains full relative to the ambient universe, and exactly the coordinate parameters p_n.

**Theorem 22.** In V=L a countable well-founded infinitary pure term using the p_n defines an atom selector. In the Cohen extension of §15 no such term exists. Consequently, relative to Con(ZFC), ZFC does not decide this countable-coordinate definability assertion, although the corresponding full S5 model satisfies □Functional Choice in both cases.

Here is the positive construction. Define the pairwise distinct atoms

    c_n := p_n ∧ ∧_{m≠n}¬p_m.

For q:t the bivalent bits c_n≤q code an arbitrary subset of N, and every such subset is coded by some q because D_t=P(W). If a is a world atom, the bivalent bits a≤p_n give its own real code. A formula of second-order arithmetic, with finitely many real variables and any finite number of real-quantifier alternations, now translates into the modal language: replace quantification over real variables by proposition quantification using the c_n coding; replace natural-number quantifiers by countable conjunctions/disjunctions; replace each membership bit by the appropriate order test. Instantiate arithmetic relations on numerals by their ordinary truth values. The resulting syntax is countable and well-founded. Induction on the arithmetic formula proves correctness, since proposition coding is onto P(N).

In V=L there is a parameter-free projective well-order of the reals (indeed the canonical constructible order is Δ¹₂). This standard fact is given in David Marker, *Descriptive Set Theory*, Example 4.31, printed p.42 (PDF page 42), https://www.math.uic.edu/~marker/math512/dst.pdf. Restricting the usual real code to Cantor space gives such an order on 2^N. Translating its projective definition by the preceding paragraph supplies a countable formula L(a,b), in the p_n alone, that is a rigid strict well-order of the world atoms. Its truth is bivalent because all its bit tests are bivalent and the full S5 domains are constant.

Define

    S(q) := ∃a [At(a) ∧ a≤q ∧
                 ∀b((At(b)∧b≤q)→(a=b∨L(a,b))) ∧ a].

This formula is used under λq; the final occurrence of a is the proposition a itself. For nonzero q the displayed rigid guard singles out its unique L-least atom, so the existential union denotes exactly that atom. At q=bottom it denotes bottom. Hence AS(S). No semantic well-order parameter was named: the constructible well-order is supplied by a countable translation of its projective definition. No arbitrary uncountable family of syntax labels is being smuggled in.

The negative half is Theorem 13, which permits ANY real-coded countable syntax, not merely projective definitions. Both halves concern fullness relative to their respective ambient set-theoretic universes. The syntax can remain the same in an outer extension while the quantified type domains acquire new members, so there is no absoluteness claim for its denotation. This is an independence result for the specified full-model definability question, not a contradiction in □Functional Choice or in the infinitary language.


### End-to-end audit of Theorem 22

The positive proof uses only countably many named proposition parameters, proposition quantification, Boolean/modal operations, and one outer λ-abstraction. It does not quantify over an external family of witnesses. The semantic q_A={e_n:n∈A}, used to verify surjectivity of the real coding, belongs to P(W) in the ambient universe and is never named in the formula. Each c_n={e_n} is instead the explicit countable term displayed above.

For every quantified real variable X in the projective formula, use a fresh proposition variable q_X. Its ONLY appearances after translation are the bits c_k≤q_X. Therefore two proposition values coding the same real give the same translated truth value, even though they can differ on the other worlds. The coding is onto P(N), so induction verifies BOTH existential and universal real quantifiers, despite the larger proposition domain. For the two free real arguments of the well-order, substitute the bits a≤p_k and b≤p_k, with At(a), At(b) supplied by the selector guard. Arithmetic natural-number quantifiers expand over standard numeral assignments; elementary arithmetic relations then become top or bottom. Each branch has the finite quantifier/operation depth of the chosen arithmetic formula, followed by the displayed countable atom definitions, and the entire syntax remains countable and well-founded.

All these bit tests are bivalent in full S5. Boolean operations, countable meets/joins and quantification over the fixed domain preserve bivalence. Thus L(a,b) is a rigid truth value and its strict-order interpretation is independent of the evaluation world. At q≠bottom its least-atom guard is true of exactly one atom a*. Consequently the final existential in S(q) is, pointwise, the union of that single proposition a*: S(q)=a* as a proposition, not merely agreement at the actual world. At q=bottom no atom satisfies a≤q, so S(q)=bottom. This checks the operation-valued conclusion AS(S) without choosing any additional semantic parameter.

The checked primary locator is Marker's Example 4.31 on printed page 42, the 42nd PDF page (zero-based PDF index 41). It states the Δ¹₂ well-order under V=L. The modal translation is supplied here rather than attributed to Marker. The canonical construction may be given without a real parameter; even a presentation with a fixed real parameter causes no difficulty, since its individual bits can be substituted as top/bottom in the countable syntax. This would still add no semantic parameter beyond the p_n.

Finally, all powersets and quantifier domains in each half of the independence statement are those of its ambient universe. A ground-universe selector formula is still legitimate syntax in a forcing extension, but the extra reals and higher-type entities change its interpretation. In the positive universe the translated constructible order covers all world codes; §15 proves that in the specified Cohen universe no real-coded formula, including this one, can define a selector on all ambient subsets of all ambient worlds. The difference is semantic fullness, not a failure of well-founded syntax or a hidden extra constant.
