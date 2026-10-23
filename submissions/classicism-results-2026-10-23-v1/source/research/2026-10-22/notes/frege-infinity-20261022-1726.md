# Frege cardinalities, numerical absoluteness, and Strong Possibility

Research note, 22 October 2026. New arguments by OpenAI Codex (GPT-6), for independent audit. No database or generated files changed; no Lean work or formal-verification claim. These are ordinary proofs in the fixed relational type system of C. Novelty in the literature is not claimed.

## Scope and source boundary

Write BP for C + □Plenitude, equivalently C + □ND + Atomicity in the recorded sense. It is essential that ND is boxed. Write Max for Pure Maximalist Classicism and SP for Strong Possibility (pure), with their reference-theory side conditions unchanged.

The source of the original steps below is `misc`, this note, not a published paper. Recorded ingredients are:

* `topics/classicism/background.md`, Frege definitions of 0, Suc, FiniteCardinality, I* and countability.
* `writeups/c5-and-atomicity-imply-no-pure-contingency.md`, §§1–5: atom-swap automorphisms and conjugation, based on the Goodsell–Yli-Vakkuri theorem and Cian Dorr's sketch of 23 September 2026. The new step here is induction showing that these automorphisms fix **every internal finite cardinality**, then extending the atom-swap argument to formulas with such parameters.
* `writeups/pure-possibility-implies-axiom-of-infinity-t.md`, §1, Lemmas 1–4: number persistence, cases, swap, and exclusivity. Lemma 4 says that finite m,n either are identical or necessarily have no common instance; its actual consequence is enough below.
* `results/strong-possibility-and-infinity-e-incompatible.yaml`: SP implies individual monism, using the consistent maximalist singleton-root model. This is Cian Dorr's recorded argument, not a discovery here.
* `models/coalesced-maximalist-root.yaml` and `models/coalesced-single-individual-root.yaml`: maximalist models with arbitrary root extension components, respectively infinite and singleton individual domains.

All paths above are relative to `/Users/danielkodsi/Downloads/classicism-map/topics/classicism/` except where their displayed prefix already includes that directory.

The proved-only Engine was queried with optional assumptions in the premise set. It confirms BP implies □ND, Atomicity, BF, No Pure Contingency, Countable Boolean Completeness and the recorded Necessity of Arithmetic; BP does not imply either base-type Infinity axiom. It confirms □Functional Choice implies Well-Ordering and Relational Choice. It does not encode the new principles proved below.

## 1. Two elementary Frege lemmas in C

Fix an admitted counting type σ, and put ν=(σt)t and N=FiniteCardinality_σ. No operation with output e is used.

**Lemma 1.1 (extension invariance of finite cardinalities).**

Nn and ∀x(Xx↔Yx) imply nX↔nY.

Proof: instantiate the induction defining N with

    W(n) := ∀X,Y [(∀x (Xx↔Yx)) → (nX↔nY)].

For 0 this follows from its definition as emptiness. Suppose W(n). If X,Y are coextensive and (Suc n)X, choose a with Xa and n(X−a), where X−a is the literal abstract λx.(Xx∧x≠a). Then Ya and X−a,Y−a are coextensive, so W(n) gives n(Y−a), and hence (Suc n)Y. The converse exchanges X,Y. Thus W is successor-closed and N gives W(n). This proof only transfers **truth of application** along coextension; it never identifies coextensive properties or invokes Logical Equivalence under an optional hypothesis.

**Lemma 1.2 (adjoining a fresh point).** If Nn, nX, and ¬Xa, then (Suc n)(X+a), where X+a:=λx.(Xx∨x=a).

Proof: a belongs to X+a and (X+a)−a is coextensive with X. Lemma 1.1 gives n((X+a)−a), the required successor witness.

**Lemma 1.3 (Infinity gives realization).** The Axiom of Infinity at σ implies ∀n(Nn→∃X nX).

Proof: induct with W(n):=Nn∧∃X nX. The zero case uses the empty property. If W(n), choose nX. X cannot be universal: if it were, Lemma 1.1 would give n⊤_σ, contradicting the Infinity axiom. Choose a outside X; Lemma 1.2 realizes Suc n. Numberhood is successor-closed. No choice is involved: this is an induction proving existential statements, not an operation selecting witnesses.

## 2. BP gives numerical-parameter modal absoluteness

**Theorem 2.1.** Let A(n₁,…,n_k) be a pure formula whose free variables are among the displayed variables, each n_i having a Frege cardinality type ν_i=(σ_i t)t. Over BP,

    ∀n₁…n_k [ (∧ᵢ N_{σ_i}(n_i)) → (□A ∨ □¬A) ].

Equivalently, on these parameters A→□A and ¬A→□¬A. A may quantify over arbitrary admitted types and may contain the defined modalities. It need not be an arithmetical formula in the restricted sense of the recorded arithmetic schema. There are no free nonlogical constants or other free parameters.

### Admissible atom-swap machinery

BP supplies C5, BF at all types, and Atomicity at t. At two distinct propositional atoms w,w′, put u=¬(w∨w′), H:=Atom(w)∧Atom(w′)∧w≠w′, and

    F(p) := (u∧p) ∨ (w∧(w′≤p)) ∨ (w′∧(w≤p)).

H is rigid by ND and BF, because atomhood and the Boolean order are built from identities, connectives and quantifiers. The recorded proof establishes under H that F is an involutive Boolean automorphism, fixes all identity propositions, commutes with quantifiers, and exchanges the two atoms: w≤F(p) iff w′≤p.

We make the relational-type bookkeeping explicit, repairing an inadmissible piece of notation in that write-up. Define transformations T_τ on expressions recursively. **T_e(a):=a is metalinguistic substitution only; it is never an object-language term of type ee.** Define T_t(p):=F(p), and for an admitted arrow type στ define

    T_{στ}(X) := λy^σ. T_τ( X(T_σ(y)) ).

When σ=e, the argument here is just y. For every relational τ, a term λx^τ.T_τ(x) of type ττ is admitted. The recorded conjugation proof, with the identity substitution at e, gives under H:

1. T_τ(T_τ(x))=x;
2. T_τ(Xa)=(T_{στ}(X))(T_σ(a));
3. for every pure term B with free variables among z̄,
   T(B(z̄))=B(T(z̄)).

For (3), logical constants are fixed because F commutes with their defining Boolean/quantifier/equality operations, application uses (2), and abstraction uses the involution. Equality of abstractions obtained under H is licensed by the rigidity of H, necessitation of the discharged implication, K and Modalized Functionality. No optional hypothesis is inserted into the theoremhood side condition of Logical Equivalence.

### The new induction

Fix σ and its cardinality type ν. The closed pure terms 0_σ and Suc_σ are fixed by T. Therefore, under H,

    T_ν(0_σ)=0_σ,
    T_ν(Suc_σ n)=Suc_σ(T_ν n).

Instantiate the definition of N_σ at the admitted property

    W := λn^ν. T_ν(n)=n.

The first equality gives W0; the second gives Wn→W(Suc n). Hence **every** N_σ-number n is fixed by T_ν. This includes numbers not denoted by any closed numeral and works independently at each counting type σ_i. It uses the impredicative induction already in the definition of N, not an external standardness assumption.

Now suppose the displayed numbers satisfy their N predicates. Equivariance for the pure formula A and the preceding identities give F(A)=A under H. If A were true but not necessary, Atomicity supplies an atom w below A (A is nonbottom because true) and an atom w′ below ¬A (¬A is nonbottom because A is not top). They are distinct. The atom-swap equation gives w′≤A from w≤A and F(A)=A, contrary to w′≤¬A. Thus A→□A. Apply the same argument to ¬A for the other direction. This proves the theorem.

**Modal bookkeeping.** The theorem only uses the unboxed Atomicity_t and the boxed ND instances supplied by BP; it does not necessitate either optional premise inside the argument. Its fully closed schema is also necessary under BP, by applying the discharged theorem under a box and using 4 on the finitely many □Plenitude instances needed to derive its premises. This is a schema in fixed metalinguistic types, not a quantification over types.

## 3. Numerical extensionality and null-cardinality collapse

Define the following new candidate principles, one instance per σ:

    NE_σ := ∀m,n [Nm∧Nn∧∀X^{σt}(mX↔nX) → m=n].

    NC_σ := ∀n [Nn∧∀X^{σt}¬nX → n=⊥_ν].

**Corollary 3.1. BP proves NE_σ and NC_σ for every σ.**

For NE, Theorem 2.1 makes the pure coextension formula ∀X(mX↔nX) necessary when true. Intensionality / Modalized Extensionality in C then identifies m and n. For NC use the formula ∀X¬nX and identify n with the empty relation ⊥_ν. The fact that ⊥_ν need not itself be a finite cardinality is immaterial: it is a closed pure term, so it is fixed by the atom swap.

These are restricted extensionality results about numerical cardinalities, not general Extensionality. BP is compatible with nontrivial modal distinctions and does not identify arbitrary coextensive relations.

**Corollary 3.2. BP+I*_σ proves every finite cardinality is instantiated.**

C proves Suc_σ(⊥_ν)=⊥_ν by Logical Equivalence applied to the theorem that an existential conjunction with false is false. Under I*, induction proves n≠Suc n for every N-number n: the zero case is zero-not-successor; the successor case follows by successor injectivity. If a finite n has empty extension, NC gives n=⊥_ν, hence n=Suc n, contradiction.

This is a new route from the arithmetic assumption I* to cardinal realization under BP. It does not silently identify I* with the Axiom of Infinity in arbitrary C-models.

## 4. Strong Possibility's numerical pathology

**Theorem 4.1. SP forces infinitely many pairwise distinct finite cardinalities of individuals with empty current extensions. In particular SP refutes NE_e and NC_e.**

The recorded argument gives E₁:=∀x^e y^e(x=y) from SP. SP also implies Max. For every pair of distinct standard integers i,j, the closed pure identity between their e-numerals is not a theorem of C: the full extensional Henkin model with at least max(i,j) individuals gives the two numerals different extensions. Max therefore makes those numerals distinct. This uses the fixed reference theory C in the Max side condition.

At an E₁-world no property of individuals can have two or more instances. Unfolding the numeral definitions shows that each standard numeral 2_e,3_e,… has empty current extension. Hence 2_e and 3_e are coextensive but distinct, refuting NE_e. Also 2_e≠⊥_ν by Max, since a two-individual full extensional model gives 2_e an instance, so NC_e fails already at 2_e.

There is an exact internal statement. Under E₁, for every finite cardinality n, if n has an instance then n=0_e or n=1_e. Given nX, either X is empty, so 0_eX and recorded exclusivity gives n=0_e; or X has a member a, and monism makes X−a empty, so 1_eX and exclusivity gives n=1_e. Conversely 0_e has the empty property as instance and 1_e has the universal property as instance. Thus under SP the finite cardinalities have exactly **three current coextension classes**: zero, one, and the empty-extension class. The last contains infinitely many pairwise distinct entities. This does not assert that a quotient entity representing these three classes exists.

**Independence from ordinary Max.** The standard maximalist coalesced root with infinitely many individuals satisfies all NE_σ and NC_σ locally. At that root every type has infinitely many entities, the free root component isolates exactly the standard numeral values as N_σ, and every standard numeral has a finite-set extension as an instance. Distinct numeral values therefore have different current extensions; none has empty extension. Conversely the recorded singleton maximalist root refutes NE_e and NC_e by the preceding monism argument. These are new verifications of those particular model constructions, not automatic transfers of flags between variants. No statement about their boxed forms is asserted.

## 5. A numerical injection into individuals from □Functional Choice and Infinity

**Theorem 5.1. C+□Functional Choice+the Axiom of Infinity at e proves that N_e has a relational injection into e.**

Here an injection is a graph J^{ν_e e t} that is total on N_e, single-valued there, and left-unique there. No ν_e→e or e→e operation is formed.

The proved-only Engine gives □Functional Choice→Well-Ordering and Relational Choice. The recorded route is □FC→□RelChoice and □Plenitude→□Actuality→□Transversal, hence □Transversal Choice→□Well-Ordering. Fix the resulting local well-order ≤ of e. Let P_a:=λx.(x<a), the strict initial segment at a.

Claim: ∀n(N_en→∃a.nP_a). Instantiate Frege induction with W(n):=N_en∧∃a.nP_a. Zero is witnessed by the least individual, whose strict predecessor property is empty. For the step take a with nP_a. The property L_a:=λx.(x≤a) has cardinality Suc n, by Lemma 1.2 and Lemma 1.1, since it is coextensive with P_a+a. It is not universal: otherwise Lemma 1.1 gives (Suc n)⊤_e, contrary to the Infinity axiom. The complement of L_a is therefore instantiated. Let b be its least member. The well-order axioms imply P_b is coextensive with L_a: everything ≤a is <b; any x<b outside L_a would precede b in the complement. Lemma 1.1 therefore gives (Suc n)P_b. This closes the induction.

Put J₀(n,a):=N_en∧nP_a. This relation is total on N_e. It is left-unique: if J₀(n,a) and J₀(m,a), the finite cardinalities n,m share P_a as an instance, so recorded exclusivity gives n=m. Choose any individual a₀ and pad J₀ off the numbers by relating every nonnumber only to a₀. The padded relation is total on all ν_e. Relational Choice supplies a total single-valued subrelation; restricting its input to N_e yields the claimed injection.

All uses of well-ordering and choice are local. The proof invokes no theoremhood-only equivalence rule on an optional premise, and the Frege induction property explicitly carries N_n so that the successor step may use finite-cardinality extension invariance and the Infinity axiom.

**Application for the parent world-profile lane.** If UCP_e entails that no relational injection Atom_t→e exists, then □FC+Infinity_e+UCP_e refutes Ctbl_{e,t}(Atom_t). Indeed the given countability relation gives each atom at least one number code and gives distinct atoms disjoint code fibers. Compose it with Theorem 5.1's injection N_e→e. The result is total and left-unique on atoms; Relational Choice selects one output per atom if the forbidden-injection formulation also requires right-uniqueness. Thus it contradicts the parent lane's UCP cardinal bound. The UCP bound itself is not reproved in this note.

## 6. Further candidate: local Dedekind principles

For completeness, a natural all-type strengthening considered before the SP pivot is: every property X with no finite cardinality admits a total single-valued injective but nonsurjective self-relation R^{σσt} on its instances. It is well-typed even at σ=e.

In ZFC, the usual maximalist coalesced root with free root extension components satisfies this schema locally: N_σ is precisely the standard numerals at that root, every infinite extension has a countable subset, shift that subset and fix its complement, and realize the graph in a root component. Full S5 models satisfy its boxed form. A separation from BP can be sought using a full extensional model constructed **inside a model of choiceless set theory with an infinite Dedekind-finite set**; the individual instance then fails although BP holds. This last separation is a relative-consistency route, not a self-contained set-theoretic construction in this note; do not promote it without documenting the metatheory and its source. It is not needed for any theorem above.

## Audit status

Sections 1–5 are new ordinary arguments built on the specifically identified recorded lemmas; they are ready for independent mathematical audit. The model checks in §4 use external standardness only where the free root-component construction explicitly supplies it. Theorem 2.1 uses internal impredicative induction and does **not** assume standardness. No general consistency or inconsistency result for Strong Possibility has been obtained: its consistency remains open in the supplied records. No literature novelty or Lean verification is claimed.

## 7. Simpler equivalent formulations of Frege infinity

This section responds to the request for more perspicuous equivalent definitions. The original records are preserved.

**Lemma 7.1 (finite equal-cardinality inclusions).** In C, if Nn, nX, nY, and ∀x(Xx→Yx), then X and Y are coextensive.

Proof: induct on n with the property consisting of Nn together with the displayed universally quantified claim. At zero, both X,Y are empty. At the successor of m, choose a∈X with m(X−a), and b∈Y with m(Y−b). Since X⊆Y, a∈Y. If a=b we already have m(Y−a); if a≠b, recorded Swap (Lemma 3 of the cited maximalist-infinity write-up), applied inside Y to a,b, gives m(Y−a). Now X−a⊆Y−a, so the induction hypothesis makes these two properties coextensive. Both X,Y contain a, so they too are coextensive. This is again a statement about extensions, without identifying coextensive relations.

**Corollary 7.2 (finite upper bound).** If Nn, nY and X⊆Y, then ¬(Suc n)X.

For a successor witness a would satisfy a∈X⊆Y and n(X−a). Lemma 7.1, applied to X−a⊆Y, makes X−a coextensive with Y, contrary to their different memberships of a.

**Theorem 7.3. In C the Axiom of Infinity at σ is equivalent to finite-cardinality realization:**

    ¬∃n [Nn ∧ n⊤_σ]  ↔  ∀n [Nn → ∃X^{σt} nX].

The forward implication is Lemma 1.3. Conversely, if Nn and n⊤_σ, realization at the finite cardinality Suc n gives an X with (Suc n)X, contradicting Corollary 7.2 with Y universal.

It is also equivalent in C to the elementary formulation “every finite collection leaves an outsider”:

    ∀X^{σt} [(∃n (Nn∧nX)) → ∃a^σ ¬Xa].

The forward direction uses Lemma 1.1 if a finite X were universal; the converse instantiates X with the universal property. This is often the clearest informal reading, while realization is useful for proofs.

**Lemma 7.4. In C, realization implies I*_σ.** Zero-not-successor is already a theorem. For injectivity, let Nm,Nn and Suc m=Suc n. Realize Suc m at X. Unfold its two successor assertions, getting a,b with m(X−a), n(X−b), Xa and Xb. If a=b these are a common instance of m,n; otherwise Swap turns n(X−b) into n(X−a). Recorded exclusivity then gives m=n.

**Theorem 7.5. Over BP the following are equivalent, at each fixed σ:**

1. the Axiom of Infinity at σ;
2. every finite cardinality at σ is instantiated;
3. successor is injective on the finite cardinalities at σ;
4. I*_σ;
5. I_σ=◇I*_σ.

Theorem 7.3 and Lemma 7.4 give (1)↔(2)→(4). The first conjunct of I* is a C-theorem, giving (3)↔(4). Corollary 3.2 gives (4)→(2) using BP. Finally (4)→(5) is T, while (5)→(4) is Goodsell's recorded C-theorem, `writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`, Lemma 5 (that lemma does not use Countable Boolean Completeness). These equivalences therefore offer a substantially simpler infinity axiom **when BP is explicitly held fixed**: “the Frege successor operation is injective on numbers.”

The BP assumption cannot be dropped from (4)→(1). In the maximalist singleton-root model, Max gives I_e by the C-consistency of I*_e in the full infinite extensional model, hence I*_e by the recorded theorem, while the actual individual domain is a singleton. This is an existing model, not a new consistency assumption.

## 8. Simpler equivalent formulations of the countability predicate

Fix counting type σ, number type ν=(σt)t and N=N_σ. Let X^{τt}; the recorded applications use relational τ, but the graph formulations here are well-typed at τ=e too. The record defines Ctbl_{σ,τ}(X) by a relation R^{τνt} such that, for X-members y,z,

    (∃n∈N [Ryn∧Rzn]) ↔ y=z.

This does **not** require R to assign only one number to each y. It gives every y at least one number-code and gives distinct y disjoint code fibers. Reading it immediately as a single-valued injection suppresses a step. The following equivalences make that step explicit.

**Theorem 8.1 (C, no extra principles).** Ctbl(X) says exactly that X is the range of a partial single-valued relation on N. Equivalently, either X is empty or X is the range of a total single-valued relation on N.

For the partial form, reverse R and restrict both ends: S(n,y):=Nn∧Xy∧Ryn. Code-fiber disjointness makes S single-valued in n, and the y=z instances give surjectivity onto X. Conversely reverse any such partial enumeration to obtain R. If X is nonempty choose one y₀ with Xy₀ and fill each missing numeric input with y₀. This yields a total single-valued relation on N with exactly range X. The choice of a single witness y₀ is ordinary existential elimination, not an axiom of choice. The converse forgets totality. Empty X requires its own disjunct because N contains zero.

**Theorem 8.2 (Plenitude).** For relational τ, C+Plenitude proves

    Ctbl_{σ,τ}(X)
       ↔ [ ¬∃y Xy  ∨  ∃f^{ντ} ∀y (Xy ↔ ∃n∈N [fn=y]) ].

Thus the especially perspicuous “empty, or the range of a numerical sequence” is an exact equivalent under BP. To obtain f, pad the total enumeration from Theorem 8.1 off N by the same y₀, so it is total and single-valued on all ν; Plenitude represents it by an operation. Conversely use Ryn:=(fn=y). No Choice principle is used, and no ν→e operation is asserted; for individual outputs retain the relational form of Theorem 8.1.

**Theorem 8.3 (I*_σ).** Under I*_σ, Ctbl_{σ,τ}(X) is equivalent to the existence of a total single-valued injective **graph** from X into N. No Choice or Plenitude is required.

I* together with the definition of N supplies the usual Peano successor laws and induction for every definable property of numbers, including formulas with R,y as parameters. Define the usual natural order by n≤m iff ∃k∈N Sum(n,k,m). The least-number principle therefore holds for every instantiated property of N. For each y∈X its nonempty code fiber {n∈N:Ryn} has a unique least member. The abstract

    R_min(y,n) := Xy ∧ Nn ∧ Ryn
                  ∧ ∀m∈N (Rym→n≤m)

is total and single-valued on X and is injective because distinct X-members had disjoint original code fibers. Conversely an injective graph itself satisfies the recorded Ctbl formula. Plenitude, if also assumed, represents the graph as an operation of type τν after padding off X by zero; the output ν is always relational, even when τ=e.

This covers all Max models at every fixed counting type: I*_σ is C-consistent (use an appropriate full model with infinite σ-domain), so Max supplies ◇I*_σ, and the recorded I→I* theorem supplies I*_σ. It also covers BP+Infinity_σ by Theorem 7.5.

**A useful warning about finite counting types.** Without I*, the internally defined numbers may be a finite truncated chain containing an overflow cardinality. In the one-individual full extensional model, N_e consists of exactly 0_e, 1_e and the empty cardinality ⊥_ν; Suc(⊥_ν)=⊥_ν. Consequently “countable relative to e” there means admitting a coding by a three-element set, not ordinary countability by an infinite ω. This is why one should keep the subscript σ and its infinitude assumptions visible when presenting the simpler forms. The model calculation is direct from the full interpretation, not a claim about all Henkin models with one individual.

## 9. Further simplification: the extra numerical laws under I*

**Theorem 9.1. Over C+I*_σ, the following are equivalent:** Infinity_σ; realization of every N_σ-number; NE_σ; NC_σ.

Infinity↔realization is Theorem 7.3. Realization implies NE: if m,n are coextensive numerical cardinalities, realize m at X; then nX too, and exclusivity gives m=n. Realization implies NC vacuously. Conversely, if a numerical n has empty extension, Suc n also has empty extension by its definition. NE then identifies n and Suc n, contradicting the no-fixedpoint induction under I* from §3. NC yields the same contradiction from n=⊥_ν and Suc(⊥_ν)=⊥_ν.

In particular, **under Max, NE_e and NC_e are equivalent to the already-recorded actual individual Infinity axiom**. They should not be presented as unrelated new independent axes over Max. Their significance for BP is different: BP proves NE and NC even in finite domains, where successor may have the unique empty absorbing overflow value.

**Theorem 9.2. Max implies quantified Infinity at every relational type σ, not just at t.**

The recorded proof of Max→Infinity_t actually constructs a total, left-unique, nonsurjective relation on the whole propositional domain. At every relational type σ=σ₁…σ_k t, the pure operation c(p):=λx₁…x_k.p injects t into σ: equality of the outputs implies p=q by applying to arbitrary arguments, available by Existence. For k=0 use identity. Transfer the relation along c to its image and fix every element outside the image. Explicitly, if R is the relation on t and S(x):=∃p(x=c(p)), use

    R′(x,y) := [∃p,q (x=c(p)∧y=c(q)∧Rpq)] ∨ [¬Sx∧y=x].

The same left-uniqueness argument as in the recorded proof shows R′ is total, left-unique and misses c(p₀), where p₀ was omitted by R. Recorded Dedekind Lemma 5 then yields quantified Infinity_σ. This transfer uses no Choice. Thus over Max, NE_σ and NC_σ already follow at every relational counting type; only their individual-type instance supplies the additional actual-infinity restriction.

## 10. Choice-free improvement to the numerical embedding and world bound

**Theorem 10.1. C+Infinity_σ+Well-Ordering at σ proves a relational injection N_σ→σ, without Choice.**

Use J(n,a):=Nn∧nP_a from Theorem 5.1. The existence proof there did not use Choice. It is also already single-valued. If nP_a and nP_b and a<b, then P_a⊆P_b, so Lemma 7.1 makes them coextensive; yet a belongs to P_b and not P_a. The case b<a is symmetric. Totality of the well-order therefore forces a=b. Left-uniqueness follows from recorded exclusivity as before. The last selection step of Theorem 5.1 was unnecessary once Lemma 7.1 was available.

**Theorem 10.2. C+Infinity_σ+Ctbl_{σ,σ}(⊤_σ) proves a relational injection N_σ→σ.**

Infinity gives I* by §7. The least-code construction of §8 gives an injective graph from σ into N_σ. Pull back the usual numerical order to σ. This is a well-order on σ: any instantiated property of σ yields, by existential comprehension along its graph, an instantiated property of N; its least number has a corresponding member, which is least in the pullback order. Apply Theorem 10.1. No Choice or Plenitude is used.

For clarity, the least-number principle here is available for arbitrary definable properties, not just arithmetic formulas. N's impredicative induction permits parameters and quantifiers of all admitted types. Under I*, the usual order laws hold. If an instantiated property P had no least number, induct on n with “no m≤n satisfies P”: at zero, P0 would be least; at Suc n, any new P-witness would be least because all smaller numbers were excluded. Thus P would be empty, contradiction.

### Conditional application to the parent UCP proof, with nonunique profiles

The parent lane's UCP_e is the existence of an individual-to-proposition profile assignment realizing every rigid individual property as a possible profile. A profile proposition q_X need only be nonzero; **it need not be an atom**. The following avoids silently assuming unique worlds.

Assume BP, Infinity_e, UCP_e and Ctbl_{e,t}(Atom_t). Let R(w,n) be the atom-number coding relation. For each individual a let q_a be the nonzero profile proposition for the rigid singleton {a}. Distinct individuals have disjoint q_a: no world can realize both singleton patterns. Define

    C(a,n) := ∃w [Atom_t(w) ∧ w≤q_a ∧ R(w,n)],

with the numerical domain restricted to N_e as in Ctbl. Each a has a code: Atomicity supplies an atom below q_a, and that atom has a number-code. If a,b share a code, the atom-code property makes the two witnessing atoms identical. A nonzero atom cannot lie below two disjoint q_a,q_b, so a=b. Thus C is a Ctbl_{e,e} code for the entire individual domain. Theorem 10.2 yields an injection N_e→e. Composing the original atom-number relation with this graph gives disjoint nonempty individual-code fibers for atoms. If a single-valued atom→e graph is required, first replace R by its least-code graph (§8), then compose. This needs I*_e, already supplied by Infinity_e, and no Choice.

Consequently, conditional on the parent lane's independently proved UCP bound forbidding an injection Atom_t→e:

    BP + Infinity_e + UCP_e  →  ¬Ctbl_{e,t}(Atom_t).

This improves the §5 application by removing □Functional Choice altogether. It also corrects the tempting but unjustified shortcut from a profile q_a directly to a chosen atom below it.

### An equivalent chain-condition formulation

At a relational Boolean-algebra type τ, write CCC_{σ,τ} for: every property X^{τt} whose members are nonbottom and pairwise disjoint is Ctbl_{σ,τ}. “Pairwise disjoint” means distinct x,y in X have x∧y=⊥_τ.

**Theorem 10.3. Under Atomicity_τ, CCC_{σ,τ} is equivalent in C to Ctbl_{σ,τ}(Atom_τ).**

If the atoms are countable by R(w,n), code a member x of a disjoint nonbottom family X by n whenever some atom w≤x has R(w,n). Atomicity gives every x a code. A shared code identifies the witnessing atoms, and a nonzero atom cannot lie below two distinct disjoint members of X. This is the recorded Ctbl condition. Conversely the atoms themselves are nonbottom and pairwise disjoint (the usual Boolean atom lemma in C), so CCC applied to their property gives countable atoms. No choice of one atom below each x is made.

Thus the preceding UCP consequence also refutes the internal countable chain condition at t, counting by e. The Infinity_e hypothesis ensures that “countable” has a genuine Peano index rather than a finite overflow index.

## 11. General invariant parameters, beyond numerical ones

**Theorem 11.1.** Theorem 2.1 remains true with arbitrary individual parameters among the free variables. Atom-swap conjugation fixes these by its very definition T_e(a):=a, which is a metalinguistic identity substitution. Hence a pure formula with only individual and numerical parameters satisfies A→□A and ¬A→□¬A under BP.

More generally, let μ be a relational type, let c₁,…,c_r be closed pure terms of type μ, and let f_i be closed pure constructors μ^{k_i}→μ (finitely many, with finite arities). Define G_μ as the least property containing the c_j and closed under the f_i, using the same impredicative universal-property pattern as FiniteCardinality. Then every G_μ-element is fixed by every atom-swap conjugation: instantiate its defining induction with W(x):=(T_μx=x), using that the constructors and constants are fixed pure terms. Theorem 2.1 therefore holds with any finite list of such generated parameters too.

As a consequence, two G_μ-elements that are coextensive as relations are identical under BP: their coextension formula is pure with invariant parameters, hence necessary, and Intensionality applies. This is a general extensionality theorem for internally generated logical data. It does not claim general Extensionality for arbitrary relation parameters, and no constructor with output e is introduced.

## 12. Numerical Collection: one canonical supremum rather than countable completeness

This section isolates an assumption in Goodsell's recorded proof, rather than attributing the isolation to the source. The underlying proof is Theorem 9 and especially Lemma 8 of *Arithmetic is Necessary*, draft of 5 June 2024, transcribed in `topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`. The equivalences below are new arguments in the present scratch work.

Fix σ and ν=νσ, and define

    Hσ(X) := ∃n [Nσ(n) ∧ X={n}],       X:νt,
    NCOLLσ := Hσ has a least upper bound in the Boolean order on νt,
    BF_Nσ := ∀X^{νt}[(∀n(Nσn→□Xn))→□∀n(Nσn→Xn)].

Here `{n}:=λm.n=m` and `Y≤X` is necessary inclusion, not merely actual inclusion. We call NCOLL **Numerical Collection**, reserving NC for the distinct Numerical Null Collapse condition in §3.

**Theorem 12.1 (C).** The following are equivalent: NCOLLσ; Nσ is the least upper bound of Hσ; BF_Nσ; Nσ is locally weakly inextensible. Any least upper bound of Hσ is Nσ itself.

For any n and X, `{n}≤X` iff □Xn. Left to right uses the necessary self-identity of n; right to left uses boxed identity substitution. Since numberhood is persistent in C, N is an upper bound of H.

Suppose B is a least upper bound. Then every actual number necessarily has B. Since successor of an actual number is an actual number, every actual number necessarily has the property λn.B(Suc n). That property is another upper bound, so leastness yields □∀n(Bn→B(Suc n)). Also □B0. Necessitate the C theorem giving N-induction, instantiate it with B inside the box, and obtain N≤B. Conversely B≤N since N is an upper bound. Antisymmetry gives B=N. This is exactly the argument of recorded Lemma 8, with the sole CBC invocation replaced by NCOLL.

If N is the least upper bound, an X with ∀n∈N □Xn is an upper bound and hence N≤X; this is BF_N. Conversely BF_N makes N less than every upper bound, while persistence already makes N an upper bound. Finally the displayed BF_N is precisely the defining local weak-inextensibility condition for N. No optional premise has been necessitated. This does not silently identify the local condition with a boxed rigidity principle.

**Arithmetic consequence.** Goodsell's formula induction (recorded Theorem 9) now gives from NCOLLσ, for every arithmetical formula A and every numerical tuple of its free parameters,

    □(Iσ→A) ∨ □(Iσ→¬A).

No other use of CBC occurs. Thus the recorded incompatibility of Maximalism with Necessity of Arithmetic applies already to this one canonical supremum at the relevant arithmetic counting type, in particular σ=e. The Gödel/incompleteness side of that recorded argument must retain its original consistency and arithmetic interpretation conditions; this paragraph does not claim a fresh independent incompleteness proof.

One must not call the members of H Boolean atoms or assume they are pairwise Boolean-disjoint. Under Maximalism, two currently distinct Frege numbers may become identical where I* fails. The theorem concerns the canonical family of numerical haecceities and its necessary-inclusion supremum, not an asserted disjoint partition.

## 13. Counting-base independence once both Frege domains are Peano

The following gives a simpler way to read type-indexed countability under explicit arithmetic assumptions. It is not a claim that the index is harmless when a Frege domain has overflow collapse.

Fix σ,ρ and assume I*σ and I*ρ. Let J(n,m), with n:νσ and m:νρ, be the intersection of all relations Q that contain (0σ,0ρ) and are closed under simultaneous successor:

    J(n,m) := ∀Q^{νσνρt}[(Q(0σ,0ρ) ∧
                ∀u,v(Q(u,v)→Q(Sucσu,Sucρv))) → Q(n,m)].

All types are admitted relational types. J is a graph; no map with individual output is used. Its definition supplies J(0σ,0ρ), closure under the two successors, and induction over J for arbitrary properties of ordered pairs expressed as relations.

**Theorem 13.1 (C + I*σ + I*ρ).** J is the unique bijective relational Peano isomorphism between Nσ and Nρ.

First J(n,m) implies Nσn∧Nρm, because this conjunction is one of the inductive relations in the definition. J has the decomposition property

    J(n,m) → [(n=0σ ∧ m=0ρ) ∨
      ∃u,v(J(u,v) ∧ n=Sucσu ∧ m=Sucρv)].

Indeed the right side, as a property of n,m, contains the base pair and is successor-closed: if it holds for (n,m), then J(n,m) follows in either disjunct, and this pair witnesses the successor disjunct for (Sucσn,Sucρm). Apply J-induction.

J is total on Nσ: 0σ has mate 0ρ, and a mate m for n yields mate Sucρm for Sucσn. This is Nσ-induction with the property ∃m J(n,m). The symmetric argument gives totality on Nρ. To prove functionality, induct on n in Nσ with the property that n has at most one mate. If n=0σ, decomposition and zero-not-successor force every mate to equal 0ρ. If n=Sucσu, decomposition forces any two mates to be Sucρv and Sucρv′ with J(u,v), J(u,v′): the corresponding first-coordinate predecessors equal u by successor injectivity. The induction hypothesis gives v=v′ and hence the mates coincide. The symmetric argument proves injectivity. Thus J is a bijection.

For uniqueness, let K be any total functional graph between these domains that sends zero to zero and commutes with successors. Nσ-induction shows that the unique J-mate and unique K-mate agree at zero and at every successor. Hence K and J have the same graph. This is uniqueness of the graph as an actual extension; no unjustified identity of merely coextensive relation objects is asserted. If the graph is required to be an object with specified intensity, existence and uniqueness of that stronger object need an appropriate extensionality or rigidity hypothesis.

**Corollary 13.2 (C + I*σ + I*ρ).** For every admitted τ and X^{τt},

    Ctbl_{σ,τ}(X) ↔ Ctbl_{ρ,τ}(X).

If R(x,n) is a σ-code, define S(x,m):=∃n(J(n,m)∧R(x,n)). Every x∈X has an S-code by totality of J. A code m shared by x,y identifies their J-preimages by injectivity, so the original R condition gives x=y. Conversely any x=y has a shared S-code by nonempty fibers. The reverse direction uses the converse graph. Neither choice nor Plenitude is needed; multiple-code fibers are preserved correctly.

Consequently the σ-counted and ρ-counted versions of CBC, CCC, and countability of any specified property are equivalent whenever both I* hypotheses hold. Boxed versions follow only under boxed arithmetic hypotheses or by necessitating the corresponding C conditional theorem and applying modal reasoning; an optional unboxed hypothesis is never automatically boxed. In particular Maximalism, which supplies I* at each type by its possible-arithmetic consequence, makes its different Frege counting indexes interchangeable, even when actual individual infinity fails.

## 14. Numerical Collection is strictly weaker than CBC and boxed Plenitude

This section adds a new verification to existing model constructions; it makes no database edit and does not attribute the new NCOLL verdict to the original source.

**Semantic criterion.** Consider a sound action/Henkin model of C whose transport preserves closed pure terms. Suppose that at every object reachable from the evaluation point, Nσ consists exactly of the values of the externally standard numeral terms 0σ,Sucσ0σ,… . Then BF_Nσ holds throughout that reachable part, hence so does NCOLLσ by Theorem 12.1.

At an object U, suppose X necessarily holds of every current number. At an arrow h:U→V and any number m at V, choose an external natural k with m equal to the V-value of the kth numeral. The U-value n of that same numeral is a current number, and transport takes n to m because the numeral is a closed pure term. The premise □Xn at U therefore makes X true of m at h. This is exactly the semantic quantifier clause needed for □∀m∈N X m. The argument repeats at every reachable U. It neither assumes an object-language standardness axiom nor replaces a Henkin number domain by ω without checking its standard-numeral description.

**Why the criterion applies in the named finite-support models.** The recorded models are ideally full and extensionally full at each object. Thus the external set of standard numeral values is admitted as the actual extension of a property W. It contains zero and is closed under successor. The impredicative definition of N therefore makes every N-element belong to W. Conversely each standard numeral belongs to N by a finite metatheoretic iteration of the C closure theorem. This establishes the criterion at every object and every counting type, including cases where different standard numerals have equal values. The models are not full constant-domain S5 models; their finite-support admissibility restriction remains in force. Only the explicit local extensional-fullness fact is used here.

Two precise separations follow.

1. **Finite-support action model: permutations of N.** See `topics/classicism/models/finite-support-permutations.yaml`, its group `finite-support-one-object`, and Classicism Appendix D, Definitions D.1–D.3 and Proposition D.5(1), pp. 73–76. The group explicitly verifies extensionally full domains at its sole object. Thus every NCOLLσ holds necessarily. The recorded countable family A_m of propositions “the permutation swaps 0 and m” has no least upper bound: its least cover pinned by {0,…,N} strictly shrinks when that finite pinning set grows. The group argument turns this into a CBC failure using the admitted numerical coding relation. The propositional algebra is atomless, also recorded, so Plenitude fails: Plenitude entails Actuality, whose strongest true proposition is a Boolean atom, contradicting atomlessness. Thus NCOLL, even its all-type boxed schema, does not entail CBC or Plenitude.

2. **Finite-support action model: N and singleton, all maps.** See `topics/classicism/models/finite-support-two-object-all-maps.yaml`; construction source Classicism Appendix D, p. 79, paragraph “One particularly interesting result.” Both objects are extensionally full. The model record explicitly checks standard numerals at both objects, including why their cardinality entities stay distinct at the singleton object through arrows back to N. Hence all boxed NCOLL instances hold. CBC fails for the recorded countable family of propositions whose first change occurs at an even position. General □BF fails, since new entities appear along arrows from the singleton object. This gives the sharper separation: even boxed numerical BF at every counting type does not imply boxed general BF.

CBC implies NCOLLσ through the one countable family Hσ; □Plenitude implies all NCOLLσ through the recorded arithmetic/numerical absoluteness argument (or its stronger BF and rigid-comprehension consequences). Consequently the examples establish strict weakness, not merely missing recorded arrows. No consistency conclusion for Strong Possibility follows: these models do not satisfy Maximalism.

### 14.1 Exact possible-witness formulation and all-type Maximalist failure

A more perspicuous equivalent of NCOLLσ is

    ∀X^{νσt}[◇∃n(Nσn∧Xn) → ∃n(Nσn∧◇Xn)].             (Numerical Witness)

That is: every possibly instantiated numerical property could be instantiated by some current number. This is exactly the classical/modal dual of BF_Nσ (substitute ¬X). The reverse implication is already a theorem of C: current numberhood persists, so if a current number could have X, possibly a number has X. Hence NCOLL equivalently says that numerical existential quantification commutes with possibility, or numerical universal quantification commutes with necessity. These formulations do not quantify over an externally specified ω and do not require an object-level individual-valued operation.

The Maximalist obstruction applies at **each fixed counting type σ**. For every admitted σ, a full S5 model with both an infinite individual domain D and infinitely many worlds W makes that type infinite and satisfies I*σ. Its proposition domain is P(W), and constant-valued relations inject propositions into every relational type; fullness makes each Nσ exactly the standard numeral values. An extensional one-world model with infinite individuals would not suffice at σ=t, since it has only two propositions. Thus C is consistent with Iσ. The translated arithmetic theory {A : C proves Iσ→A} is recursively enumerable, consistent, and extends the Peano axioms by the same source Lemma 1. The fixed-type version of the recorded Goodsell Theorem 11 therefore gives an arithmetical A with both Iσ∧A and Iσ∧¬A C-consistent. Maximalism makes both possible, whereas NCOLLσ implies their conditional arithmetic determinacy by Theorem 12.1 and Goodsell Theorem 9. Consequently Maximalism refutes NCOLLσ at each fixed σ, not merely at some unspecified schema instance.

Equivalently Maximalism proves, for each σ,

    ∃X^{νσt}[◇∃n(Nσn∧Xn) ∧ ∀n(Nσn→□¬Xn)].

Some property possibly belongs to a number although no current number could have it. This is a precise formal criticism, and must not be weakened to the vague claim that “numbers can vary.” It also does not say that an actual number can cease being a number: C proves the opposite. The defect is the failure of numerical possible-witness extraction.

By the semantic criterion above, an action model of Maximalism cannot have only standard numeral values at every reachable object. For every fixed σ there must be a reachable object whose Nσ includes an entity unequal there to each externally standard numeral value. The root itself can still have exactly the standard numeral values, as in the coalesced constructions. This is a semantic consequence about models, not a finitary theorem expressing external ω-standardness. It explains how Maximalism may enjoy current extensional arithmetic at the root while forcing modal numerical nonstandardness elsewhere.

## 15. A countable complete atomic relational domain is Frege-finite

This is an internal theorem, not an appeal to external full powersets or the continuum. It supplies the requested positive size dichotomy for BP + Infinity_e with weaker local assumptions.

Write Fin_σ(A):=∃n(Nσn∧nA). Fix a relational type τ. Let CBC_{e,τ} denote the single range-type/counting-type instance of CBC: every τ-property countable relative to N_e has a Boolean least upper bound in τ.

**Theorem 15.1.** In C,

    I*_e + Atomicity_τ + CBC_{e,τ}
       ⊢ Ctbl_{e,τ}(⊤_τ) → Fin_τ(⊤_τ).

No Choice, Plenitude, or Rigid Comprehension is assumed. Consequently BP + Infinity_e proves at every relational type τ that its entire domain is either Frege-finite or not countable relative to N_e. “Not countable” retains the exact background definition; a continuum cardinal value is not asserted in arbitrary Henkin semantics.

### 15.1 Finite closure facts

The following are C theorems, by N-induction and finite-cardinality extension-invariance (§1).

* Every subset of a finite property is finite. In a successor case delete a witness a from the containing property. If the subset omits a, apply the induction hypothesis directly; if it contains a, apply it after deleting a and then add the fresh point back.
* Adjoining one point to a finite property preserves finiteness: retain its cardinal if that point is already included, otherwise use successor and the fresh-point lemma.
* The union of two finite properties is finite. Induct on the cardinal of the first and use adjoining one point.
* The image of a finite property under a partial functional relation is finite. On deleting a domain witness a, the image either stays unchanged or adds the unique value of a. This is a graph statement at arbitrary admitted input/output types; it introduces no individual-valued operation.

These inductions prove implications about arbitrary internal finite-cardinality witnesses. They do not presume that all such witnesses are externally standard.

### 15.2 Finitely many atoms imply a finite Boolean domain

For A a property of τ-atoms, put

    D_A(p) := ∀a(Atom_τ(a) ∧ a≤p → Aa).

Under Atomicity_τ, D_empty consists exactly of ⊥_τ. If A=B∪{a}, with a an atom absent from B, then

    D_A = D_B ∪ {p∨a : D_B(p)}

as actual extensions. For the nontrivial inclusion, q∈D_A decomposes as (q∧¬a)∨(q∧a). The second term is either ⊥ or a, because a is an atom. Every atom below q∧¬a belongs to B, so q∧¬a∈D_B. Conversely adding a to a member of D_B introduces no atoms outside B∪{a}: any atom below p∨a lies below p or equals a, by finite Boolean distributivity and atomicity of that atom. Finite union and functional-image closure now prove by finite-cardinality induction that Fin_τ(A) implies Fin_τ(D_A). Taking A to be all atoms yields Fin_τ(⊤_τ).

Therefore if the whole τ-domain is not finite, its atom property is not finite. This implication uses Atomicity_τ at the empty-family step and only ordinary finite Boolean algebra thereafter.

### 15.3 A countable infinite atom property contains an N_e-indexed sequence of distinct atoms

Suppose the whole τ-domain is countable but not finite. Restrict its coding relation to the atoms. Since I*_e holds, each nonempty numeric-code fiber has a least code (§8); these least codes are distinct for distinct atoms. Pulling back the natural-number order gives a well-order of the atom property for every admitted nonempty subproperty.

The finite-initial-segment argument of §10 generalizes from an entire type to any nonfinite property A equipped with such a well-order. Define J(n,a) to say that a∈A and n∈Nτ counts the strict A-predecessors of a. Zero is represented by the least element of A. If n counts the predecessors of a, then Sucτ n counts those predecessors together with a. That lower-closed finite property cannot exhaust A, since A is not finite. The least element b of its complement has exactly that property as its predecessors, providing the successor step. Finite equicardinal inclusion proves uniqueness of a for n; Exclusivity proves uniqueness of n for a. Hence J is a relational injection Nτ→A.

A nonfinite property A also makes the entire τ-domain nonfinite, by finite-subset closure. Therefore Infinity_τ and I*τ hold. The canonical Peano graph of §13 now transfers the injection to N_e. We obtain a graph j(n,a), total and one-to-one from N_e into the atoms. This construction uses least codes and internal induction, not a choice principle.

### 15.4 Countable joins code every numerical subset extension

For any X^{ν_e t} supported on N_e, let

    F_X(a) := ∃n(N_en ∧ Xn ∧ j(n,a)).

F_X is countable relative to e: j itself gives its disjoint nonempty numeric-code fibers. CBC_{e,τ} therefore supplies a unique Boolean least upper bound y_X. We use its defining graph K(X,y), so no choice or function-representation assumption is needed.

For every n∈N_e and its selected atom a=j(n),

    a≤y_X  iff  Xn.

The forward direction from Xn is the upper-bound property. If ¬Xn, every atom in F_X differs from a, by injectivity of j, and therefore lies below ¬a. Leastness gives y_X≤¬a, excluding a≤y_X because a is nonzero. It follows that equal joins give equal actual extensions of X on N_e. We do not claim that arbitrary coextensive X objects are identical.

Let C(y,k) be the assumed countability code for the entire τ-domain, and compose it with K:

    T(X,k) := ∃y(K(X,y) ∧ C(y,k)).

Every supported numerical property X has a code k∈N_e. If X,Y share such a code, the original C condition makes their joins identical, so X and Y agree on every number.

Now form, using ordinary C comprehension,

    D(n) := N_en ∧ ¬∃X[Supported_N(X) ∧ T(X,n) ∧ Xn].

D is supported on N_e, hence has a code k∈N_e. Every X sharing code k with D agrees with D at k. Thus the existential clause on the right at n=k is equivalent to Dk itself: one direction uses agreement; the other uses X=D and its code. Consequently Dk↔¬Dk, contradiction.

This completes the theorem. The diagonal uses equality of subset extensions only, so no rigid representative or extensionality principle was hidden in the argument. Atomicity and countable joins are the structural assumptions; the countability hypothesis supplies the selection needed to build the atom sequence.

### 15.5 Stronger theorem: Atomicity is unnecessary

The parent researcher proposed retaining an infinite principal ideal at each split. The following audit completes that improvement and supersedes Atomicity in Theorem 15.1.

**Theorem 15.2.** In C, for any counting type σ and relational type τ,

    I*σ + CBC_{σ,τ} ⊢ Ctbl_{σ,τ}(⊤_τ) → Fin_τ(⊤_τ).

Thus the only positive structural assumption beyond the Peano index is countable completeness at the given Boolean type. The proof in fact uses joins only of countable, pairwise disjoint nonzero families. This is an internal Henkin-valid argument and does not use a choice schema, Plenitude, Atomicity, or Rigid Comprehension.

Assume the τ-domain countable and nonfinite. Least σ-numeric codes well-order its elements, as before. Say Inf(p) when the principal ideal [0,p]:=λq.q≤p is not Fin_τ. Inf(⊤) holds.

If Inf(p), p is neither zero nor an atom, since either case makes [0,p] have at most two members. Split p=a∨b with a,b disjoint and nonzero. At least one of Inf(a),Inf(b) holds: otherwise [0,p] is the image of the finite Cartesian product [0,a]×[0,b] under join, using q=(q∧a)∨(q∧b). That image is finite by iterating the finite-image and finite-union lemmas; this two-argument proof needs no product object type. Hence some a<p satisfies Inf(a). Let T(p,a) select the least-coded such a whenever Inf(p).

Define Rec as the least relation containing (0σ,⊤τ) and closed under

    Rec(n,p) ∧ T(p,a)  →  Rec(Sucσn,a).

Its impredicative definition quantifies relations of the admitted type νσ τ t. Pair-induction shows that its pairs have n∈Nσ and Inf(p), and gives the same zero-or-successor decomposition used for the canonical graph in §13. Nσ-induction supplies a value at every n: start at top and use the existence of T for every infinite principal ideal. The Peano conditions make this graph functional: a pair at zero cannot come from a successor, and two pairs at Suc n decompose to pairs at the same predecessor n, whose values agree by induction; T has a unique output. This proves the required recursion internally rather than assuming an individual-valued recursion operation or dependent choice.

Write p_n for the unique graph value, purely as convenient mathematical notation, and let r_n=p_n∧¬p_{Suc n}. Then r_n is nonzero, the p_n descend, and r_m,r_n are disjoint for m≠n. These facts follow by N-induction using p_{Suc n}<p_n and the usual Peano order. In particular the r_n are distinct. Every property of selected r_n is countable relative to σ, through its numerical indices.

For each actual X supported on Nσ, take the join y_X of precisely the r_n with Xn. Pairwise disjointness gives

    r_n≤y_X iff Xn:

when ¬Xn every selected r_m lies below ¬r_n, so the join does too; r_n is nonzero. Equal joins therefore imply equal numerical subset extensions. Composing the join graph with the assumed numeric code of τ and applying the exact diagonal of §15.4 yields a contradiction. No step of this latter argument requires that r_n be atoms.

The contrapositive form is useful: under I*σ and CBC_{σ,τ}, an internally nonfinite Boolean domain τ cannot be countable relative to Nσ. BP + Infinity_e therefore gives the finite-or-uncountable conclusion, but is far stronger than the assumptions needed for this particular conclusion.

### 15.6 CBC can be stated using only disjoint nonzero families

Under I*σ, CBC_{σ,τ} is equivalent in C to its restriction to countable properties of pairwise disjoint nonzero τ-entities. This makes the disjoint-family formulation precise without a concealed choice assumption.

Given a countable F, its multicode relation is already a partial functional graph from Nσ into F: a number shared by two F-members forces their identity. Fill missing indices with ⊥τ, obtaining a total functional graph E(n,y) whose range contains F and is contained in F∪{⊥}. This completion is definable by cases, with no selected preimages and no operation-representation assumption.

Using the graph recursion just proved, form s_0=⊥ and s_{Suc n}=s_n∨E_n, and put b_n=E_n∧¬s_n. All of this is expressed by relational graphs; the displayed subscripts abbreviate their unique values. By induction, the nonzero b_n are pairwise disjoint, and their family is countable via its n-indices. Let y be its join, supplied by the disjoint version of CBC. Induction gives s_n≤y and E_n≤y, since E_n≤s_n∨b_n. Thus y is an upper bound of F. Conversely every upper bound of F bounds each b_n (which lies below E_n, and any extra E_n is bottom), and hence bounds y. Therefore y is the required join of F.

This equivalence is stated with the explicit I*σ assumption used for functional numerical recursion. It does not silently apply the argument to a collapsed finite Frege index.

## 16. Ambient Frege arithmetic at e agrees with the hereditary rigid core

This section uses the independently developed core lemmas in `/tmp/classicism-research/relational-coding-recursion-20261022.md`, §§14–16, rather than claiming that full external powersets are available. Under C5, the hereditary core consists of all individuals at e, the settled truth values at t, and the rigid relations supported on the lower cores at higher types. Its restricted quantifiers and comprehension interpret an extensional Henkin higher-order structure in the same admitted relational types. Under BP, RC makes every admitted actual subset of a core tuple have a unique core representative. The core lemmas and numerical-parameter absoluteness from §2 provide the following bridge.

Fix counting type e only. Write K(X) for Core_et(X), and for n:ν_e define the admitted operation

    q(n) := λX^{et}. K(X) ∧ nX.

Let 0^K and Suc^K be the zero and successor in the core interpretation; explicitly

    0^K = λX. K(X) ∧ ∀x ¬Xx,
    Suc^K(a) = λX. K(X) ∧ ∃x[Xx ∧ a(λu.Xu∧u≠x)].

The individual quantifiers need no core restriction because Core_e is the entire individual domain. Let N^K be the least core property containing 0^K and closed under Suc^K, with the core's quantifiers and comprehension.

**Theorem 16.1 (BP).** q is a bijection from ambient N_e onto N^K, preserves zero and successor, and transfers the ambient Axiom of Infinity_e exactly to the core-translated Axiom of Infinity at its individual domain.

For n∈N_e, q(n) is in Core_ν. Its membership at a core_et parameter X is nX, a settled proposition by the numerical-plus-core parameter absoluteness theorem. At noncore X it is false, and the core predicate itself is settled. Thus q(n) has settled membership everywhere; the C5 core lemma identifies this with rigidity, and its support is visibly in Core_et.

The zero identity q(0)=0^K follows from the displayed definitions. If X is core_et, deletion of one individual gives another core_et property. Unpacking successor therefore proves q(Suc n) and Suc^K(q(n)) coextensive. Both are core objects, so core extensionality identifies them.

For injectivity, suppose q(m)=q(n) for ambient numbers. Given any ambient e-property X, RC gives its unique rigid coextension Y. Since every individual is core, Y lies in Core_et. Finite-cardinality extension-invariance gives mX↔mY and nX↔nY, while equality of q(m),q(n) gives mY↔nY. Hence m and n agree on every ambient e-property. Numerical Extensionality under BP (§3) gives m=n. This step is precisely where the fact that Core_e contains all individuals matters.

Ambient N-induction now shows that every q(n) lies in N^K: the core zero and successor equations supply its base and step. For the converse, define the actual image property

    P(a) := Core_ν(a) ∧ ∃n(N_en ∧ a=q(n)).

It is supported on Core_ν. RC provides a rigid coextension P*, hence a core property of that domain. P* contains 0^K and is closed under Suc^K by the same equations, so core N-induction gives every N^K-element P*, and therefore P. This proves surjectivity without external full semantics or a choice principle.

Finally ⊤_e is core_et under BP, and q(n)(⊤_e)↔n(⊤_e). The established bijection therefore identifies

    ∀n∈N_e ¬n(⊤_e)

with its core-translated counterpart. Zero-not-successor and successor injectivity likewise transfer through the bijection. Thus optional Infinity_e is the same arithmetic size assumption for the ambient theory and for its extensional core.

**Scope warning.** This is a bridge for counting individuals, not a claim that ambient and core Frege numbers coincide at every counting type. At t the ambient Boolean algebra can be infinite while Core_t has exactly two truth values. Its ambient N_t can therefore be Peano while the core's cardinalities of truth values have finite overflow. Extending the preceding argument to such a type would improperly replace arbitrary ambient subsets by subsets of a proper core subdomain.

## 17. Frege infinity and a self-indexed numerical injection

**Theorem 17.1 (C).** If there is a total injective functional relational graph from Nσ into σ, then Infinity_σ. No I*σ, Choice, Plenitude, or well-ordering assumption is needed in this direction.

Suppose, toward contradiction, that m∈Nσ counts the whole σ-domain. Every finite property has an admitted well-order, by finite-cardinality induction: the empty property has the empty strict order; in a successor case delete a witness a, well-order the remainder by the induction hypothesis, and append a as the last element. For any nonempty subproperty of the enlarged domain, either its intersection with the remainder has a least member or a is its sole member. This uses a relational order of type σσt, which is admitted even for σ=e.

Choose such a strict well-order < of the entire finite σ-domain. For each a let P_a(x):=x<a. Finite-subset closure gives a numerical cardinality of P_a, and Exclusivity makes it unique among Nσ. Thus

    H(a,n) := Nσn ∧ n(P_a)

is a total functional graph σ→Nσ. It is injective: if a<b then P_a is a proper subset of P_b (a belongs to the latter and not the former), so finite equicardinal inclusion forbids the same number from counting both. It misses m: if m counted P_a as well as the whole domain, the same inclusion theorem would make P_a universal, contradicting a∉P_a.

Now let j:Nσ→σ be the hypothesized injective graph. The composite j∘H is a total injective selfgraph of σ, and its range omits j(m): equality with an image j(H(a)) would, by injectivity of j, force H(a)=m. The recorded C Dedekind lemma (`pure-possibility-implies-axiom-of-infinity-t.md`, lemma on a total left-unique nonsurjective relation) says no finite cardinality can count a domain admitting such a graph. This contradicts m(⊤σ).

This proof uses internal finite-cardinality induction; it does not replace m by an external finite integer or assume that all Frege numbers are realized. The distinct predecessor-cardinality entities are distinguished by their realized finite extensions, not by an extensionality axiom.

**Corollary 17.2 (C + well-orderability of σ).** The following are equivalent:

1. Infinity_σ;
2. an injective relational graph Nσ→σ exists;
3. a total injective nonsurjective relational selfgraph of σ exists.

The implication 1→2 is the finite-predecessor construction of §§5 and 10, now using an infinite well-ordered domain. The implication 2→1 is Theorem 17.1. Given 1 and 2, I*σ holds; shift the j-image by successor and fix points outside that image. The resulting total injective selfgraph omits j(0), proving 3. The recorded Dedekind lemma gives 3→1. All maps in this statement are relational graphs, so the individual case never invokes the inadmissible type ee.

In particular □Functional Choice supplies the recorded well-orderability principle, so it equates the Frege and relational Dedekind formulations of infinity at every type. It still does not assert Infinity_e: finite individual domains remain models unless that optional size axiom is added.

## 18. Bounded arithmetic, Σ₁ correctness, and a concrete possible proof of inconsistency

This section is a new mathematical argument, building on the recorded C lemmas for arithmetic and on standard arithmetization. It does not establish inconsistency of Maximalism. Its conclusion is a sharply specified modal arithmetic pathology.

Fix any counting type σ and abbreviate Nσ, Iσ, I*σ by N,I,I*. The recorded source proves in C that I↔I*, that numberhood persists, that distinct current numbers remain distinct conditional on I, and that Sum/Prod on current numerical parameters are conditionally determinate. See Goodsell's lemmas 2–7 in `countable-boolean-completeness-implies-necessity-of-arithmetic.md`; no CBC is used in those lemmas.

### 18.1 Syntax and coding conventions

“Δ₀” and “Σ₁” here refer to the ordinary first-order arithmetic language with bounded quantifiers and the usual arithmetic terms. This is conservative notation for the background's relational arithmetic language. No object-level addition or multiplication operation is postulated. A compound term is replaced by a finite tuple of numerical value variables linked by Sum/Prod graphs. Under I these values exist uniquely. At an I-world they retain the values supplied by current numerical parameters, by the recorded arithmetic persistence and functionality lemmas. Thus the modal arguments below may reason with the customary term notation and then eliminate it into the permitted relational language. This prevents an accidental appeal to Plenitude for a numerical function object.

The proof-coding facts used later are standard: provability for a suitably presented effective extension of PA has a Σ₁ formula; every Σ₁ formula can be put into the form ∃n R(n) with R bounded; true Σ₁ sentences are PA-provable; and the usual provability predicate satisfies the conditions for Gödel's second theorem. A checked primary exposition is Andrew Marks, *Computability Theory*, 25 February 2024, Corollary 11.3, Lemma 11.5, §12.1 and Theorem 13.5, printed pp. 50–58: <https://math.berkeley.edu/~marks/notes/computability_notes_v1.pdf>. The single-witness reduction can use one number bounding all original witnesses, retaining them as bounded quantifiers. No claim that an arbitrary primitive-recursive proof predicate is literally Δ₀ in the bare language is needed.

### 18.2 Bounded numerical Barcan is already available in C + I

**Lemma 18.1.** C proves, assuming I, for every b∈N and arbitrary X^{νσt},

    [∀m∈N (m≤b → □(I→Xm))]
       → □(I→∀m∈N (m≤b→Xm)).                    (BBF)

Use N-induction on b, with the induction property including the displayed implication universally over X and conditional on I. At zero, the premise gives □(I→X0), and the C theorem that I implies the Peano laws yields necessarily that, if I, every number ≤0 is zero. This proves the conclusion.

At Suc b, current I gives the elementary order inclusion m≤b⇒m≤Suc b. Hence the premise supplies the induction hypothesis at b, as well as □(I→X(Suc b)). Inside the box, I supplies the Peano decomposition

    m≤Suc b  iff  (m≤b or m=Suc b).

Combine the two boxed conclusions. The proof necessitates only C theorems of the form I→(Peano law), never the optional current assumption I. Numberhood of b and its successor persists, as required when using the laws in the box. The induction applies even to internally nonstandard b and to X with arbitrary admitted parameters.

This bounded result is substantially weaker than NCOLL or its I-relative version: it places a current numerical bound on the quantified witnesses.

### 18.3 Δ₀ absoluteness and Σ₁ persistence

**Theorem 18.2.** For each bounded arithmetic formula A with numerical parameters, C + I proves both

    A → □(I→A),          ¬A → □(I→¬A).

For identity use NI in the positive case and the recorded conditional distinctness lemma in the negative case. Sum/Prod use the recorded conditional determinacy lemma, with current I selecting the disjunct matching current truth. For order m≤n, a positive instance has a current Sum witness, which persists; a negative instance has a current reverse strict-order witness, which persists and, conditional on future I, excludes m≤n. Finite propositional combinations use K.

For a bounded universal ∀m≤b B, if true, apply the formula induction hypothesis at each current m≤b and then BBF. If false, a current counterexample m≤b persists as a number; the order instance and ¬B persist conditional on I, so it remains a counterexample at every I-world. This gives both directions. Bounded existential formulas follow by negation. Compound bounds are treated by their unique current numerical value as in §18.1. This completes the structural induction without countable completeness or an unbounded numerical BF.

**Corollary 18.3.** For every Σ₁ arithmetic formula A with current numerical parameters,

    C + I ⊢ A → □(I→A).

Choose its current finite tuple of existential witnesses. Their numberhood persists, and their bounded matrix persists by Theorem 18.2. Thus the same witnesses establish A at every I-world. The analogous negative persistence holds for Π₁ formulas. These are schema statements, not an internal truth predicate for all formulas.

### 18.4 The actual Σ₁ and Π₁ arithmetic of Maximalism

For a fixed σ define the external first-order arithmetic theory

    Tσ := {A : C proves Iσ→A},

using the fixed translation into Frege arithmetic at σ. This is the arithmetic shadow of C + Iσ, not Maximalism. It is deductively closed, recursively enumerable, and extends PA, by the recorded source lemmas. A full S5 C model with both infinitely many individuals and infinitely many worlds has every type infinite and each Nσ exactly the standard numeral values; Sum and Prod then have their standard interpretations. It satisfies Iσ, so Tσ is true in the standard natural numbers and in particular consistent. For σ=e alone, the simpler full infinite-base extensional model suffices; it would not suffice uniformly at σ=t. These are metatheoretic facts; no internal assertion of standardness is being added to C.

**Theorem 18.4.** For every Σ₁ sentence A, Maximalism proves A if Tσ proves A, and proves ¬A otherwise. Consequently each Σ₁ and each Π₁ sentence has its standard truth value at every Maximalist evaluation point.

Maximalism gives Iσ, since I*σ holds in the full S5 model with infinite individuals and worlds just described. If Tσ proves A then C proves Iσ→A, so Maximalism proves A. Otherwise Iσ∧¬A is C-consistent, and the pure Possibility form of Maximalism gives ◇(Iσ∧¬A). If A held currently, Corollary 18.3 would give □(Iσ→A), contradicting that possibility. Hence Maximalism proves ¬A.

Every true standard Σ₁ sentence is PA-provable, hence belongs to Tσ. No false standard Σ₁ sentence belongs to Tσ by its full standard C model. This establishes the standard-truth conclusion for Σ₁; negation gives Π₁. It does not assert that the current numerical domain is externally standard, nor that Maximalism fixes all higher-complexity arithmetic sentences to their standard truth values.

### 18.5 A canonical arithmetic witness of numerical collection failure

Choose a fixed effective presentation of Tσ and its usual arithmetized provability predicate. If a recursive axiom set is desired, replace the recursively enumerable presentation by a recursively decidable padded presentation with exactly the same theorems: attach a syntactic certificate recording a bounded enumeration stage to each axiom. Fix this presentation before forming the consistency sentence. The standard Hilbert–Bernays derivability conditions then apply.

Put Con(Tσ):=¬Prov_Tσ(⌜0=1⌝). Choose a bounded formula Rσ(n) for the single-witness Σ₁ normal form

    Prov_Tσ(⌜0=1⌝) ↔ ∃n Rσ(n),

with PA proving the equivalence. Rσ may include boundedly quantified proof and computation certificates; n packages or bounds all unbounded witnesses. It is safer to call Rσ an **inconsistency certificate predicate** than to identify its one variable with a raw unaugmented proof code. All its fixed natural-number constants become closed Frege numerals, so the translated formulas are pure.

Since Tσ is consistent, its standard Con(Tσ) is true, and Theorem 18.4 gives

    Max(C) ⊢ Con(Tσ).

Gödel's second theorem gives Tσ ⊬ Con(Tσ). By the definition of Tσ, C therefore does not prove Iσ→Con(Tσ); equivalently Iσ∧¬Con(Tσ) is C-consistent. Maximalism consequently gives

    Max(C) ⊢ ◇(Iσ ∧ ¬Con(Tσ)).

Combining the two, and applying bounded absoluteness separately to each current number, gives the sharper pair

    ◇[Iσ ∧ ∃n∈Nσ Rσ(n)],
    ∀n∈Nσ □[Iσ→¬Rσ(n)].

Thus a numerical inconsistency certificate for the fixed effective theory Tσ is possible at an arithmetic world, although **no current number can become such a certificate at an arithmetic world**. This is an explicit, purely arithmetical counterexample to the Iσ-relative numerical possible-witness principle. It avoids using an unspecified higher-order property as the counterexample.

There is an additional boundedness conclusion. For every current b∈Nσ, BBF applied to ¬Rσ gives

    □[Iσ→∀n∈Nσ(Rσ(n)→b<n)].

Any possible inconsistency certificate at an Iσ-world exceeds each current numerical bound in this precise boxed sense. Do not move the outer ∀b inside □: doing so would be the very numerical BF step that fails.

These statements do not say that Tσ really has a finite proof of contradiction, that Maximalism is inconsistent, or that the relevant possibility preserves external standardness. The standard metatheory says Tσ is consistent. The possible certificate occurs in a nonstandard arithmetic interpretation, and the formulas exhibit exactly how the quantifiers permit that outcome. Under BP, the relative numerical collection principle blocks the phenomenon; under BP + Infinity_σ, the conditional Iσ is available throughout by pure absoluteness.

### 18.6 No consistent effective extension of Maximalism

**Corollary 18.5.** Max(C) has no consistent recursively enumerable axiomatized extension in a fixed effective language containing the displayed arithmetic translation. In particular, assuming its recorded relative consistency, Max(C) has no recursively enumerable axiomatization.

Suppose S were such a consistent extension. Since S includes Max and hence Iσ, its first-order arithmetic consequences T_S form a recursively enumerable consistent extension of PA. Its standard consistency sentence Con(T_S) is a true Π₁ sentence. Theorem 18.4 puts this sentence in Max, hence S, and therefore T_S proves its own consistency. This contradicts Gödel's second theorem for the fixed standard presentation of T_S.

Equivalently, no second-incompleteness machinery is necessary for this particular corollary. For each program, its halting assertion H is Σ₁. Max proves H if it halts and ¬H if it does not. Enumerating S-proofs until one of H,¬H appears would decide halting; one must appear, and consistency of S prevents the wrong answer because S already contains the correct Max consequence. This is impossible.

The conclusion is a limitation on effective axiomatization, not a contradiction in Maximalism. C + □Functional Choice, with or without the single optional Infinity_e axiom, is recursively axiomatizable (its type/formula schemata are effectively enumerable) and has the indicated full models in the usual metatheory. This contrast is precise; it does not by itself decide which theory should be accepted as true.

## 19. Addendum: the core bridge under C5

The relational-core lane supplied a stronger argument after §16 was written. It is recorded here without deleting the earlier BP proof.

Under C5, persistent predicates have settled membership, and settled membership characterizes rigidity. The C theorem that numbers are necessarily numbers, necessitated with its universal closure, makes N persistent. Thus N is already rigid under C5.

Induct on n∈N_e to prove that nX is settled for every rigid e-property X. At zero, all X-memberships are settled, and BF makes ∀x¬Xx settled. At a successor, X−{a} is rigid for each individual a; apply the induction hypothesis to n(X−{a}), combine with settled Xa, and use BF to make the existential over a settled. Consequently q(n) from §16 is core-valued under C5, without Atomicity or RC.

The image property P(a)=Core_ν(a)∧∃n(N_en∧a=q(n)) is itself settled: N-membership, core-membership and identity are settled under C5, and BF handles the quantifier. Hence P is already a core property, so core induction gives the same surjectivity as in §16 without an RC step. The zero/successor equations and ambient induction are unchanged. Because q(n)(⊤_e)↔n(⊤_e), this surjection alone transfers Infinity_e in both directions between ambient and core interpretations. Injectivity is not needed for that transfer.

With Infinity_e also assumed, q becomes injective without Atomicity or RC. Realize any n at an actual finite e-property X. Every Frege-finite property has a rigid coextension in C, by finite-cardinality induction and closure of rigid haecceities under finite joins. Call this coextension Y. If q(n)=q(m), then nY and mY, and Exclusivity gives n=m. Thus C5 + Infinity_e already gives the full numerical bijection to the core. The original BP theorem remains stronger in the finite-domain case, where its numerical extensionality argument also identifies any overflow values.

## 20. C5 already gives numerical extensionality and the full e-core bridge

This improves §§3, 7.5, 16 and 19. The proof was independently audited by the relational-core lane. Atomicity and Rigid Comprehension are unnecessary for these numerical conclusions.

**Lemma 20.1 (C5).** If n∈Nσ and X^{σt} is rigid, then nX is settled: nX→□nX and ¬nX→□¬nX.

Induct on n, carrying Nn in the induction property. At zero, every membership Xx is settled by rigidity under C5, and BF makes ∀x¬Xx settled. In the successor case, X−{a} is rigid for every a: its memberships are Boolean combinations of settled memberships and settled identities. The induction hypothesis makes n(X−{a}) settled, as is Xa; BF then makes ∃a[Xa∧n(X−{a})] settled. This argument works at every σ, not only e. In particular ⊤σ is rigid under C5, so n(⊤σ) is settled.

**Theorem 20.2 (C5).** Every natural cardinality is either realized or identical to the bottom cardinality:

    ∀n∈Nσ [ (∃X nX) ∨ n=⊥_{νσ} ].

Use N-induction with W(n):=Nn∧[(∃X nX)∨n=⊥]. Zero is realized by the empty property. If n=⊥, then Suc n=⊥ by the C Boolean identity already used in §3. Otherwise take nX. If X has an outsider, the fresh-point lemma realizes Suc n. If X is universal, finite-cardinality extension-invariance gives n(⊤σ), which is necessary by Lemma 20.1. Numberhood of n is necessary in C. Necessitate the discharged C theorem

    Nn ∧ n(⊤σ) → ∀Y ¬(Suc n)Y

from the finite upper-bound lemma, and use K to infer □∀Y¬(Suc n)Y. Necessary emptiness identifies Suc n with ⊥_{νσ}. This completes the induction without necessitating any optional assumption.

**Corollary 20.3 (C5).** Numerical Null Collapse NCσ and Numerical Extensionality NEσ hold at every counting type.

If a natural cardinality has no instance, Theorem 20.2 identifies it with bottom. If coextensive numerical m,n have an instance, Exclusivity identifies them; otherwise both are bottom. Consequently every equivalence in Theorem 7.5 already holds over C5, not merely BP:

    Infinityσ ↔ all numerical cardinalities realized ↔ I*σ ↔ Iσ
              ↔ successor injective on Nσ.

There is one more compact equivalent under C5:

    Infinityσ ↔ ¬Nσ(⊥_{νσ}).

Infinity gives realization, excluding bottom. Conversely if m counts the universal property, its successor is an uninstantiated natural cardinality and hence bottom by NC, so bottom is a number. The bottom cardinality here is **not zero**: zero counts empty properties, whereas bottom counts no properties at all. This warning is essential to the proposed simpler definition.

**Corollary 20.4 (C5).** The e-core map q of §§16 and 19 is a bijection even without Infinity_e. Surjectivity and the successor equations were proved in §19. For injectivity, if n has a witness X, it is a finite property and therefore has a rigid coextension Y in C; because the individual core is all e, Y is core_et. Equality q(n)=q(m) then makes Y a common instance and Exclusivity gives n=m. If n has no witness, NC makes it bottom; equality of q-values prevents m from having a rigid finite witness, so m also is bottom. Thus the full e-core arithmetic bridge requires C5 alone.

The stronger BP numerical-parameter absoluteness theorem in §2 still has a separate role: it treats arbitrary pure formulas with numerical parameters and unrestricted higher-type quantifiers. The present C5 proof establishes these particular numerical extensionality and core-comparison results; it does not claim all such pure formulas are absolute under C5.

## 21. Maximalism makes each fixed finite-individual possibility internally infinite

This is a new localization of the recorded Max→Infinity_t proof. The world-cardinality lane independently audited the construction and transfer. No Strong Possibility, Atomicity, Choice, BF or Plenitude is assumed.

Fix an externally specified positive integer r. Let E_r be the closed pure sentence saying that exactly r individuals exist. Let A_t:=λp.Atom_t(p). For n∈N_t put

    h_r(n) := E_r ∧ (Suc_t n)(A_t),
    Π_r := ∀n∈N_t ◇h_r(n).

Here h_r is an admitted ν_t→t operation. E_r is an ordinary fixed finite formula, not an unrestricted variable cardinality parameter.

### 21.1 Consistency of Π_r

For each positive integer j take the full S5 model with constant individual domain D={1,…,r} and exactly j mutually accessible worlds. At t its Boolean algebra is P(W_j), its atoms are the j singletons, and at every component world E_r∧(Suc_t n_j−1)(A_t) is true, where n_j−1 denotes the standard numeral j−1.

Coalesce these models under a new root using the free-root-component construction of Classicism Appendix E. At e one may take the singleton set of compatible constant threads when r=1; in general the usual product of the r-element component domains suffices. At a relational type the new entity consists of an arbitrary root truth extension on root arguments together with one admitted component entity in each summand. Application is componentwise away from the root, and its root truth extension is unrestricted. Each projection onto a component domain is onto. Each component keeps its entire S5 world structure; one does not flatten a j-world component into a one-world extensional model.

Closure under abstraction follows by evaluating the abstract at the root and separately in every component. H and Logical Equivalence hold by the same componentwise argument as in `writeups/coalesced-all-finite-individual-domains.md`, now with full S5 components. In particular the root can see every component world, while a world inside a component sees exactly that component's worlds.

Let S be the external set of root denotations of the standard ν_t numeral terms. There is an admitted property of ν_t whose root extension is S, since the root component is arbitrary. S contains zero and is successor-closed, so impredicative Frege induction makes every root number a member of S. Conversely every standard numeral is a root number. Thus the root N_t consists exactly of the standard numeral denotations. These denotations are distinct: any two are distinguished by projection into a finite component whose t-domain, of size 2^j, has room to realize both finite cardinalities.

For root numeral n_k, the component with j=k+1 makes E_r true and has exactly k+1 propositional atoms, so h_r(n_k) is true there. Thus Π_r holds at the root of a model of C, establishing its C-consistency. The use of externally full components and arbitrary root components is explicit; no assertion that every Henkin model has standard N_t is involved.

### 21.2 Pulling the possible pattern back to the actual numbers

Maximalism supplies ◇Π_r. If n is any current number, C gives □N_tn. As in the recorded proof, ◇Π_r together with this persistence gives ◇◇h_r(n), and 4 gives ◇h_r(n). Hence Max proves Π_r itself, including its instances at all internally quantified current numbers.

If n,m are current numbers with n≠m, the boxed Exclusivity and Swap lemmas give

    □¬[(Suc_t n)(A_t) ∧ (Suc_t m)(A_t)].

The argument is exactly the recorded proof's successor-exclusivity step with the property A_t in place of the universal individual property. It does not depend on A_t being rigid. Therefore h_r(n) and h_r(m) are Boolean-disjoint. By Π_r neither is bottom, so they are distinct. We obtain a total injective operation from N_t into the nonbottom part of the Boolean interval ↓E_r. Its image is a pairwise disjoint family. Equality Suc_t n=Suc_t m would give equality of these h_r-values, so Suc_t is injective on N_t as well; zero is never a successor by C.

Let H(p):=∃n∈N_t(p=h_r(n)). On Q_r(p):=(p≤E_r), define the relational graph

    R(p,q) := [∃n∈N_t(p=h_r(n) ∧ q=h_r(Suc_t n))]
              ∨ [¬H(p) ∧ q=p].

The first part shifts the h_r-image and the second fixes its complement. Totality on Q_r follows from cases on H. Injectivity follows from injectivity of h_r and successor; a fixed point outside the image cannot share an output with a shifted point inside it. Finally h_r(0) is in Q_r and outside the range, because zero is not a successor. This is the recorded Dedekind condition, indeed with a single-valued graph.

**Theorem 21.1.** For every fixed positive standard r, Max(C) proves that the Boolean interval ↓E_r is relationally Dedekind-infinite and hence Frege-infinite:

    ¬∃m∈N_t m(λp.p≤E_r).

It also supplies the explicit N_t-indexed pairwise-disjoint nonbottom family h_r above. This is an internally quantified theorem, stronger than the separate external schema saying that ↓E_r has arbitrarily many standard-finite members. It does not assert an internal universal quantification over r, which would require a separate uniform consistency construction and conditional preservation of the individual cardinality parameter.

For r=1 this shows that the monistic possibility has internally infinite propositional structure even in ordinary Maximalism. Strong Possibility additionally makes E₁ actually true, but is unnecessary for the interval-infinity conclusion. The theorem does not settle Strong Possibility's consistency.

## 22. A choice-free diagonal and ambient cardinal stratification under Maximalism

**Lemma 22.1 (C).** If there is a total single-valued injective relational graph J from Nσ into a domain τ, then

    ¬Ctbl_{σ,τt}(⊤_{τt}).

Suppose instead R(X,n) gives the recorded multiple-code countability relation for all τ-properties. Define

    C(X,a) := ∃n∈Nσ[R(X,n) ∧ J(n,a)].

Every X has at least one a-code. If C(X,a) and C(Y,a), injectivity of J identifies their witnessing numbers, and the disjoint-code condition on R gives X=Y. Thus C is a possibly multivalued assignment of nonempty pairwise-disjoint sets of τ-codes to all τ-properties.

Comprehension gives the diagonal property

    D(a) := ∃X[C(X,a) ∧ ¬Xa].

Choose an a with C(D,a). If D(a), a witness X to its defining existential shares a code with D, hence X=D, contradicting ¬Xa. If ¬D(a), the witness X=D makes its defining existential true. Both alternatives contradict classical logic. No code needs to be selected uniformly, no numerical least-code principle is used, and no I*, Choice, Plenitude or extensional collapse of properties is assumed. The equality of code-sharing properties is supplied directly by the recorded Ctbl definition.

The same proof is a useful general formulation of relational Cantor: no property domain can be assigned nonempty disjoint codes in its argument domain. Single-valued assignment is unnecessary.

**Theorem 22.2 (Max).** At every counting type σ and every relational type τ,

    ¬Ctbl_{σ,τt}(⊤_{τt}).

The recorded Max→Infinity_t proof supplies an injective pure operation g:N_e→t, not merely the assertion Infinity_t. Max gives I* at every counting type; the canonical number-base isomorphism of §13 therefore supplies an injective graph Nσ→N_e. For every relational τ=τ₁…τ_k t, the constant operation p↦λx₁…x_k.p injects t into τ, with the case k=0 being identity. Compose these graphs and apply Lemma 22.1. All outputs are relational, and no prohibited individual-valued function type is used.

More generally, let α=α₁…α_k t have at least one **relational** argument α_i. Ignoring the other arguments embeds α_i t into α, and hence

    Max(C) ⊢ ¬Ctbl_{σ,α}(⊤_α)

for every counting type σ. To justify transfer, a countability code for α restricts along any injective graph β→α to a countability code for β; composition and comprehension suffice.

This gives a syntactic stratification: all higher relation types with any relational argument are uncountable in the internal numerical sense. The proof does not settle countability of t itself, or of relation types e^k t whose arguments are all individuals. It also does not identify these internal sizes with external alephs in arbitrary Henkin or action models. Any sharper countable/uncountable model spectrum for the remaining types needs an explicit construction, not merely the absence of this diagonal argument.

## 23. Numerical Collection as the supremum of increasing finite initial segments

This provides a simpler equivalent formulation of the parent lane's relative Numerical Collection. Fix σ, write ν=νσ, N=Nσ, and I=Iσ. Everything in the equivalence below is over C; it does not assume I actually true.

For any proposition q define

    h^q_n := λm.q∧m=n,              Q_q := λm.q∧Nm,
    H_q := λY.∃n∈N(Y=h^q_n).

A least upper bound of H_q, if one exists, is necessarily Q_q. Indeed Q_q is an upper bound by persistence of numberhood. If B is least, B≤Q_q. Since every actual successor is a number, λm.B(Suc m) is also an upper bound of H_q; hence B≤λm.B(Suc m). Also h^q_0≤B gives □(q→B0). The necessitated C theorem of N-induction, together with this boxed base and the boxed successor-closure just obtained, gives □(q→∀m∈N Bm). Thus Q_q≤B, so B=Q_q.

Consequently the following are equivalent in C:

    H_q has a Boolean LUB;
    Q_q is that LUB;
    ∀X[(∀n∈N □(q→Xn))→□(q→∀n∈N Xn)].

No optional premise q or I was necessitated. The last display is the q-relative numerical BF principle. For q=I the recorded conditional arithmetic proof needs exactly this principle, so the fixed-type Gödel argument refutes it under Max. The parent lane owns that isolation of relative NCOLL_I; the present addition replaces its singleton family by an increasing family.

Let ≤ be the usual arithmetical order defined from Sum, and put

    B_n := λm.I∧Nm∧m≤n,       K := λY.∃n∈N(Y=B_n).

Conditional Peano arithmetic and number persistence give, for each current n∈N, the Boolean identities

    B_0 = h^I_0,          B_(Suc n) = B_n ∨ h^I_(Suc n).

They follow by necessitating the corresponding C theorems conditional on I and using □Nn. They are identities of relations, not merely current coextensions. The N guard on m excludes nonnumbers at all worlds.

If X is an upper bound of H_I, N-induction using these identities proves B_n≤X for every current n, so X is an upper bound of K. Conversely h^I_n≤B_n, by conditional reflexivity and persistence of Nn, so every upper bound of K is an upper bound of H_I. Their sets of upper bounds are therefore identical.

**Theorem 23.1 (C).** Relative NCOLL_I is equivalent to existence of a Boolean supremum of the canonical family of initial segments {B_n:n∈N}. If it exists, that supremum is λm.I∧Nm.

Under I the family is increasing in numerical order: if n≤k, positive persistence of order gives the necessary conditional inclusion B_n≤B_k. Its successor inclusions are strict when I is actually true, since the actual number Suc n lies in B_(Suc n) and not B_n.

Each B_n is actually Frege-finite as a property of the domain ν. Under ¬I it is empty. Under I, Nσ-induction starts with the singleton {0}; each successor adjoins the one fresh element Suc n. The finite-adjunction lemma constructs a cardinality in N_ν for that extension at every induction step. This uses no external assertion that n is standard and no cross-type cardinality operation with output e. The resulting family K is countable relative to Nσ by the graph Y=B_n, with duplicate values harmless.

**Corollary 23.2 (Max).** At every fixed counting type σ, the canonical countable increasing family of Frege-finite numerical initial segments B_n has no Boolean supremum. Thus even this one explicit increasing-chain instance of countable completeness fails. The statement is about the Boolean order on properties of numbers, which is necessary inclusion, not just current inclusion. Its current union extension is the numerical domain; the failure is that no relation represents the required least Boolean upper bound.

## 24. One more arithmetical truth level and a Π₂ boundary

### 24.1 Standard-true Σ₂ sentences are theorems

The true-Π₁ schema of §18.4 implies every standard-true Σ₂ sentence. In a fixed prenex representation A=∃n∀m δ(n,m) with bounded δ, choose a standard witness k. The sentence ∀m δ(k,m) is standard-true Π₁, so its Frege translation is a Max theorem; existential introduction gives A. Finite tuples of witnesses and universal variables can be coded in the usual way, or treated as tuples directly. This is a metatheoretic schema, with an external standard witness selected separately for each true sentence. It supplies no internal truth predicate and no uniform operation choosing witnesses.

Thus Max includes all true Σ₂ sentences and refutes all false Π₂ sentences. This alone does **not** show that all false Σ₂ sentences are excluded; arithmetic soundness must be established separately. Nor does it establish modal persistence of Σ₂ formulas.

### 24.2 A standard-arithmetic Maximalist model

Use the recorded `coalesced-maximalist-root` construction: coalesce a set of action models complete for C in the fixed effective signature, with arbitrary current root components at the admitted relational types. The construction is a model of Maximalism at the distinguished root. It is not globally full, and the argument below uses only freedom of the current root extensions.

At each fixed σ let Sσ be the external set of root denotations of the closed standard numeral terms. The admitted property of νσ with root extension Sσ and universal component extensions contains zero and is successor-closed at the root. Frege induction therefore shows that every root number is one of those denotations. Conversely each such denotation is a number by finite induction. Distinct standard numerals have distinct root denotations: a full S5 C-model with infinitely many individuals and worlds distinguishes them at every counting type, and completeness of the component family supplies the requisite distinguishing component. Equivalently one may use sufficiently large finite S5 components separately for each numeral pair. Equality at the root distinguishes components, so those numeral values cannot coincide there.

Hence n↦the root value of the n-th numeral identifies the root Nσ bijectively with external ω and identifies successor and zero with their usual operations. This conclusion is valid simultaneously at all the countably many admitted types; it is not a claim about every Max model or every world of this one.

It remains to audit Sum and Prod rather than assume that standard N alone suffices. Fix a standard numeral m. For Sum(m,n,o), finite induction shows that every relation satisfying its base and successor conditions contains the pairs (n,m+n). Conversely, an admitted binary relation on νσ can be chosen whose root extension is exactly

    { (n_k,n_(m+k)) : k∈ω },

with arbitrary, for example universal, component extensions. It satisfies the required base and successor closure at the root. Thus the universal relation quantifier in Sum rejects every numerical pair (n,o) with o≠m+n. Sum therefore has exactly standard addition at the root.

For Prod(m,n,o), finite induction using this addition result gives all pairs (n,m·n). The root binary relation with extension exactly

    { (n_k,n_(m·k)) : k∈ω }

and universal component extensions satisfies the product base and closure clauses and rejects every other numerical pair. Prod therefore has exactly standard multiplication. A formula induction now makes every closed first-order arithmetical sentence true at the root exactly when it is true in standard arithmetic.

**Theorem 24.1 (metatheoretic, relative to the recorded model construction).** Every arithmetical theorem of Max(C), at any fixed counting type, is standard-true. This follows from the existence of one Max model with standard arithmetic at its evaluation point. It does not assert that all Max models have standard numbers or satisfy all true arithmetic, and it makes no claim of an effective procedure listing the truths of that model.

Combining Theorem 24.1 with §24.1 yields an exact fragment statement:

    For each Σ₂ arithmetic sentence A,
    standard A is true  iff  Max(C) proves its Frege translation.

The same model argument excludes false arithmetic theorems at every complexity, although we have not shown that every true sentence of arbitrary complexity is provable.

### 24.3 Effective upper bound and exact degree

Work in the original fixed **finitary effective language**, with an effective enumeration of types, terms and formulas. This paragraph does not apply unchanged to an infinitary extension with noneffective conjunctions. C has a recursively enumerable proof system, as used in the recorded Goodsell argument. A pure Max axiom ◇A has the side condition that C does not prove ¬A, which is Π⁰₁ in its formula code. An oracle for 0′ therefore decides whether a candidate pure sentence contributes such an axiom. Enumerating finite proofs from those axioms and C shows that the Max theorem set is computably enumerable in 0′, hence Σ⁰₂.

More explicitly, a candidate proof can carry finite certificates for its C-theorem/Logical-Equivalence steps. Its finitely many Max-axiom steps then impose finitely many universal nonexistence-of-C-proof conditions. Existence of such a proof is an existential quantifier over its code and those finite certificates followed by a universal quantifier checking the Max side conditions, a Σ⁰₂ definition. Generalization, type correctness and the ordinary finitary inference rules are effectively checkable and add no higher complexity.

The set of true Σ₂ arithmetic sentences is Σ⁰₂-complete. The computable map sending such a sentence to its fixed-type Frege translation is a many-one reduction to the Max theorem set, by the exact fragment statement in §24.2. Consequently:

**Theorem 24.2 (metatheoretic).** In the fixed effective framework, the Max(C) theorem set is Σ⁰₂-complete under many-one reductions and has Turing degree 0″. Its first-order arithmetic consequence set at each fixed counting type is likewise Σ⁰₂-complete and of degree 0″.

The lower bound uses arithmetic soundness from the standard-root model, not mere consistency or the one-sided inclusion of true Σ₂ sentences. The upper bound uses the original C-reference theory. The result is relative to the ordinary sound metatheory in which the recorded coalesced construction exists. It is a precise effectiveness classification, not an inconsistency claim. Since the theorem set is c.e. in 0′, one cannot claim that Max has no consistent extension c.e. in 0′: Max itself supplies such an extension if consistent.

### 24.4 An explicit complexity boundary by diagonalization

There is also a direct incompleteness argument that needs only consistency, the Σ₂ upper bound and inclusion of true Σ₂ sentences. Let T be the arithmetic consequence theory of Max at a fixed counting type, and let Pr_T(x) be the Σ₂ arithmetic formula defining its theorem relation. The complexity-preserving diagonal lemma gives a Π₂ sentence G with

    PA ⊢ G ↔ ¬Pr_T(⌜G⌝).

For clarity about complexity, the primitive recursive substitution operation has a Σ₁ graph provably functional in PA; applying the usual fixed-point construction to the Π₂ formula ¬Pr_T preserves Π₂ after prenex normalization. No truth predicate for arithmetic is invoked.

If T proved G, then Pr_T(⌜G⌝) would be standard-true Σ₂ and therefore a theorem of T. The displayed fixed-point equivalence would contradict consistency. Hence T does not prove G, making G standard-true Π₂. By the separate soundness theorem, T also does not prove its false Σ₂ negation. Thus G is an arithmetical sentence independent of Max, with the true side already at complexity Π₂.

Since C⊢I→G would make G a Max theorem, C does not prove that implication. Thus I∧¬G is C-consistent and Max gives ◇(I∧¬G). The standard infinite full S5 model satisfies I∧G, so Max also gives ◇(I∧G). These possibilities do not decide G at the actual world. They distinguish the theory's arithmetic theorem set from both complete standard arithmetic and its much broader modal possibility commitments.

## 25. Finite bases, finite numerical domains, and finite Hume classes

### 25.1 A finite-power lemma already in C

For A^{σt}, let

    RP(A)(Y) := Rigid(Y) ∧ ∀x(Yx→Ax).

If A is Frege-finite, RP(A) is Frege-finite as a property of the domain σt. Here RP ranges only over admitted rigid properties; no external full powerset is postulated.

Induct on a cardinality counting A, universally over A. At zero, A is empty. Any rigid Y with empty current extension is bottom, because weak inextensibility applied to bottom has a vacuous antecedent. Thus RP(A) is the singleton {bottom}.

At a successor, choose a∈A and put B=A−{a}, with the preceding cardinality counting B. If Y belongs to RP(A), its current deleted extension Y−{a} is finite by finite-subset closure. The C finite-rigidification lemma gives a rigid Z coextensive with that deleted property. Thus Z belongs to RP(B). Finite joins of rigid relations are rigid already in C, so Z∨{a} is rigid as well. According as Ya is false or true, Y is coextensive with Z or Z∨{a}; coextensive rigid properties are identical in C. Conversely each Z in RP(B), and its union with {a}, belongs to RP(A). Thus RP(A) is the union of the identity image and the adjoin-a image of RP(B). Finite images and finite unions are finite by §11's C lemmas. This completes the induction in bare C. A itself need not be rigid. We do not claim that the literal abstract Y−{a} is rigid; that was an unnecessary use of C5 in the earlier version of this paragraph.

### 25.2 Finiteness transfers exactly to the numerical domain under C5

Write Fin_τ(X):=∃n∈Nτ nX. Then

    C5 ⊢ Fin_σ(⊤σ) ↔ Fin_νσ(Nσ).

For the forward implication, if the σ-domain is finite, §25.1 makes its entire rigid-property domain RP(⊤σ) finite already in C. Every such rigid property is a subset of a finite domain, hence finite. The relation

    R(Y,n) := Rigid(Y) ∧ Nσn ∧ nY

is therefore total and single-valued on that finite domain, by finite-subset closure and Exclusivity. Its range is exactly the realized numerical cardinalities: a realized finite property has a rigid coextension in C by finite haecceity joins, and numerical extension-invariance preserves the witnessing cardinality. Thus the realized numerical cardinalities form a finite image, a conclusion already valid in bare C. Theorem 20.2 is the only C5 step: Nσ adds at most the single bottom cardinality; finite unions finish the argument.

The reverse implication already holds in bare C. If the σ-domain were Frege-infinite, §7 would give I*σ. The successor graph would then be an injective self-map of the property Nσ missing zero. The recorded Dedekind lemma contradicts Fin_νσ(Nσ).

**Corollary 25.1.** C5 proves that a finite base domain has a finite internal domain of Frege natural cardinalities. Strong Possibility refutes the type-e instance: it makes e a singleton, while Max's I*_e makes N_e relationally Dedekind-infinite. This is a natural finite-base preservation principle, not a new refutation of ordinary Maximalism: the standard infinite-individual maximalist root satisfies its type-e implication vacuously. It is consistent with □Functional Choice both when e is finite and when it is infinite.

### 25.3 Finite Hume classes without Plenitude

Define Equi_σ(R,X) by existence of a relational graph giving a bijection from the actual R-extension to the actual X-extension. Both graph arguments have type σ; the graph itself has type σσt, including when σ=e. No σσ operation is assumed. The following is a theorem of C:

    Nσn ∧ nR → ∀X[nX ↔ Equi_σ(R,X)].

For the forward direction, induct on n and pair one chosen point of R with one chosen point of X, applying the induction hypothesis to their deleted properties and adjoining the chosen pair to the resulting graph. At zero both extensions are empty. For the reverse direction, transport a finite-cardinality witness through the bijection: at a successor choose a point a of R, let b be its unique image, restrict the graph to R−a and X−b, and apply the induction hypothesis. The graph restriction is a bijection by the original totality, functionality, injectivity and surjectivity clauses. All selections occur inside one induction step proving an existential statement; no choice operation is constructed or required.

There is an explicit admitted operation

    #(R) := λX.Equi_σ(R,X)

of type (σt)νσ. If R is rigid and finite, choose n∈Nσ with nR. Under C5, Lemma 20.1 makes nR necessary, and C makes Nσn necessary. Necessitate the displayed C theorem and apply K to obtain □∀X[nX↔Equi_σ(R,X)]. Modalized extensionality identifies #(R) with n. Thus #(R) is its unique numerical cardinality without an invocation of Plenitude.

In particular, for rigid finite R,S,

    #(R)=#(S)  iff  Equi_σ(R,S).

Every realized numerical cardinality has this form: rigidify a finite witness by the C finite-haecceity construction. By Theorem 20.2, every number is either such a finite Hume class or bottom. Under Infinityσ every number is such a class; under a finite σ-domain the overflow value bottom is a number but is no such finite class.

The restriction to finite rigid properties is substantive. For arbitrary infinite rigid properties, the argument would need persistence of their equinumerosity, which has not been established here under C5. The operation # remains syntactically available on every property, but its identification with a Frege number is only claimed on the displayed domain.

## 26. Arithmetic noncollapse has a one-application definition already in C

This strengthens the compact-definition observation in §20. The equivalence with **actual Infinity** still needs C5 or the explicit numerical Null Collapse principle, but the equivalence with I* needs neither.

**Lemma 26.1 (C).** If m,n are natural cardinalities, m≠n, and Suc m=Suc n, then their common successor is the bottom cardinality.

By boxed Exclusivity, m≠n gives □∀X¬(mX∧nX). Numberhood of n is necessary. The necessitated successor-disjointness consequence of Swap, used in the recorded Max→Infinity_t proof, therefore gives

    □∀X ¬[(Suc m)X ∧ (Suc n)X].

NI makes the assumed identity Suc m=Suc n necessary. Thus □∀X¬(Suc m)X. Modalized Functionality identifies Suc m with the necessarily empty cardinality bottom_ν. Since successor preserves numberhood, N(bottom_ν) follows. No optional assumption has been fed into Logical Equivalence or necessitated; the necessary equality is supplied by NI.

**Theorem 26.2 (C).** For every counting type σ the following are equivalent:

    Iσ;
    I*σ;
    ¬Nσ(bottom_νσ);
    ∀n∈Nσ ◇∃X^{σt} nX.

The source gives I↔I*. Lemma 26.1 makes ¬Nbottom imply successor injectivity; zero is never a successor by a C theorem, so I* follows. Conversely under I*, successor has no numerical fixed point, by the ordinary N-induction derivable from its two Peano clauses. Since Suc(bottom)=bottom, bottom cannot be a number.

For the last equivalence use the C identity criterion

    n=bottom_ν  iff  □∀X¬nX.

The forward direction follows from NI and application; the reverse is Modalized Functionality. If bottom is not a number, every numerical n differs from bottom, so possibly some X has n. Conversely a numerical bottom would contradict the asserted possible realization. Thus I* says exactly that every natural cardinality is **possibly** realized. Infinityσ, by §7, says that every natural cardinality is **actually** realized. This distinguishes the two assertions without substituting an external ω for the internal numerical domain.

The simplest replacement for the original four-quantifier arithmetic noncollapse condition is therefore the single application

    ¬FiniteCardinality_σ(λX^{σt}.bottom).

It must not be shortened to ¬Nσ(0σ): zero and the bottom cardinality are different entities. The former counts empty properties; the latter counts none.

### 26.1 Possible realization does not imply possible genuine infinity

There is an explicit model of C with

    I*_e ∧ □¬Infinity_e.

Use the singleton-root variant of the coalesced construction, now with only the full one-world models having j individuals, for j=1,2,3,…, as its components. Choose one pointed individual in each component and send the sole root individual to it. The arbitrary-current-root component clause is the one verified by the recorded `coalesced-single-individual-root` model, citing Classicism (16 May 2023 draft), §2.6 pp.41–42 and n.61, Appendix E p.83. Completeness of the component family is needed for Maximalism but not for this construction to be a model of C; we do not claim Max at this restricted root.

As with the other free-root constructions, an admitted ν_e-property can have exactly the standard numeral denotations as its current extension. Hence N_e is standard at the root. Arbitrarily large finite components distinguish every pair of standard e-numerals, so their successors are also distinct and I*_e is true at the root. Its sole individual is carried to a chosen individual of each finite component. Quantifiers at a component range over that component's full domain; this is the action-model construction, not a constant-domain product semantics requiring a surjective map from the singleton root's individual domain.

Every world has finitely many individuals: the root has one and component j has j. At each, the corresponding standard finite cardinality witnesses failure of Infinity_e. Thus its negation is necessary at the root, while I*_e is true there. This is a new semantic separation verified from the recorded construction, not an already recorded model verdict and not a claim of literature novelty.

Consequently even “there could be a genuinely infinite individual domain” is stronger than the compact arithmetic condition in bare C. I* only requires unbounded possible finite-cardinality realization in the internal sense of Theorem 26.2. The stronger implication I*→Infinity established under C5 is precisely where the additional modal/domain regularity matters.

The final interpretive sentence in the recorded arithmetic-necessity write-up says that I* possibly holds “and so in particular that σ possibly has infinitely many members.” If “infinitely many” there means the actual Frege Infinity axiom rather than arbitrarily many possible finite members, the preceding restricted-root model supplies a correction to that interpretation. No source or database text has been edited; the formal Goodsell proof and its conditional arithmetic theorem are unaffected.

## 27. The numerical domain is always finite or Dedekind-infinite, already in C

This short argument was proposed by the parent lane and independently checked here. It is stronger than the initial finiteness observations in §25 and uses no C5, Choice or fullness assumption.

**Lemma 27.1 (finite successor path, C).** For every n∈Nσ there is a Frege-finite property A of νσ containing 0 and n, contained in Nσ, and successor-closed except possibly at n:

    A0 ∧ An ∧ ∀m(Am→Nσm)
       ∧ ∀m[(Am∧m≠n)→A(Suc m)].

Use the displayed existential assertion, together with Nσn, as the induction property. At zero take A={0}. For the successor step replace A by A′=A∪{Suc n}, which is finite by finite-adjunction. It contains zero and Suc n and is contained in Nσ. For closure away from Suc n, an old A-member m unequal to n uses the previous closure clause; if m=n, its successor is the newly adjoined point. The new point itself is the one permitted exception. This verifies the induction step even if Suc n was already in A or equals n. No uniqueness of predecessors or injectivity of successor is needed.

If bottom belongs to Nσ, apply Lemma 27.1 with n=bottom. Since Suc(bottom)=bottom, the exceptional endpoint is closed too. Hence A contains zero and is fully successor-closed; the definition of Nσ gives Nσ⊆A. Finite-subset closure yields Fin_νσ(Nσ).

Conversely, if bottom is not a number, Theorem 26.2 gives I*σ. The successor graph is then a total injective self-map of Nσ missing zero, so the recorded Dedekind lemma refutes Fin_νσ(Nσ). Therefore:

**Theorem 27.2 (C).**

    Fin_νσ(Nσ) ↔ Nσ(bottom_νσ) ↔ ¬I*σ ↔ ¬Iσ,

and, by classical negation,

    ¬Fin_νσ(Nσ) ↔ I*σ
                  ↔ Nσ is relationally Dedekind-infinite.

The last equivalence is exact: I* supplies the successor graph, while any Dedekind witness excludes finite Nσ and the first line then gives I*. There is no intermediate Frege-infinite but Dedekind-finite case for this particular inductively generated numerical domain, even in C without Choice. This does not assert the same dichotomy for arbitrary domains or arbitrary properties.

**Necessary-finiteness corollary.** If bottom is a number, number persistence makes that necessary. Necessitating the discharged C equivalences above therefore gives □Fin_νσ(Nσ). Moreover C proves Infinityσ→I*σ by actual realization, so its contrapositive gives Nσ(bottom)→Fin_σ(⊤σ), and the same reasoning gives □Fin_σ(⊤σ). Thus

    ¬I*σ → □Fin_σ(⊤σ) ∧ □Fin_νσ(Nσ).

The converse from necessary base finiteness is false, by §26.1's root with all finite individual worlds but I*_e true. Necessary finiteness of the numerical domain itself is equivalent to its current finiteness, since T supplies the reverse direction.

### 27.1 A last possibly realized cardinality

If Nσ(bottom), there is a number m different from bottom with Suc m=bottom. Induct on

    n≠bottom ∨ ∃m∈Nσ[m≠bottom∧Suc m=bottom].

The base uses 0≠bottom. At a successor, if the successor is not bottom use the first disjunct. If it is bottom and the predecessor is not bottom, use that predecessor as the witness. If the predecessor is bottom, the induction hypothesis already supplies a witness. Apply this to the numerical bottom to obtain the existential.

Thus ¬I*σ is equivalently the existence of a last possibly realizable cardinality m whose successor is impossible to realize:

    ∃m∈Nσ [m≠bottom ∧ Suc m=bottom].

The wording “possibly realizable” is justified by Theorem 26.2's general criterion m≠bottom iff ◇∃X mX. Moreover if mR holds at a world, R cannot leave an outsider: the fresh-point lemma would realize Suc m, contradicting its identity with bottom. Hence such an m could count the whole σ-domain, though it need not do so actually. This distinguishes a uniform last potential cardinality from the unbounded collection of finite possibilities in §26.1.

### 27.2 Comparison with C5 and Strong Possibility

Combining Theorems 20.2, 25.1 and 27.2 gives the following transparent division:

- In C, actual Infinityσ implies numerical Infinity of Nσ; the converse can fail even when no individual-infinite world is possible.
- Under C5, actual base Infinityσ, numerical Infinity of Nσ, I*σ, and ¬Nσ(bottom) are all equivalent.
- Under Strong Possibility, the individual domain is finite (indeed singleton), but N_e is Dedekind-infinite. Only 0_e and 1_e have current instances; the remaining numerical cardinalities form a Dedekind-infinite family of empty current extensions. On that family successor is injective, remains inside it, and misses 2_e, since its only numerical predecessor is 1_e under I*.

The final point is a precise conditional pathology of Strong Possibility, not a proof that Strong Possibility is inconsistent. Ordinary singleton-root Max models already exhibit the same finite-base/infinite-number-domain behavior without requiring Strong Possibility.

## 28. The exact finite-index caveat for countability

**Theorem 28.1 (C).** If Iσ fails, every property countable relative to σ is Frege-finite. Consequently Countable Boolean Completeness at every relational τ counted by σ holds, indeed necessarily.

By Theorem 27.2, ¬Iσ makes Nσ finite. The recorded Ctbl definition is equivalent to saying that the coded property is the range of a partial single-valued relation on Nσ (§8). Finite-image closure therefore makes its range finite. Every finite family in a Boolean algebra has a least upper bound, by finite-cardinality induction: the empty family has bottom as join, and adjoining one member takes a binary join. Thus CBC follows at each fixed τ. Numberhood of bottom is persistent, so necessitating these discharged C implications gives the boxed versions as well. No external ω or external choice of codes has been used.

The converse “every finite property is countable relative to σ” is false when Nσ is finite and too small. For instance, in the full extensional model with a singleton individual domain, N_e has three elements (0,1,bottom), while many higher type domains have more than three entities. A property containing four distinct entities is finite but not Ctbl relative to e, by the finite pigeonhole principle.

There is a useful explicit range of finite-index models. Fix an external positive integer K and take the singleton free-root construction of §26.1, but retain only the full one-world components with j=1,…,K individuals. Its root has exactly one individual. At that root the e-numerals 0,…,K are distinct, because the K-individual component distinguishes them by their finite extensions. Every numeral above K is necessarily empty, at the singleton root and all its components, and hence equals bottom. The arbitrary root-extension predicate again makes N_e exactly the standard numeral denotations; therefore

    |N_e(root)| = K+2.

All current relations are available as root truth extensions. Accordingly a root property is Ctbl relative to e exactly when its current extension has at most K+2 elements, by the usual finite injection criterion. In particular the same actual singleton individual domain supports arbitrarily large, but finite, numerical countability indices as K varies. With all finite components retained, §26.1 gives an infinite numerical index while still keeping every individual world finite.

These are external cardinal calculations in explicitly specified models, not an assertion that every internally finite numerical domain has an externally standard finite size. They show why the unqualified word “countable” is misleading unless the arithmetic index is known to satisfy I*, and why the actual size of the chosen counting base is not by itself enough to determine that index in bare C.

## Additional reference and audit notes for §§23–28

The independent world-cardinality lane checked the standard-root Sum/Prod argument in §24.2 and the bare-C equivalences in §26. The proof of the finite-path lemma in §27 came from the parent lane and was checked here. These are agent audits, not human verification or Lean certificates.

The standard computability facts used in §24.3 are stated in Andrew Marks, *Computability Theory*, 25 February 2024, Theorem 16.7 (Post's hierarchy theorem), printed pp.68–69, and Definition 16.10 immediately after: [author-hosted notes](https://math.berkeley.edu/~marks/notes/computability_notes_v1.pdf). The arithmetic and Maximalist applications here are new derivations, not claims made in those notes.

The independently prepared `/tmp/classicism-research/max-degree.md`, §§10–11, also obtains the whole Max theorem set's exact degree using a definable oracle predicate, and strengthens it to robust lower bounds for consistent effective extensions. Section 24 here gives a complementary reduction using ordinary arithmetical Σ₂ sentences and therefore also classifies the arithmetic consequence set. Overlap between the notes should not be represented as separate independent literature discoveries.

## 29. Max's arithmetic is strictly stronger than PA plus all true Σ₂ sentences

This answers the narrower comparison question, not a complete classification of Max's arithmetic consequences. The actual satisfaction construction below was independently checked by the relational-core lane, with particular attention to internal formula codes, assignment guards and the absence of Choice, Plenitude or BF. No literature novelty is claimed.

Fix one counting type σ and interpret arithmetic on Nσ. Write T₂ for the ordinary external first-order theory

    PA + all standard-true Π₁ sentences.

Its deductive closure is also the closure of PA plus all standard-true Σ₂ sentences: a true Σ₂ sentence has a standard witness leaving a true Π₁ instance, while each Π₁ sentence can be written as a Σ₂ sentence by a dummy existential quantifier. This assertion concerns deductive closure, not an internal arithmetical truth predicate.

We will exhibit a particular Π₂ sentence G₂ such that

    C ⊢ Iσ→G₂^σ,       Max(C) ⊢ G₂^σ,       T₂ ⊬ G₂.

Here G₂^σ denotes the fixed Frege translation. Thus Max's arithmetic consequence theory properly extends T₂. The gap already comes from the impredicative arithmetic available in C+I, rather than from an additional modal Max instance tailored to G₂.

### 29.1 Current arithmetic comprehension and coding

Under Iσ the source supplies first-order PA, with Sum and Prod as functional graphs. The definition of Nσ supplies induction for every admitted property of numbers, including properties defined with higher-order quantifiers. Lambda abstraction supplies comprehension for every such formula. Interpret set equality extensionally, as agreement on Nσ, rather than identifying coextensive intensional entities. These resources give the ordinary impredicative second-order arithmetic argument needed below. No modal operator occurs inside the construction, and no instance of numerical BF or NCOLL is used.

Use standard natural-number coding of first-order arithmetic formulas, terms, finite proofs and finite assignments. The relevant parsing, substitution, depth, assignment-update and term-evaluation functions have PA-provably total recursive graphs. All references to these functions can be eliminated in favor of their graphs, so no choice of an object-level operation is required. Their numerical output type νσ is relational in any case.

An assignment is a coded finite sequence of numerical values, read as zero outside its length. Updating any variable pads the sequence when necessary. This represents every assignment to the finitely many free variables of a coded formula. Guard all satisfaction predicates by well-formedness of the formula and validity of its assignment code. We quantify only over Nσ for syntactic codes and values.

### 29.2 Partial satisfaction and gluing, including nonstandard codes

Let PSat(R,k) say that the admitted relation R(f,s) is supported on well-formed formula/assignment pairs with formula depth at most k and satisfies the usual Tarski clauses there: atomic formulas by term evaluation; Boolean connectives by their truth tables; and

    R(∀v φ,s) ↔ ∀a∈Nσ R(φ,update(s,v,a)).

All subformulas in a recursive clause have smaller depth. PSat is one formula of the higher-order language with numerical k and a relation parameter R; it is not an external sequence of separate clauses indexed by standard k.

By Nσ-induction, for every internal k there exists R with PSat(R,k). At depth zero the relation is given directly by the atomic evaluation clause. Given a relation at depth k, define R′ on formulas of depth at most k+1 by applying one compositional clause to that relation on the immediate subformulas. On old formulas of depth at most k, R′ agrees with R because R already obeys its clauses. On formulas of depth k+1, the immediate subformulas have depth at most k, so this agreement verifies the required clauses for R′. Comprehension supplies R′. This is an induction proving existence, not a choice of a sequence of partial satisfaction relations.

Uniqueness and compatibility follow by a separate depth induction: if PSat(R,k) and PSat(S,l), then R and S agree on all valid pairs of depth at most min(k,l). At a universal quantifier, the induction hypothesis already applies to every updated assignment, so their universal clauses agree. The assertion being inducted includes the quantifiers over R,S, formula codes and assignment codes; its abstract is admitted.

Now use impredicative comprehension to define

    Sat(f,s) := valid(f,s) ∧ ∃R[PSat(R,depth(f)) ∧ R(f,s)].

Existence of partial satisfaction and compatibility make this a full compositional satisfaction relation. To check a clause for f, choose one partial relation at depth(f); compatibility identifies its values on every immediate subformula and every updated assignment with the displayed global Sat. The guards prevent unconstrained entries of partial relations from entering the definition.

This covers all **internally coded** formulas, including nonstandard codes in a nonstandard arithmetic model. The depth induction was internal and its existential induction property is permitted by full higher-order comprehension. Nothing here presumes that every internal formula has externally standard finite depth.

For each externally fixed first-order formula A, ordinary structural induction gives the disquotation equivalence for its code and all coded assignments. In particular Sat agrees with A itself on its closed code. This does not violate Tarski: Sat is a newly available higher-order relation; no first-order arithmetical formula defining arithmetic truth has been produced.

### 29.3 A controlled presentation of T₂

Fix one Σ₁ arithmetic formula H(e) expressing that machine e halts on input e, and put NH(e):=¬H(e). Present T₂ by PA and the sentences NH(numeral e) for all standard e whose machines do not halt. Every true Π₁ sentence is PA-equivalent to one such negative-halting sentence by the usual effective Σ₁ normal-form compilation, so this is a presentation of the same deductive closure.

This presentation avoids a casual assumption that uniform truth for arbitrary bounded formula codes is itself a bounded predicate. There is a fixed Π₁ formula NH, and the syntax test “this is the code of NH(numeral e)” is effectively decidable. Choose the ordinary coding so that e is recoverable from that syntactic pattern. The axiom predicate Ax₂(c) is therefore Π₁ (using PA's provably total coding graphs), and the finite-proof relation is Π₁. Hence

    Pr₂(c) := ∃p Proof₂(p,c)

has a Σ₂ definition. In the standard model it defines exactly the T₂ theorem relation.

The satisfaction relation from §29.2 agrees uniformly with the coded sentences NH(numeral e): numeral evaluation is verified by N-induction, and then the compositional clauses for the single fixed formula NH give

    Sat(code(NH(numeral e))) ↔ NH(e).

This statement ranges over all internal e. No appeal to the external truth of any one negative-halting assertion is made in proving it.

### 29.4 Internal proof soundness

C+I proves that every PA axiom is Sat-true. The induction-axiom case works even for internally nonstandard formula codes: for such a code f and assignment s, instantiate N-induction with the admitted property

    λn.Sat(f,update(s,v,n)).

Its base and successor hypotheses are exactly those expressed by satisfaction of the antecedent of the coded induction axiom. The resulting universal conclusion is exactly its consequent. The ordinary logical axioms and inference rules are sound by the compositional clauses, with validity quantified over assignments.

The extra Ax₂ axioms are sound as well. Their axiom condition includes NH(e), and the preceding uniform fixed-formula agreement makes the corresponding coded sentence Sat-true. Induction on the internally coded proof length therefore yields

    ∀c [Pr₂(c)→Sat(c)]

for sentence codes c. This is current semantic soundness relative to the constructed higher-order relation. It does not claim that an arbitrary C+I model is externally standard or that its internally evaluated Ax₂ predicate agrees with the external axiom set on every nonstandard code.

### 29.5 The separating Π₂ sentence

Choose the complexity-preserving Gödel fixed point for Pr₂:

    PA ⊢ G₂ ↔ ¬Pr₂(⌜G₂⌝),             G₂ ∈ Π₂.

The same coding justification as §24.4 applies. Externally T₂ is consistent and contains every standard-true Σ₂ sentence. If T₂ proved G₂, then Pr₂(⌜G₂⌝) would be a true Σ₂ sentence and therefore also a T₂ theorem, contradicting the fixed-point equivalence. Thus T₂ does not prove G₂, and G₂ is standard-true.

Internally, C+I proves Pr₂(⌜G₂⌝)→Sat(⌜G₂⌝) by §29.4, and Sat(⌜G₂⌝)↔G₂ by disquotation for the fixed sentence G₂. The PA fixed-point equivalence then makes Pr₂(⌜G₂⌝) contradictory. Therefore C+I proves ¬Pr₂(⌜G₂⌝), and hence G₂.

This proves the displayed separation. Since Max includes I and every C theorem, it proves G₂; since it includes PA and every true Π₁ sentence, it contains T₂. Its arithmetical theory is therefore a **proper** extension of PA plus all true Σ₂ sentences.

The construction also proves the formal Con(T₂) statement from C+I, because a T₂-proof of 0=1 would contradict its Sat-soundness. However the strictness proof above uses the Π₂ Gödel sentence and semantic reflection directly. It does not rely on an unaudited equivalence between Con(T₂) and uniform Σ₁ reflection for PA, or on a generalized second-incompleteness theorem for a noneffectively axiomatized theory.

This argument constructs truth only for the single first-order arithmetic signature. It does not construct a satisfaction relation uniformly for every type of C, and it does not prove C+I's own consistency. Thus it does not conflict with §18.5's ordinary Gödel obstruction for the effective arithmetic shadow of C+I.

## 30. Natural consistency separators at every fixed truth level

The satisfaction construction has a useful natural strengthening of §29's specially chosen Gödel sentence. For each **externally fixed** integer k≥1, let

    U_k := PA + all standard-true Π_k sentences.

Thus U_1 is the theory denoted T₂ in §29. Fix its usual arithmetical proof presentation, whose axiom condition is Π_k, proof condition Π_k, and theorem predicate Pr_k is Σ_{k+1}. Let

    Con_k := ¬Pr_k(⌜0=1⌝).

This is a Π_{k+1} sentence. For every fixed k and counting type σ,

    C ⊢ Iσ → Con_k^σ,
    Max(C) ⊢ Con_k^σ,
    U_k ⊬ Con_k.

Consequently the arithmetic of C+I, and hence that of Max, is not contained in any one of the theories PA+true Π_k. This is a statement about each fixed finite complexity level. It does not say that Max contains all those theories.

### 30.1 Presentation and internal semantic soundness

For a completely controlled presentation, choose a fixed universal Π_k formula Q_k(e). Arithmetic normal-form compilation ensures that every Π_k sentence is PA-equivalent to one instance Q_k(numeral e). Use PA plus those instances for which Q_k(e) holds as the axiom condition. Parsing the instance and recovering its numerical index can be done with the usual provably total coding graphs. The presentation can be chosen so that the resulting axiom predicate is Π_k. It presents U_k in the standard model.

The Sat relation of §29.2 satisfies, uniformly in internal e,

    Sat(code(Q_k(numeral e))) ↔ Q_k(e).

This uses numeral-evaluation induction and the compositional clauses for the single fixed formula Q_k. It does not require a first-order truth predicate uniform over k, nor the unsupported assertion that truth for arbitrary bounded formula codes is a bounded formula. The fixed formula Q_k can have nonstandard numerical arguments; its syntactic complexity is externally fixed.

The PA-axiom argument from §29.4 is unchanged. The extra axiom condition Q_k(e) makes its coded instance Sat-true by the displayed equivalence. Internal proof-length induction therefore gives

    C+Iσ ⊢ ∀c[Pr_k(c)→Sat(c)]

for sentence codes. Since Sat makes 0=1 false, this proves Con_k. This part uses the same current higher-order comprehension and N-induction as §29. No BF, NCOLL, Plenitude, Choice or external standardness of a model is needed.

### 30.2 Why U_k cannot prove this natural consistency statement

For clarity, the needed non-r.e. derivability facts have a direct published source. Artemov and Beklemishev, *Provability Logic*, §8.3, Propositions 120–122, printed p.83, establish provable Σ_{k+1}-completeness, the Bernays–Löb derivability conditions for provability in T+true Π_k, and equivalence of its consistency statement with uniform Π_{k+1} reflection over T. Their presentation takes an elementary presented base T; use a standard elementary presentation of PA. [Author-hosted text](https://sartemov.ws.gc.cuny.edu/files/2012/10/Artemov-Beklemishev.-Provability-logic.pdf).

Here is the relevant incompleteness argument, rather than an appeal to ordinary r.e. Gödel II where its hypothesis fails. Write P(A) for Pr_k(⌜A⌝). The proof predicate satisfies:

1. If U_k proves A, then U_k proves P(A).
2. PA proves P(A→B)→(P(A)→P(B)).
3. PA proves P(A)→P(P(A)).

For the controlled presentation in §30.1, (2) is coded proof concatenation. Provable Σ_{k+1}-completeness proves (3): a Σ_{k+1} assertion has the form ∃xπ(x), with π Π_k; a witness makes the corresponding Π_k numeral instance an available axiom, from which a proof of the existential can be uniformly coded. Condition (1) follows for each fixed finite U_k proof from its finitely many true Π_k axiom instances and the corresponding proof code. Thus no recursive enumeration of all U_k axioms is presumed.

Take a Gödel fixed point G with PA proving G↔¬P(G). Derivability applied to G→¬P(G), together with (3), gives

    U_k ⊢ P(G) → P(0=1).

Indeed P(G) implies both P(P(G)) and P(¬P(G)), and a coded propositional contradiction yields P(0=1). Hence U_k proves Con_k→¬P(G), and therefore Con_k→G. If U_k proved Con_k, it would prove G and then P(G) by (1), contrary to G→¬P(G). The external theory U_k is consistent because every one of its axioms is standard-true. Therefore U_k does not prove Con_k.

For k=1 this makes the strict separator especially natural:

    Max(C) ⊢ Con(PA+true Π₁),
    PA+true Π₁ ⊬ Con(PA+true Π₁).

This Π₂ statement is also the usual 1-consistency assertion for PA, or equivalently the uniform Π₂-reflection principle for PA with the above standard presentation. It should not be called ω-consistency; those are different notions. The original Gödel-sentence proof in §29 remains valid independently of adopting this reflection terminology.

### 30.3 The exact comparison with the finite true-arithmetic fragments

Section 24.4 produced a standard-true Π₂ sentence G_Max that is not a theorem of Max's arithmetic consequence theory. Its proof used that this consequence theory has a Σ₂ theorem predicate and contains every true Σ₂ sentence; the standard-root model supplied soundness.

Every U_k with k≥2 contains G_Max, since it contains all true Π₂ sentences. Thus U_k is not a subtheory of Max's arithmetic consequences. Conversely Max proves Con_k by §30.1, whereas U_k does not prove Con_k by §30.2. Therefore Max's arithmetic consequence theory is not a subtheory of U_k either. We obtain the precise comparison:

- For k=1, Max's arithmetic consequences properly contain U_1, equivalently PA plus all true Σ₂ sentences.
- For every fixed k≥2, Max's arithmetic consequence theory and U_k are incomparable under deductive inclusion.

All these are claims about the ordinary external first-order arithmetic consequence theories under the fixed Frege interpretation. They do not assert that all Max models have standard arithmetic, nor that one arbitrary Max model satisfies all the standard-true Π_k axioms. At this stage these fragment claims did not classify Max's entire arithmetic theory. The exact candidate involving the arithmetic shadow of C+I and true Π₁ is subsequently established, with its additional interpretation dependencies, in §37.

## 31. Rigid powers preserve finite versus infinite size in bare C

The finite-rigid-power theorem in §25.1 has a choice-free converse. For any admitted property A^σt, write

    RP(A)(Y) := Rigid(Y) ∧ ∀x(Yx→Ax).

Then bare C proves

    Fin_{σt}(RP(A)) ↔ Fin_σ(A).

The forward direction uses the graph Y=H_a of the haecceity assignment on a∈A. Every H_a is rigid and supported on A. Haecceities are injective: H_a=H_b implies a=b by evaluation at a. Equivalently, the partial relation taking a singleton property Y=H_a to its unique member a has A as its range. If RP(A) is finite, finite-subset and finite-partial-image closure make A finite. This uses a graph whose output type can be e; it does not introduce an inadmissible e-valued function type. The reverse direction is precisely §25.1.

Therefore every fixed finite iteration of the rigid-power construction preserves Frege finiteness and Frege infinitude. No Choice, RC, C5 or external cardinal convention is needed for this dichotomy. The implication from finiteness of a rigid power to finiteness of the base was pointed out independently by the relational-core lane.

For a finite base, the proof gives more than a finiteness bound: RP(A) represents every actual subset of A uniquely. Existence follows because every subset of a finite property is finite and hence admits a rigid coextension in C; uniqueness follows from the C theorem that rigid coextensive relations are identical. If A=B∪{a} with a outside B, RP(A) is the disjoint union of the images Z↦Z and Z↦Z∨H_a of RP(B). Each map is injective, and the images are disjoint according to truth at a. Consequently, in any model where A has external standard finite size n, RP(A) has exactly 2^n elements. The internal theorem above does not require that a Frege-finite property have externally standard finite size.

This separates two roles that should not be conflated: finite-subset representation already follows in C; RC supplies rigid representatives for arbitrary admitted subsets, which permits the unrestricted Cantor diagonal in the separate numerical-core analysis.

## 32. A precise limitation of the arithmetic-potentialism analogy

This section records a research constraint, not a characterization theorem for Max.

Hamkins, *The modal logic of arithmetic potentialism and the universal algorithm*, arXiv:1801.04599v5, Lemma 2, pp.6–7, characterizes arithmetic end-extension possibility over a c.e. PA extension by consistency with the current model's Σ₁ theory. But Theorem 5, p.9, also shows that the full arithmetic extension frame modally defines the standard cut and therefore violates induction for modal formulas in every nonstandard model. [Primary text](https://arxiv.org/pdf/1801.04599).

Apply only the first statement externally to the effective arithmetic shadow Tσ={A:C⊢Iσ→A}. If an arithmetic model M satisfies Tσ and all standard-true Π₁ sentences, its Σ₁ theory is the standard Σ₁ theory: true Σ₁ sentences are already PA theorems, and false ones are excluded by the true Π₁ axioms. Accordingly every Tσ-consistent arithmetic sentence can be realized in an arithmetic end-extension of M.

This observation is suggestive for the possible exact-shadow candidate

    Th_arith(Max(C)) ?= deductive closure(Tσ + true Π₁).

It does not prove that candidate. A C model must validate induction for every admitted predicate of numbers, including predicates with modalities. The full end-extension frame over a nonstandard arithmetic model fails precisely this requirement. Nor does an arithmetic end-extension automatically extend all the relational types and lambda abstractions of C. One would need a separate restricted Henkin construction preserving the desired current arithmetic while satisfying C and all Max instances. No such construction is supplied here.

In particular, Hamkins's arithmetic maximality principle is the principle that every possibly necessary arithmetic sentence is already true. It is distinct from this project's pure Maximalism, whose instances assert possibility of C-consistent pure sentences. The names and the shared S4 setting do not justify identifying their models or theorem sets.

## 33. Detailed singleton finite-fan model and verified structural flags

This makes §26.1's separation explicit and distinguishes it from the already recorded `coalesced-all-finite-individual-domains` model. That recorded model uses **all threads** as root individuals and consequently has an actually infinite individual root. The present variant uses exactly one root individual. Its source construction is the singleton-root alternative in *Classicism*, Appendix E p.83, also cited by `coalesced-single-individual-root`; the new choice of component family and the verdicts below are the present argument.

### 33.1 Worlds, domains and evaluation

For every positive external integer j, let M_j be the full one-world extensional model with D_e^j={1,…,j}. All its relational types are full finite function domains, ultimately ending in the two truth values. Fix a distinguished a_j∈D_e^j. Add a root r with D_e^r={a}, and send a to a_j along the distinguished arrow r→j. Each component has only its identity arrow. The root also has its identity arrow.

At every relational type τ=σ₁…σ_l t, write A_r=∏_iD^r_{σ_i} and A_j=∏_iD^j_{σ_i}; for t these are singleton tuple spaces. The free root domain has the form

    D^r_τ = P(A_r) × ∏_{j≥1} P(A_j).

A root entity X is represented by its arbitrary current extension X_r and its component extensions X_j. Application is coordinatewise, with the component application using the component images of arguments. The map D^r_τ→D^j_τ is onto at each relational type. The map D_e^r→D_e^j is generally not onto.

Quantifiers at j range over the full local domain D^j_σ, not merely over images of root entities. In particular, the individual quantifier at j ranges over all j individuals. Quantifiers at r range over D^r_σ. Lambda abstraction has its current truth extension determined by the root evaluation, and its j-th coordinate by the corresponding local abstraction in M_j. Every such family is admitted. These are precisely the local-domain clauses of the singleton-root coalesced action model. The construction theorem supplies validity of C. The completeness of a family of components is required to obtain Max, not to obtain C; this family is deliberately restricted and is not complete for C.

The displayed product description is not an attempt to prove ordinary unboxed Functionality. That optional principle can fail here: operations can agree on all current individuals while differing on future individuals outside the image of the singleton root. Modalized Functionality, the C theorem, evaluates the necessary universal condition using the full local domains and remains valid.

### 33.2 Numerical and infinitude facts

At any root type σ, arbitrary current extensions include the predicate whose extension consists exactly of the standard numeral denotations. It contains zero and is successor-closed, so the impredicative Nσ has precisely those denotations as its root extension. For σ=e, arbitrarily large finite components distinguish every two different standard numerals. For relational σ, the root domain is infinite and full current extensions contain properties of every standard finite size, which distinguish the numerals directly. Therefore the root arithmetic at every type is standard and satisfies I*σ, hence Iσ. Addition and multiplication are standard by the current full-relation argument in §24.2.

The root has exactly one individual, so ¬Infinity_e. Component j has exactly j individuals, so ¬Infinity_e there too. Thus

    r ⊨ I_e ∧ □¬Infinity_e,

or equivalently I_e∧¬◇Infinity_e. Every relational root domain contains an injection of D_t^r=P({r,1,2,…}) by constant relations, so it is infinite; standardness of Nσ then gives Infinity_σ for each relational σ. At every component every fixed type domain is externally finite. In particular, no component supplies a genuinely infinite domain at any fixed type.

For each external k≥1, the sentence saying there are exactly k individuals is possible at r, witnessed by M_k. This external schema and I_e must not be silently replaced by the possibility of an actually infinite individual world.

### 33.3 Positive structural flags, with scope checked

At the root, Boolean order at τ is inclusion in every coordinate of the displayed product. Therefore the Boolean algebra is a product of full powerset algebras.

**Boolean Completeness, Atomicity and Strong Leibniz, all boxed.** Coordinatewise intersections and unions give the bounds of every admitted root family. Every nonzero entity contains a singleton in some coordinate. That coordinate singleton is an atom; its image at a component is either a local singleton or bottom, and hence necessarily settles every local entity. Thus every nonzero entity has a strong world below it. The one-world components satisfy the same principles. Consequently □BC, □Atomicity and □Strong Leibniz hold at every relational type. These boxed verdicts are checked at every world, not obtained by necessitating root hypotheses.

**Rigid Comprehension, boxed.** Given a current root extension S⊆A_r, define Y_r=S and Y_j=π_j[S], where π_j maps each root tuple to its component tuple. This is an admitted relation. Every root instance remains an instance at every component, so Y is persistent. If a relation Z is necessary of every current Y-instance, it contains S at the root and contains π_j[S] at component j; hence Y≤Z. The local inextensibility condition at each one-world component is automatic. Thus Y is rigid and currently coextensive with S. The argument does not need the tuple projections to be onto. Every component is extensional, so □RC holds at every relational type.

**Relational Choice and well-ordering, boxed, in the ordinary choice metatheory.** Every current root relation is available. A metatheoretic choice of a witness in each nonempty current fiber can therefore be represented by an admitted root graph, with arbitrary component coordinates. Likewise each root domain can be well-ordered by an admitted current graph. The components are full finite models. Thus the Relational Choice and well-ordering schemas hold at every world. These semantic flags use the ordinary metatheoretic axiom of choice for arbitrary root sets; the earlier internal C proofs did not use it.

**Barcan: exactly the relevant type distinction.** For every relational quantified type τ, projection D^r_τ→D^j_τ is onto. Therefore ∀x^τ□Xx at the root implies that X is universal in each component, and hence □∀x^τXx. BF_τ holds at r and trivially at each component, so □BF_τ holds for each relational τ. In contrast BF_e fails at r. Let X have X_r={a} and X_j={a_j}. Then ∀x^e□Xx is true at r, while ∀x^eXx fails in each component j≥2. Hence the full BF schema and its boxed version fail.

### 33.4 Negative flags and limits

ND_e holds at the singleton root vacuously and at every extensional component, so □ND_e holds. ND_t fails at the root: a nonzero proposition supported at one component is distinct from bottom at r but becomes bottom at a different component. The same failure occurs at every relational type by taking constant relations. Thus the all-type ND schema fails, and so do C5 and □Plenitude.

Numerical Null Collapse and Numerical Extensionality at e fail. The standard numerals 2_e and 3_e are distinct, but both have empty current extensions because the current individual domain is singleton. The numerical domain N_e itself is Dedekind-infinite by I_e, despite the finite individual base.

Max fails, since Infinity_e is C-consistent but its possibility is false here. Strong Possibility also fails since it implies Max. No verdict of Max or Strong Possibility is imported from the complete-component singleton construction.

The root-marker proposition supported only at r shows that the distinctness-preserving modality collapses to truth at r. For any true p use that marker q in ∃q[q∧□(◇q→p)]; ◇q holds only at r. Conversely the displayed box-ne definition implies p by T. Thus Box_ne p↔p and its dual holds at the root. This is a further verified structural fact, not a consistency argument for Strong Possibility.

These are semantic facts about this explicit full-at-each-local-extension action model. They are not claims that every Henkin C model has these powersets, that C proves these structural schemas, or that the database already records the singleton finite-fan variant.

## 34. Why the standard-cut obstruction does not currently refute Strong Possibility

Here are the exact premises of the analogy in §32. Let T be a fixed consistent c.e. extension of PA, enumerated by standard finite fragments T_k. In the full arithmetic potentialist system containing every T-model and every arithmetic end-extension, Hamkins's Theorem 5 identifies the standard cut in each model M by the modal predicate

    B(k) := “Con(T_k) holds in every T-end-extension of M.”

For externally standard k, every T-model satisfies Con(T_k), by finite-fragment reflection. For nonstandard k, the full system supplies an end-extension falsifying Con(T_k). Thus B holds exactly at the externally standard numbers. In a nonstandard M this is a proper successor-closed subset containing zero, so induction for B fails. The result uses the full extension relation and permits the numerical parameter k in the possibility assertion. It is not a theorem about arbitrary S4 accessibility relations.

C, in contrast, has N-induction for every admitted numerical predicate, including λk.□(Iσ→Con(T_k)). Therefore a C model with nonstandard Nσ cannot have exactly this full arithmetic access pattern. The fact that a particular ordinary end-extension exists does not by itself make it accessible in a C action model, with compatible higher-type entities and lambda abstractions.

Strong Possibility supplies a different schema:

    Diamond_ne P,  for each closed pure P consistent with Max(C).

Its premise is consistency with Max(C), not merely consistency with C+Iσ or with an arithmetic T. Its target has no free numerical parameter, and its modality is Diamond_ne rather than an independently stipulated relation of all arithmetic end-extensions. In particular it does not directly supply, for each particular nonstandard current k, an accessible arithmetic world in which that very k indexes an inconsistent finite fragment. A closed existential possibility could introduce a new numerical witness; distinctness preservation alone does not make that witness equal to the image of a specified current parameter.

No argument here establishes the stronger parameter-by-parameter extension property from Strong Possibility. Consequently the standard-cut theorem gives no present inconsistency proof for Strong Possibility. It specifies an obstruction that any proposed semantic construction must avoid.

There is also a useful conditional compactness check. If Strong Possibility is consistent in the project's finitary Henkin/action semantics, it has a model with nonstandard Nσ at every fixed chosen counting type. Add one fresh constant c^νσ, assert Nσc and c≠n for each standard numeral n. Every finite subset is satisfiable in a Strong Possibility model by choosing a sufficiently large numeral, since Strong Possibility implies Max and I*σ. Compactness gives a model of the whole expanded theory; forget the fresh constant afterward. Its reduct is a Strong Possibility model with a nonstandard numerical element. This is a conditional Henkin-model argument, not an existence proof of Strong Possibility and not a compactness claim for full standard higher-order semantics.

Thus it would be especially unsafe to argue that Strong Possibility avoids the modal-induction obstruction by forcing all its arithmetic models to be standard. If it is consistent, compactness supplies nonstandard ones. What must be restricted is the accessible-world structure or its arithmetic extension behavior, not the availability of nonstandard Henkin arithmetic itself.

## 35. Current extensional quotients and arithmetic conservativity of boxed Plenitude

This section concerns ordinary first-order arithmetic consequences in the finitary Henkin/action semantics of C. It does not claim conservativity for modal formulas, for arbitrary higher-order sentences, or for full Functional Choice. Its counting base is e on both sides.

**Theorem 35.1.** For every ordinary first-order arithmetic sentence A,

    C+I_e ⊢ A^e    iff    C+□Plenitude+Infinity_e ⊢ A^e.

Here all the schemata in C and □Plenitude retain their original type scope, and A^e is the usual Frege arithmetic translation. The reverse-to-premise inclusion is immediate: Infinity_e implies I_e. The substantive direction is an extensional Henkin countermodel transfer, described in detail below.

### 35.1 Representatives, current equivalence and domains

Let M be a Henkin/action model of C at a point r satisfying I_e and falsifying A^e. Only the current evaluation at r is used for the quotient. Put ν=(et)t, and translate types recursively by replacing e with ν and leaving t fixed. Since the original types are relational, all translated types remain admitted. Write a superscript dagger for this metalinguistic type translation.

Define formulas D_τ and E_τ giving admissible representatives and current equivalence, recursively on the original type τ. At the bases,

    D_e(a) := N_e(a),                 E_e(a,b) := a=b,
    D_t(p) := ⊤,                     E_t(p,q) := (p↔q).

Thus truth-type representatives are **all** ambient propositions, identified by their current truth value. They need not themselves equal ambient ⊤ or ⊥. There are exactly two current E_t classes, represented by those two propositions.

For a relational type τ=σ₁…σ_l t with l≥1, D_τ(F) says both:

- F is currently false outside tuples satisfying every D_{σ_i};
- on admissible tuples, its current truth is invariant under componentwise E_{σ_i}.

Define E_τ(F,G) as current agreement of F and G on all admissible argument tuples. Each formula is finite at a fixed type and is an admitted C formula. Recursively E_τ is an equivalence relation on D_τ. Let the new domain be

    D^E_τ := {a∈D^M_{τ†}: M,r⊨D_τ(a)} / E_τ.

For τ=e the equivalence is ordinary current identity on N_e(M). For τ=t it gives two truth values. At each relational type, an equivalence class is literally an extensional relation on the product of the lower quotient domains. Support eliminates irrelevant values outside the represented domain, and invariance makes the relation independent of representatives.

Currying is compatible with this construction. If F represents an admissible relation of type στ and a is an admissible σ representative, then the ambient partial application Fa represents an admissible τ relation. Equivalent F and a give equivalent results. When τ=t, admissibility is automatic, and the result is evaluated by its current truth class.

### 35.2 Henkin comprehension and the extensional C model

Translate equality of the new τ-sort by E_τ and quantify only over D_τ representatives. Translate application by ambient application and truth by current truth. An induction on formulas proves that satisfaction is invariant under changing representatives. For a lambda abstraction, take the ambient abstraction of the translated body and conjoin the admissibility guards for all its displayed arguments. That current relation is supported and invariant, so it belongs to the indicated quotient domain. This proves closure under every lambda abstraction with parameters and hence the required Henkin comprehension.

Interpret the logical constants by these same guarded translations. The result E is a classical extensional Henkin model in the original relational type system, with individual domain N_e(M). Identity is extensional equality of actual quotient relations; functions with identical application behavior are identical. The usual soundness verification for extensional Henkin models therefore validates C: all H axioms and rules hold, and H-equivalent lambda bodies determine the same extensional relation, validating Logical Equivalence. Equivalently, use the extensional Henkin model construction of *Classicism*, §3.2, Definition 3.6 and Proposition 3.7, pp.47–48, after the closure verification just supplied.

The modal abbreviation in E is trivial: since the proposition domain has two elements, p=⊤ has exactly the same truth value as p. Thus □ and ◇ both act as the identity on truth values. This does not change M or assert that its original modality was trivial; E is a newly constructed model using M's current extensional information.

### 35.3 Plenitude in the quotient needs no choice

Every extensional Henkin model closed under the relevant lambda abstractions satisfies Plenitude for relational outputs. Suppose U^{στt} is total and single-valued in E, where τ=ρ₁…ρ_k t. Define

    X := λx^σ y₁…y_k. ∃z^τ[(Ux)z ∧ z[y₁…y_k]].

This is an admitted operation of type στ. For any x, choose a witness z only within the proof for that fixed x. All U-related outputs are identical by the uniqueness premise, so Xx is coextensive with z, hence identical to z in E. Therefore (Ux)(Xx). For τ=t the same definition has an empty tuple of y-arguments and works with the two truth values. No operation with output e is introduced, and no choice function has been assumed.

So E satisfies every Plenitude instance. Since its modality is trivial, it satisfies □Plenitude as well. This argument establishes unique-output representation; it does not select an output from an arbitrary nonempty fiber, and therefore does not prove Functional Choice.

### 35.4 Individual infinity and recovery of the original arithmetic

The individual domain of E is the current N_e domain of M. Its zero and successor graph, inherited from M, satisfy the Peano clauses under I_e. They are admitted relations in E: their ambient definitions have numerical guards and depend only on current identity of numerical arguments. Every admitted E-property of individuals pulls back to an admitted property of N_e in M. Consequently E satisfies second-order induction, with parameters from its entire Henkin hierarchy, for this inherited individual Peano system.

The inherited successor graph is injective and omits zero. It therefore gives a relational Dedekind witness on E's individual domain. The C finite-cardinality lemma excludes any finite cardinality of that whole domain, so E satisfies Infinity_e.

It remains to compare this inherited individual Peano system with E's own Frege natural cardinalities. This is essential: the target arithmetic A^e uses the latter, not an arbitrarily named individual successor structure.

Use the inherited Peano order on E's individuals. Let L_a be its strict initial segment below a, and relate a to a Frege number n exactly when n counts L_a. Second-order induction on the inherited individual Peano system proves that every L_a has a natural cardinality: the zero segment is empty, and the successor segment adjoins its predecessor as a fresh point. Conversely Frege N-induction proves that each Frege number counts some L_a, again using these zero and successor clauses.

A fixed segment has a unique natural cardinality by Exclusivity. Distinct initial segments cannot have the same finite cardinality: they are linearly ordered by inclusion, and strict inclusion contradicts the finite equal-cardinality inclusion lemma. Hence this relation is a bijection between E's individual Peano system and its Frege N_e, preserving zero and successor. It preserves addition and multiplication as well, by their defining recursion clauses and uniqueness proved by induction. Therefore every first-order arithmetic sentence has the same value in the two systems.

The inherited individual system was precisely M's current Frege arithmetic, so E falsifies A^e. We have constructed a C+□Plenitude+Infinity_e countermodel whenever C+I_e has one. The relevant Henkin completeness theorem now proves Theorem 35.1.

### 35.5 Scope and interpretation

The quotient need not contain every external subset of its domains. It is a Henkin model whose admitted relations are the supported extensional quotients represented in M. This is why the transfer applies to the actual finitary proof systems; it is not an invocation of full higher-order categoricity, which would force standard arithmetic.

The theorem gives a precise sense in which boxed Plenitude plus actual individual infinity adds modal and structural regularity without adding ordinary first-order arithmetic consequences beyond C+I_e. It does not erase the substantial modal differences: the source M can have singleton individuals and noncollapsed e-numbers, whereas the new E has genuinely infinite individuals and trivial modality.

No conservativity assertion for □Functional Choice follows. Adding arbitrary-output selection to a Henkin hierarchy is a further question, and the present unique-output reconstruction deliberately does not claim to settle it. Nor has a corresponding same-base statement for counting t or every other type been proved here.

## 36. Source-based arithmetic conservativity of boxed Functional Choice

Section 35 deliberately stopped at Plenitude. A further, substantial interpretation theorem supplies the missing Choice step. The source route was identified by the parent lane and audited here. Unlike §35's elementary current quotient, this result relies on the finite-order set-theoretic interpretation described below. No claim is made that Choice follows in C or that an arbitrary current Henkin hierarchy already contains selectors.

**Theorem 36.1.** For any fixed counting types σ and ρ and any ordinary first-order arithmetic sentence A, the following are equivalent:

    C+Iσ ⊢ A^σ;
    C+□FunctionalChoice+Infinityρ ⊢ A^ρ;
    C+□FunctionalChoice+{□Infinityτ : τ is an admitted type} ⊢ A^ρ.

The braces denote a schema, with one sentence for each fixed type, not an object-language quantifier over types. In particular the C+Iσ arithmetic shadow is independent of σ, and full boxed Functional Choice with actual infinity is conservative over that common arithmetic shadow. The theorem concerns finitary proof-theoretic consequences in Henkin semantics. It is not a claim that full models of the weak and strong systems have the same structural or modal properties.

### 36.1 The external interpretation theorem and its precise use

Colin McLarty, *Interpreting set theory in higher order arithmetic*, arXiv:1207.6357v5 (15 February 2013), defines Z_m using extensionality, full comprehension at each of its finitely many orders, and second-order induction (§2). Theorems 4.3 and 5.3 interpret ZFG[n+] plus V=L in Z_{n+2}; this set theory has replacement, global well-ordering, and at least n iterated powersets of ω. The base case is Theorems 3.2 and 3.4. [Primary manuscript](https://arxiv.org/pdf/1207.6357).

We use this as a **number-preserving interpretation**, not merely an equiconsistency statement. The preservation can be checked in the construction: the interpreted ω is the canonical tree of strictly descending finite sequences of the original numbers (§3.1 and Theorem 5.2), and the original number n corresponds to the subtree for its strict initial segment. Membership between those finite-ordinal trees gives the original order and successor. The constructible inner interpretation retains this ω and its elements; it changes the available sets, not those numbers or their arithmetic operations. Thus a fixed first-order arithmetic sentence has the same value before and after the interpretation.

This is the exact additional source reliance. We do not claim that the manuscript proves a theorem specifically about Classicism, nor that its constructible interpretation preserves arbitrary higher-order arithmetic statements.

### 36.2 Why C+Iσ supplies every finite-order source theory

Repeat §35's current quotient with its new individual base equal to Nσ(M), rather than specifically N_e(M). The type substitution sends e to νσ=(σt)t, still an admitted relational type. All support, current-equivalence, currying and guarded-comprehension arguments are unchanged. The inherited Peano structure on that base satisfies induction for every admitted property with parameters of arbitrary fixed finite types.

For any external finite m, its unary powerset chain gives a model of McLarty's Z_m: order one is the numerical base; order two consists of its admitted extensional unary properties; each subsequent order consists of admitted extensional properties of the preceding order. Full comprehension for formulas in these sorts follows from the guarded lambda construction, and extensionality follows from the quotient. No Choice is used in forming this source structure. Its first-order arithmetic is the original current arithmetic of M.

Therefore, given a C+Iσ countermodel to A^σ and any fixed n, the source interpretation yields a model S of ZFG[n+] whose internal ω has the same arithmetic and falsifies A. S need not be externally well-founded, and its ω need not be standard. Neither is required for this transfer.

### 36.3 Only a finite type fragment must be built in S

Suppose there were a finite proof π of A^ρ from boxed Functional Choice and the all-type boxed Infinity schema. Expand all abbreviations occurring in π, and include the finitely many H-proof certificates used to justify its Logical-Equivalence instances. The resulting proof uses only finitely many types, including their subtypes, logical constants and Frege arithmetic types.

One does **not** construct an internally uniform hierarchy for every type of C inside a single bounded-powerset set model. Instead choose n large enough for this one finite collection. There is an explicit finite bound: assign b(e)=0, b(t)=1 and, conservatively,

    b(αβ)=max(b(α),b(β))+3.

An object at a previously bounded level can be injected into a higher iterated powerset by singleton lifting. Two such codes can be paired by Kuratowski pairing, at a cost of two powerset levels. A function graph is a subset of that pair space, at a cost of one further level. Thus n at least the maximum of these bounds for the expanded finite proof, with harmless extra levels for its coding constructions, supplies all the required type carrier sets and all their function sets. Separation and replacement form the indicated subsets, images and products. This is a deliberately generous finite rank bound, not a claim that three levels are optimal.

### 36.4 The full internal S5 interpretation of that fragment

Inside S, take individuals D_e=ω and worlds W=ω. Take D_t=P(W), and for every function type occurring in the finite fragment take the full set of functions D_α→D_β. All these are sets by the preceding bound. Evaluate a proposition at w by membership of w. Boolean operations and quantifiers act pointwise; identity of higher objects is ordinary set identity, represented by W or the empty set. Lambda abstraction is interpreted by the ordinary function defined by its body.

This is the usual full S5 interpretation, carried out internally in S. It validates every required C instance: an H-theorem is true at every world under every assignment, and equivalent lambda bodies consequently determine the same full function. In particular the exact Logical-Equivalence side condition is preserved; no optional premise is treated as an H-theorem.

At any fixed world w, a serial relation U supplies a nonempty set of candidate outputs for each input. Global well-ordering chooses the least candidate, and replacement forms the selecting function. The full function domain contains it. Hence the relevant Functional Choice instances hold at every world, giving their boxed forms. The well-ordering used here comes from the interpreted set theory; it was not assumed in the original C model or in its finite-order arithmetic quotient.

Every required type domain is infinite in S. The individual domain is ω. The map n↦{n} injects ω into D_t=P(W), and constant relations inject D_t into every other relational type. These injections have graphs among the full admitted relations. Consequently every required Frege Infinity sentence holds at every world, giving its boxed form.

The interpreted Frege arithmetic at each required counting type is isomorphic to S's ω. One can define its n-th cardinality by counting the current extension of a property with the initial segment below n. Full function and property domains make this definition admitted. Its zero and successor clauses follow from finite bijection arithmetic; its image is an admitted successor-closed property, so Frege induction gives surjectivity. The ω-injection into the counted domain realizes every such finite cardinality and gives injectivity by finite pigeonhole. Thus the interpretation preserves zero, successor, addition and multiplication, and A^ρ has the same value as A in S.

The putative proof π would therefore make A true in S, contrary to the original countermodel and number preservation. This proves that the strongest displayed theory has no additional ordinary arithmetic consequences over C+Iσ.

### 36.5 Closing the equivalences and keeping their limits explicit

For each ρ, Infinityρ implies Iρ, so its C+Iρ shadow is contained in the arithmetic shadow of either stronger displayed theory. The countermodel argument gives the converse inclusion in the C+Iσ shadow for every σ. Applying it in both directions shows that all the C+Iσ shadows coincide, and gives the three equivalences in Theorem 36.1.

The use of all-type boxed Infinity is optional in the theorem: it is a convenient strongest positive package, and each finite proof uses only finitely many instances. The one-type actual Infinity version lies between C+Iρ and that strongest package, so it has the same arithmetic consequences too.

This result says exactly that □Functional Choice contributes no further **ordinary first-order arithmetic theorems** once the weak arithmetic noncollapse assumption I is available. It adds many genuine structural and modal principles and does not follow from C+I. Nor does the proof preserve an arbitrary original model's individual domain, its current relation domains, its higher-order parameters, or its accessible worlds. It reconstructs an appropriate counterinterpretation using a finite-order constructible set model.

### 36.6 Comparison with Max's non-effective arithmetic extension

Let T be this common arithmetic consequence theory. It is a consistent recursively axiomatizable extension of PA and is standard-sound: a full S5 model with infinite individuals and worlds supplies the intended standard arithmetic. Its ordinary arithmetized consistency assertion Con(T) is a true Π₁ sentence. Therefore Max proves Con(T), by §18, while T cannot prove Con(T), by Gödel II.

Max contains T already through C+I. Consequently

    T  is a proper subtheory of  Th_arith(Max(C)).

This is a precise arithmetic-strength comparison, not a proof that Max is inconsistent, and not an argument that arithmetic strength alone selects the preferred modal framework. The earlier possible-proof pathology remains: Max can make a false arithmetic inconsistency assertion possible while proving its actual negation. The positive □Functional Choice package instead adds the recorded stability principles without adding ordinary arithmetic consequences beyond T.

The conservativity theorem and this strictness consequence depend on the stated McLarty interpretation bridge. The simpler boxed-Plenitude conservativity in §35 remains independently available without that external constructibility theorem.

### 36.7 Identification with the union of all finite-order extensional arithmetic

Let Z_<ω denote the union of McLarty's finite-order extensional arithmetic theories Z_n, for external finite n≥2, under their usual inclusions of the lower-order languages. Each Z_n has the comprehension, extensionality and induction specified in §36.1. This union is an ordinary finitary theory with unbounded finite orders: it is not an infinitary conjunction, an additional infinite type, or a claim that the entire hierarchy is one set.

**Corollary 36.2.** The common ordinary first-order arithmetic theory T of Theorem 36.1 is precisely the ordinary first-order arithmetic consequence theory of Z_<ω. Equivalently, for each arithmetic sentence A,

    C+Iσ ⊢ A^σ    iff    Z_<ω ⊢ A
                     iff    Z_n ⊢ A for some external finite n.

For the inclusion from right to left, a finite Z_<ω proof lies in some Z_n. The current quotient of §36.2 interprets that entire finite-order theory in C+Iσ while preserving its numerical arithmetic, so its arithmetic conclusion belongs to T.

For the converse, take a finite C+Iσ proof of A^σ. Include its expanded definitions, subterm types, Logical-Equivalence H-certificates, and the fixed auxiliary arithmetic-correctness derivations as in §§36.3–4 and 37.7. A sufficiently high but finite iterated-powerset set theory builds the internal full S5 interpretation of this fragment, with individuals and worlds both ω. Every required Infinity instance, and hence the required Iσ, holds. The interpretation verifies the proof and identifies its Frege arithmetic with the set theory's ω. McLarty's number-preserving interpretation then transfers A to some finite Z_n. The rank and order n depend on the finite proof; no uniform finite n is asserted.

This corollary identifies only ordinary first-order arithmetic consequences. It does not identify the modal or higher-order theories, and it does not eliminate the source-dependent finite-order constructibility interpretation used for the reverse inclusion. Together with §37 it gives the equivalent formulation

    Th_arith(Max(C)) = Cn(Th_arith(Z_<ω) ∪ TrueΠ₁).

## 37. Exact ordinary arithmetic shadow of Pure Maximalism

This is a new metatheoretic argument, not a claim already present in the map. Its scope is the finitary pure theory and its Henkin proof semantics. It uses the current quotient and the number-preserving McLarty interpretation audited in §§35–36, together with an internal finite-component version of the free-root coalescence. It does not identify the higher-order or modal consequence theories. The external source results used are McLarty's finite-order constructible interpretation and Bacon–Dorr's countable BBK completeness; the current quotient, arithmetic preservation, bounded-rank coalescence, and exact consequence-theory equality are new arguments in this research note. This is a mathematical proof audit, not a Lean verification or an assertion of literature novelty. All counting-base changes use the canonical graph isomorphism J_{σ,ρ}; in particular J_{e,t} denotes the comparison of e-counting with t-counting, not a type named et.

Let T be the common first-order arithmetic consequence theory of C+Iσ from §36, and let TrueΠ₁ be the set of all standard-true first-order Π₁ arithmetic sentences. The following equality is between sets of ordinary arithmetic sentences, with deductive closure understood in the ordinary first-order arithmetic language:

    Th_arith(Max(C)) = Cn(T ∪ TrueΠ₁).

In particular this is also Cn(T ∪ TrueΣ₂). The latter reformulation follows because each true Σ₂ sentence has a standard witness leaving a true Π₁ instance, and TrueΠ₁ is contained in TrueΣ₂ after adding a dummy existential quantifier. These observations require no assertion that T itself is Π₁-axiomatizable.

### 37.1 The lower inclusion and the correct initial countermodel

Max proves Iσ and therefore contains T in its arithmetic translation. Section 18 proves that Max proves every true Π₁ arithmetic sentence. This establishes the lower inclusion.

For the converse, suppose an arithmetic sentence A is not a consequence of T∪TrueΠ₁. We first need a C model with the required arithmetic. One must not assume that an arbitrary model of T expands to a C+I model.

Instead the following theory is consistent:

    C + I_e + {P^e : P∈TrueΠ₁} + ¬A^e.

Indeed, if a finite subset were inconsistent, there would be true Π₁ sentences P₁,…,P_k such that C+I_e proves (P₁∧…∧P_k)→A in the arithmetic translation. By the definition of T, that ordinary arithmetic implication belongs to T, contrary to the assumed consistency of T∪TrueΠ₁∪{¬A}. Henkin completeness now supplies a model M of the displayed theory.

Apply the current quotient of §35, with base N_e(M), and then a sufficiently high finite-order McLarty interpretation. For each externally fixed finite rank bound required below this gives a model S of ZFG[n+] plus V=L whose internal ω has the same first-order arithmetic as M's current N_e. In particular

    S ⊨ ¬A and every sentence of TrueΠ₁.

S may be externally ill-founded and its ω may be nonstandard. All remaining constructions are carried out internally in S; they do not replace its ω by the external standard natural numbers.

### 37.2 Reduce a putative Max proof to finitely many component requests

Suppose Max proved A^e by a finite proof π. Use the equivalent Possibility presentation of pure Maximalism. Only finitely many added axioms occur in π, say

    ◇φ₁,…,◇φ_k,

where each φ_i is a closed pure sentence consistent with C. Include in the finite proof fragment every subterm type and every H-proof certificate used to license a Logical-Equivalence instance. Also include the fixed auxiliary derivations used below to verify the Frege Peano clauses and the recursive characterization of Sum and Prod, together with their own expanded subterms and H-certificates; include the full N_e and numeral-orbit definitions even if they were hidden in abbreviations. If the initial proof used the Distinctness presentation, first replace its finitely many used axioms by their finite derivations from the equivalent Possibility schema. This changes only the finite fragment and its eventual rank bound.

Use the consistency predicate of the original typed calculus itself. Its finite proofs are effectively checkable: Logical-Equivalence axiom lines carry their H-proof certificates, and beta-eta identifications can carry finite conversion certificates. All type and term syntax is effective. Thus Con(C+φ_i) is a standard Π₁ sentence. It is true by the side condition on the Max axiom and consequently holds in S.

There is a direct primary completeness source, so no equivalence with a newly invented first-order algebra theory is needed. In the author-hosted *Classicism*, draft of 1 July 2022, §3.1, Theorem 3.2 (pp.44–45) gives countable BBK completeness for H, and the following paragraph applies it to every H-extension. Footnote 64 constructs a complete witnessed extension and then takes typed closed terms modulo provable identity. [Exact 2022 manuscript](https://andrew-bacon.github.io/papers/Classicism.pdf). This differs in date from the 16 May 2023 draft ordinarily used by the map; the locator here deliberately refers to the inspected 2022 version.

### 37.3 Countable component algebras inside the bounded set model

Apply that explicit Henkin construction internally in S to C+φ_i, obtaining a countable BBK model M_i. Expand by a countable supply of witness constants of every type. Recursively decide each next sentence so as to retain consistency, adding a fresh witness whenever required. The consistency tests are arithmetical over ω^S; Separation and recursion/Replacement form the choices and their complete witnessed theory. The internal assertion Con(C+φ_i) ensures that this construction starts consistently and the familiar fresh-constant argument ensures each witness step preserves consistency.

The term interpretation can be coded especially economically. Choose the least-code closed term in each provable-identity class. These representatives form a subset of ω, with a type label for each one. Application takes representatives of application terms; interpretation of a term under a finite assignment is given by substitution followed by taking its representative; and truth is membership in the complete witnessed theory. Their graphs are all coded by subsets of finite powers of ω. The BBK truth lemma is proved by internal induction on term/formula codes. Since the completed theory contains every C axiom and the given φ_i, the resulting model satisfies C+φ_i. No ordinary extensional Functionality axiom is added.

This construction also handles internally nonstandard formula codes when S is nonstandard. In particular S has a coded interpretation satisfying its own required C instances; we are not taking an external standard truth predicate for its arithmetic. The proof theory used here is the original C plus the premise φ_i, with its original H Logical-Equivalence side condition. It is not strengthened by allowing Equivalence applied to φ_i-dependent theorems.

The entire countable typed algebra is therefore coded by sets of natural numbers. A fixed finite number of powersets of ω suffices, along with Separation and Replacement; there is no need to collect full powersets of its infinitely many type carriers. The later root construction uses only the finitely many component domains relevant to π.

Choose one individual a_i of each M_i. There are only finitely many components. The global well-ordering in S is available, although this finite selection itself causes no Choice issue.

### 37.4 The free current root algebra

Build a root with individual domain D_e^r=ω^S and maps π_i^e constantly equal to a_i. These maps need not be surjective. Their role is to give component values to root individual parameters; component quantifiers will still range over the whole component carrier.

Flatten each relational type τ as σ₁…σ_l t, allowing l=0 when τ=t. For the finitely many types required by π and its certificates, define recursively

    D_τ^r = 2^(D_σ₁^r × … × D_σ_l^r) × ∏_{i=1}^k D_τ^{M_i}.

The first factor is the full internal set of current truth functions on the root argument tuples; at t it is simply 2. Each relational root object is thus a pair consisting of an arbitrary current extension and one component object in each M_i. The maps π_i^τ select those component coordinates.

Application is defined by slicing the current truth function and applying the component objects to the component argument values. With all types flattened, this defines partial application as well: a slice is a current truth function on the remaining argument tuple, paired with the corresponding component partial applications. Thus projection compatibility holds by definition.

Boolean constants act on current truth values in the ordinary way and on component coordinates by their component interpretations. A quantifier has current value obtained by quantifying over the whole root sort; its i-th coordinate is the component quantifier over the whole M_i sort. In particular the i-th quantifier is not restricted to the image of π_i^e. Equality has current truth precisely when the root objects are literally equal, while its component coordinate is the component equality value of their projections. Lambda abstraction pairs the current truth function defined by its body with that body's lambda interpretation in each component under the projected parameter assignment.

The clauses are algebraic, so no representation of the components by full action models is needed. They are the direct free-current version of the coalescence construction used in *Classicism*, Appendix E, especially p.83; the use here is a new internal bounded-rank adaptation, not an attribution of this arithmetic-shadow theorem to that source.

### 37.5 C validity and the Logical-Equivalence side condition

The ordinary H rules and axioms hold at the root: logical truth is classical; quantifiers have their full local ranges; beta and eta hold by the application/lambda definitions; and current identity is genuine equality of the constructed objects. Substitution of identical root objects preserves every operation and truth value. The corresponding component clauses hold because each M_i is a C algebra. In particular current coextension of arbitrary intensional objects is never substituted for identity.

For an instance of Logical Equivalence, use its actual H-proof certificate. The H-equivalent bodies agree in current truth under every root assignment, so their lambda abstractions have the same current extension. In each component the same valid H-equivalence makes the component lambda abstractions identical, since M_i satisfies C. The two root abstractions therefore agree in every coordinate and are literally identical. This checks the theoremhood restriction directly; an equivalence merely derivable from φ_i, I_e, or any optional premise is not used as an H-equivalence.

Thus the root interpretation validates the finite C proof fragment in π. It also validates each required ◇φ_i. The i-th coordinate of the root value of φ_i is true in M_i, hence is different from its component bottom value. Accordingly the root proposition denoted by φ_i differs from the root bottom proposition. Since ◇p abbreviates p≠⊥, its current root truth follows. Closed purity is important here: no extra signature constants need simultaneous interpretation through the chosen root individual maps.

### 37.6 The root arithmetic is exactly the internal ω of S

Let b_n be the internal S-recursion

    b_0=0_e,       b_{n+1}=Suc_e(b_n),       n∈ω^S,

using the root zero and successor operations. Replacement forms its range R⊆D_ν_e^r. The root's full current property domain contains a property with extension exactly R, with arbitrary component coordinates, for example component bottoms. This property is currently zero-containing and successor-closed. The definition of N_e therefore gives N_e⊆R.

Conversely, each currently zero-containing successor-closed property contains every b_n, by induction in S on its own ω. This yields R⊆N_e. Hence the root's natural-number domain is exactly the internally represented numeral orbit R. This is an internal-standardness statement relative to ω^S; it does not say that R consists only of externally standard numerals.

Internal finite-cardinality induction shows that b_n counts exactly the root properties whose current extensions have n elements in S. The individual domain is ω^S, so the extension [0,n) is available at et and witnesses b_n for every n. These initial segments and finite pigeonhole distinguish b_m from b_n when m≠n. Thus n↦b_n is a bijection preserving zero and successor between ω^S and N_e at the root.

The full current binary relation domains also contain the graphs of addition and multiplication on this orbit, with arbitrary component coordinates. The same induction used in §24 identifies the source definitions of Sum and Prod with those graphs. Equivalently their current recursion clauses have unique solutions on this internally standard Peano system, and the full current graph witnesses exclude spurious outputs. Therefore every ordinary arithmetic sentence at e has exactly its S-arithmetic value. In particular the root falsifies A^e.

For this upper bound, no infinitude assertion about the root t-domain is required. We deliberately count at e. Other fixed counting types can be reduced to e in Max using its Iσ and I_e and the canonical numerical isomorphism of §13. If an all-type internally infinite root is wanted for another purpose, one may add a coded component satisfying C+Infinity_t, using its additional true Π₁ consistency assertion; that extra construction is unnecessary here.

### 37.7 Why the finite rank bound closes the argument

The finite proof π, its expanded abbreviations, all its subterm types, the logical-constant types appearing in it, and its finitely many H-certificates give a finite list. Enlarge it by the N_e/orbit definitions and the fixed arithmetic-correctness derivations invoked in §37.6, including Peano clauses, Sum/Prod recursion and their uniqueness arguments, with all their own subterm types and H-certificates. If another arithmetic counting base is first reduced to e, include the finite derivation using J_{σ,e} as well. This is still a finite list; the root is not tacitly assumed to validate C instances outside it. A quantifier at σ requires its (σt)t constant type; this is included whenever that quantifier occurs. There is no requirement to iterate such additions for quantifiers that never appear. The component language may contain all types, but its entire term model was coded countably in §37.3.

For the root list, each domain is formed from finitely many already bounded products, a powerset, and finitely many countable component factors. The generous finite powerset bounds from §36.3, enlarged by a fixed coding allowance and by the finite list's maximum type complexity, therefore suffice. The numeral orbit uses Replacement and a subset of an already constructed carrier, rather than a new unbounded type hierarchy. Choose the McLarty rank n at the outset large enough for this finite construction.

Inside the resulting S, every step of π is sound in the root interpretation, all its finitely many Max axioms hold, and A^e is false. This is impossible. Hence no such π exists, establishing the upper inclusion and the displayed exact arithmetic-shadow equality.

### 37.8 Consequences and limits

The description sharpens §36.6: Max adds exactly the deductive effect of all true Π₁ arithmetic sentences to the common effective arithmetic theory of C+I and the boxed-Functional-Choice infinity packages. In particular its added arithmetic is stronger than that effective theory but does not comprise all arithmetic truth.

For a finite Max proof, the argument uses only finitely many extra true Π₁ assertions Con(C+φ_i), corresponding to that proof's finitely many possibility axioms, together with whatever true Π₁ assumptions are present in a countermodel argument. Compactness therefore also gives a finite Π₁ reduction of each individual arithmetic consequence. This is not a uniform effective procedure that decides which possibilities are C-consistent.

The theorem does not turn Max into an effective theory, does not show Strong Possibility consistent or inconsistent, and does not make Max's possible arithmetic states standard-sound. Its conclusion is only about actual ordinary first-order arithmetic theorems. The source-dependent interpretation steps and the internally verified typed Henkin construction are essential; omitting them would leave the upper inclusion unsupported.

### 37.9 Current choice and actual infinity do not enlarge this shadow

The same upper-bound construction validates additional ordinary current mathematics. At the root every internal S-subset of each required argument product is an admitted current extension. S's global well-ordering therefore supplies, for any currently serial relation, a graph selecting one output from each fiber. Give that graph arbitrary component coordinates; its current root truth verifies the corresponding Relational Choice instance. The same method gives a transversal of every current equivalence relation and a well-ordering of every required current domain. These arguments concern graph relations, so they never introduce an inadmissible operation with output e.

The root e-domain is ω^S, and every root numerical cardinality b_n counts exactly n-element current extensions. Its whole e-domain is therefore Frege-infinite. Consequently adjoining any or all of the following schemata to Max leaves its ordinary arithmetic shadow equal to Cn(T∪TrueΠ₁): current Relational Choice, current Transversal Choice, current Well-Ordering, and actual Infinity_e.

One may include actual Infinity at all admitted types as well. For a finite proof using finitely many such instances, add one component M_∞ satisfying C+Infinity_t. The latter theory is consistent in an ordinary full infinite-world model, so its arithmetized consistency assertion is another true Π₁ sentence available in S. The internal typed Henkin construction supplies M_∞. Its t-carrier is infinite inside S: if it had an internal finite size n, finite-cardinality induction in the coded C algebra would make its whole t-domain counted by its n-th numeral, contradicting Infinity_t. Choice inside S then gives an ω-injection into that carrier and hence into the root t-carrier, by holding the root current bit and the other component coordinates fixed. Constant relations inject the root t-domain into every nonempty-argument relational domain. With the root e-domain already ω^S, each required root type is internally infinite, and the internally full current extension domains verify its Frege Infinity sentence.

Thus even Max plus all these current choice and all-type actual infinity schemata has exactly the same ordinary arithmetic theory. As throughout the section, only finitely many instances occur in a proof, so the bounded powerset construction remains adequate. No claim is made here for boxed choice or boxed infinity, for Plenitude, or for rigid/modal comprehension; those require additional compatibility across component coordinates that arbitrary current graph extensions do not supply.
