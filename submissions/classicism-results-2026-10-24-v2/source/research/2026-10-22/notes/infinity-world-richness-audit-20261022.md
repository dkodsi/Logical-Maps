# Infinity, world richness, and relational structure: coordination audit

Research scratch, 22 October 2026. Fixed theory: Classicism C in the relational type system. No e→e type is used. This note records ordinary mathematical arguments by the current OpenAI Codex research team, not novelty claims or independently human-checked proofs. No database records, published proofs, generated files, or Lean files have been changed. Direct source for a future record of a new argument here is `misc`.

## Detailed proof files

- `world-cardinality-ucp-20261022.md`: universal contingent profiles, transparent world-representation definition, exact Cantor limits, finite/infinite models, cardinal equivalences, induced Boolean algebra of worlds, and finite-rank rigid-power variants.
- `frege-infinity-20261022-1726.md`: numerical-parameter absoluteness, numerical extensionality/null collapse, Strong Possibility's numerical pathology, realization form of Infinity, and natural-number injection into infinite individuals under boxed Functional Choice.
- `relational-coding-recursion-20261022.md`: Plenitude as well-founded deterministic recursion; Functional Choice as well-founded dependent choice; canonical fixed-point results; extensional-fragment transplantation; Strong Possibility reflection observations.

These files are being extended during the research window. Claims marked as candidates or caveats there retain those qualifications.

## Exact background and provenance

Write B for C+□Plenitude, equivalently C+□ND+Atomicity. Do not substitute unboxed ND+Atomicity. The stronger favored package is C+□Functional Choice. Proved-only queries using `scripts.pmap.load_topic` and `Engine`, with optional assumptions in the queried premise set, confirmed B entails No Pure Contingency, □BF, □Rigid Comprehension, □Boolean Completeness, and the Strong Leibniz principles. These are recorded results, not discoveries of this lane.

The full S5/group constructions used for consistency are recorded in `models/full-infinite-s5.yaml`, `groups/full-action-models.yaml`, and `writeups/full-permutation-group-infinite-set.md`; their primary construction source is Bacon and Dorr, *Classicism*, draft 16 May 2023, §3.5, pp. 58–61 and Appendix D. The coalesced construction used for Maximalism is recorded in `groups/coalesced-sums.yaml` and the coalesced-root models, sourcing Appendix E, pp. 80–83. Generalized root variants beyond those records are marked as new semantic arguments.

The recorded result `strong-possibility-and-infinity-e-incompatible` already proves Strong Possibility implies exactly one individual. The new arguments below sharpen consequences; they do not claim to discover monism or to refute the known relative consistency of ordinary Pure Maximalism.

## A. A sharper atom-factorization theorem

This extends the mechanism in the recorded result `atomicity-t-and-bf-imply-atomicity`, whose source is Cian Dorr's observation of 23 September 2026 and whose proof pairs a proposition atom with a tuple haecceity. The factorization and exact equivalence relation below are new deductions from that mechanism.

Let τ=σ₁…σₙt, allowing n=0. Put

    A(w,x̄) := λȳ. w ∧ (ȳ=x̄).

### A1. Pair construction and equality criterion, in C

If w is a proposition atom, A(w,x̄) is an atom at τ. Indeed A(w,x̄)[x̄]=w≠⊥. If Z≤A(w,x̄), then Z[x̄]≤w, so Z[x̄] is either ⊥ or w. Necessarily, every instance Z[ȳ] entails ȳ=x̄ and hence Z[x̄]. In the first case Z=⊥ by Intensionality. In the second case any instance of A(w,x̄) has ȳ=x̄ and w, hence Z[x̄] and Z[ȳ], so A(w,x̄)≤Z. Therefore Z is ⊥ or A(w,x̄).

For atoms w,v,

    A(w,x̄)=A(v,z̄)  iff  w=v and w≤(x̄=z̄).

For the forward direction apply the operation ∃ȳ to both sides. Logical Equivalence gives ∃ȳ A(w,x̄)[ȳ]=w and similarly v, so w=v. Evaluate at x̄: w=w∧(x̄=z̄), yielding the displayed entailment. Conversely w=v and w≤(x̄=z̄) make the two abstracts necessarily coextensive; Intensionality identifies them. For the empty tuple this reduces to equality of w,v.

### A2. Every relational atom factors, assuming BF at its argument types

Suppose Z is a τ-atom. Z≠⊥ gives ◇∃x̄ Z[x̄] by Intensionality. Repeated BF yields an actual tuple x̄ with ◇Z[x̄]. Set w:=Z[x̄]. Then A(w,x̄)≤Z by necessary substitution, and A(w,x̄) is nonbottom because its value at x̄ is w. Atomhood of Z therefore gives Z=A(w,x̄), even before w has been shown atomic.

To show w atomic, take q≤w. The relation A(q,x̄) lies below Z, so it is either ⊥ or Z. Evaluation at x̄ gives q=⊥ or q=w. Since w≠⊥, w is a proposition atom.

Thus, under BF, atoms at τ are exactly pairs (w,x̄) modulo

    (w,x̄) ∼ (v,z̄) iff w=v and w≤(x̄=z̄).

No Atomicity hypothesis is required for this classification of whatever atoms exist. Atomicity_t together with BF additionally supplies an atom below every nonzero relation, as already recorded.

### A3. Under C5 the quotient is an actual product

Under ND at the argument types, w≤(x̄=z̄) with w≠⊥ implies x̄=z̄. For otherwise ND makes the corresponding disequality necessary, contradicting the possibility of w. Consequently under C5 the displayed map is a bijection

    Atoms(σ₁…σₙt) ≅ Atoms(t) × Dσ₁ × … × Dσₙ.

This is an internal relational bijection, with tuple codes if needed. It is not a claim that every external subset is represented in an arbitrary Henkin model. In full finite S5 models it gives the expected exact count of relational atoms.

## B. Minimal Strong Possibility failure of Functionality

Assume Strong Possibility. The recorded monism argument gives an actual sole individual a; ordinary Pure Maximalism follows and makes a world with two individuals possible.

Let H:=λxᵉ.(x=a) and T:=λxᵉ.⊤. At the evaluation point every x=a. NI makes (x=a)=⊤, so Hx=Tx for every actual x.

But H=T would, by Intensionality, imply □∀x(x=a), contradicting the possible existence of two individuals. Hence H≠T although ∀x Hx=Tx. This refutes unboxed Functionality already at input e and output t. BF_e also fails: ∀x□(x=a) holds, while □∀x(x=a) fails.

This is a conditional theorem about Strong Possibility; it is not a contradiction in Strong Possibility. The difference between actual coextension and intensional identity is part of C's intended semantics.

## C. Useful transparent formulation of world richness

For any support type σ, let WRσ be

    ∃V^(σt) ∀X^(σt) ∃wᵗ [Atom(w) ∧ ∀x(Xx ↔ w≤Vx)].

Read this as: every current property on the support has a representing world through one contingent predicate V. Under B it is equivalent to the rigid-profile formulation

    ∃V^(σt) ∀X^(σt) [Rigid(X) → ◇∀x(Vx↔Xx)].

Detailed proof and the unique-world variant are in the world-cardinality file. The representation formulation is more transparent and exposes the exact diagonal: at σ=t use X(p):=¬(p≤Vp); its representing world w gives Xw↔w≤Vw and Xw↔¬(w≤Vw). Thus C itself refutes WR_t. Constant-relation embeddings t↪σ transfer this to every relational σ. Individuals are the sole unrestricted admitted base type where it can consistently hold.

In full S5 with individuals D and worlds P(D), V(d) is true at S precisely when d∈S. Every rigid profile has exactly one realizing world, so the unique version is consistent with □Functional Choice for every nonempty D, finite or infinite. D=ℕ is a concrete rich positive model. All-set cardinal statements derived from this construction are full-model facts unless an internal relational proof is separately supplied.

## D. Scope of finite-rank richness

The world-cardinality file develops WR restricted to the iterated rigid-power supports A₀=e, Aₙ₊₁=rigid subproperties of Aₙ. In full S5 these are the ordinary finite powerset hierarchy over D, independent of the world set. Worlds can be chosen large enough to realize every profile on every finite rank at once.

Do not infer the Frege Axiom of Infinity merely from a schema of arbitrarily large finite requirements. With D a singleton, every finite batch of rank requirements has a finite full S5 model and satisfies ¬AxiomOfInfinity_t. The usual Henkin compactness reasoning therefore permits the whole schema together with this negation, even though it implies every fixed finite lower bound. If internal infinity is intended, keep an Axiom of Infinity explicitly in the premises. The full-model external beth-hierarchy lower bound is a different claim.

## E. Guardrails for the final assessment

1. □Functional Choice has full S5 models in the ordinary metatheory, including the very rich world-profile models. A statement that it is literally a theorem of bare C would contradict recorded countermodels; the evidence supports a strong coherent optional theory.
2. Ordinary Pure Maximalism has recorded coalesced models. Its incompatibility with many attractive necessary principles does not establish inconsistency. Strong Possibility is a further schema whose consistency is not settled by the arguments here.
3. Unboxed full second-order extensional mathematics on individuals can survive at a maximalist root; the root-transplant file explains the scope and source-verification caveat. The sharp contrast is especially stability and stronger functional/recursive/completeness principles, not a blanket inability to express mathematics.
4. Any use of infinitary conjunctions, extra sorts, stronger comprehension, or altered reference theory must be labeled beyond fixed C and supplied with exact proof rules. No such extension is silently used in this note.

## F. Exact internal finiteness by type under Functionality

This is a new deduction, independently audited by the relational-coding research agent on 22 October 2026. It concerns Frege-finiteness, not merely a schema of standard finite bounds. Write `Fin_σ(P):=∃n(N_σ(n)∧nP)` and `Fin(σ):=Fin_σ(⊤_σ)`.

### F1. Elementary finite-set lemmas in bare C

At the current evaluation point, C proves the following by induction on its impredicative finite-cardinality definition.

1. Finite properties are closed under taking subproperties and finite unions. A singleton (or an at-most-singleton property) is finite.
2. The image of a finite property under a current single-valued relational graph is finite, even when the output type is e. No operation of type e→e is asserted.
3. If A is finite, and a relation R has a finite fiber R(a,−) for every a satisfying A, then its union image `λy.∃a(Aa∧R(a,y))` is finite. The proof inducts on a finite-cardinality witness for A. For the successor step remove its witnessed element a, apply the induction hypothesis to the remainder, and take its finite union with R(a,−). No choice is used; only the one existential witness exposed at the current induction step.

For completeness, downward closure can be proved simultaneously with finite-union closure by the same remove-one induction. If nA and S⊆A, delete the successor witness a from A; S is either S minus a or the union of S minus a and the singleton a. A current single-valued graph has empty or singleton fibers, so item 2 is a special case of item 3. All membership calculations here are at the current evaluation point. Finite-cardinality predicates are invariant under current coextension, proved by the defining induction; intensional identity of coextensive properties is not used.

### F2. A finite separation lemma, without constructing arbitrary functions

Let A⊆D_σ be finite, B⊆D_τ finite, and H a family of operations F:σ→τ. Suppose

- for every F∈H and x∈A, Fx∈B;
- whenever F,G∈H agree in value at every x∈A, F=G.

Then H is finite, in C.

Prove the stronger assertion for every such H by induction on a finite-cardinality witness for A. When A is empty, the second condition makes H at most singleton. In the successor case write A=A'∪{a}, with a∉A'. For every y∈B let `H_y(F):=HF∧Fa=y`. Two members of H_y that agree on A' agree on all A, and so are identical. Thus each H_y is finite by induction. Every F∈H lies in H_{Fa}; F1(3) with finite index property B now makes H finite.

This argument neither builds every conceivable assignment nor presupposes finite interpolation. It applies to the existing operations and only bounds their number. That distinction matters in C, where distinct arguments can possibly coalesce.

### F3. Finiteness of an operation type

For any admitted operation type σ→τ (so τ≠e), its Functionality instance gives

    Fin(σ→τ) ↔ Fin(σ) ∧ Fin(τ).

The reverse implication is F2 with A and B universal and H the universal operation family: Functionality supplies the separating hypothesis.

For the forward implication, D_τ injects by the constant-operation map y↦λx.y. Also D_σ injects into D_{σ→τ}: write τ=ρ₁…ρₙt and send a to

    λx^σ z₁^ρ₁ … zₙ^ρₙ. x=a.

If the images of a,b are equal, evaluate at x=a and any tuple z̄. Their equality gives (a=a)=(a=b), hence a=b. Every type is nonempty, and the empty tuple covers τ=t. For each injection its image is a subproperty of the finite operation domain and hence finite; pull that finite image back along the inverse relational graph, whose fibers are singletons. F1 then gives finiteness of the corresponding source domain. Thus finiteness of the operation type entails both input and output finiteness. This direction uses no Functionality.

Repeatedly applying F3 down the finite type expression gives, under the finitely many Functionality instances involved:

- for a relational type τ with no occurrence of e, `AInf_τ ↔ AInf_t`;
- for a relational type τ containing e, `AInf_τ ↔ (AInf_e ∨ AInf_t)`.

Here every AInf is the genuine Frege Axiom of Infinity. Functionality is recorded as equivalent to BF in C; hence full BF suffices. Atomicity, Boolean Completeness, Choice, ND and C5 are not required for this size dichotomy. The result therefore also holds under C+□Functional Choice, with only two independent base directions of infinity.

### F4. Independence of the two directions, under boxed Functional Choice

Full S5 models witness all four possibilities: take the individual set D finite or infinite, and the world set W finite or infinite independently. The propositions are P(W), so in full models their Frege Axiom of Infinity holds exactly when W is infinite; individuals are infinite exactly when D is infinite. All these full models satisfy □Functional Choice. Thus individual infinity and propositional/world infinity should remain distinct axioms. In particular Infinity_e does not itself force Infinity_t.

## G. Boolean completeness reduced to joins of haecceities

New connecting formulation, 22 October 2026, OpenAI Codex; independently audited by the Frege and relational-core research lanes. This is an ordinary mathematical argument, not a record edit or Lean verification. The existing source-related results already prove Weak Rigid Comprehension → Boolean Completeness and ND + Boolean Completeness → Plenitude; this section does not claim a new settlement of either implication.

For an object type σ define SCσ to say: for every X^{σt}, the family

    Haecs(X)(Y) := ∃a^σ(Xa ∧ Y=λx.x=a)

has a least upper bound in the Boolean algebra at σt. The order is necessary inclusion. Write H_a for λx.x=a. C proves H_a≤B iff □Ba.

### G1. A haecceity join is persistent

Suppose B is the least upper bound of Haecs(X). For every current Xa, □Ba holds, hence □□Ba by 4. Therefore B′:=λx.□Bx is another upper bound. Leastness gives B≤B′, which is full persistence of B. This uses no BF, ND, Atomicity or actuality.

### G2. ND gives current coextension and weak rigidity

Assume ND at σ. If Xa, then □Ba and hence Ba. If ¬Xa, every current Xb satisfies b≠a, hence □(b≠a) by ND. Thus ¬H_a is an upper bound of Haecs(X), so B≤¬H_a and ¬Ba. Therefore B currently coextends X.

Now if every current B-member necessarily satisfies Z, current coextension makes every H_a with Xa lie below Z. Leastness gives B≤Z. This is weak inextensibility; G1 gives persistence. Conversely, any weakly rigid current coextension of X is an upper bound of its haecceities by weak persistence and is their least upper bound by weak inextensibility. Thus, over C+NDσ, SCσ is equivalent to Weak Rigid Comprehension for σ-properties. The reverse direction needs no ND. The current coextension clause is indispensable when ND is absent.

### G3. The all-type haecceity-join schema already gives all Boolean joins

Let τ be relational and assume SCτ. Given a family F^{τt}, let B^{τt} be the join of Haecs(F). Write τ=σ₁…σₙt, allowing n=0, and define

    L(x̄) := ∃g^τ(Bg ∧ g(x̄)).

If Fg, then H_g≤B, so □Bg and g≤L. Thus L is an upper bound of F. If Z is any upper bound of F, put U_Z(g):=(g≤Z). For every current Fg, g≤Z and therefore □(g≤Z) by 4. Hence H_g≤U_Z, so leastness gives B≤U_Z. At every world, Bg now entails g≤Z; consequently Bg∧g(x̄) entails Z(x̄), and L≤Z. This proves that L is the least upper bound of F.

No step collects a current universal quantifier into a box. The boxed inclusion B≤U_Z already quantifies locally at each world and applies to the existential witness there. Therefore SCτ implies Boolean Completeness at τ in bare C. Conversely Boolean Completeness at σt immediately supplies SCσ. Taken over every type, the haecceity-join schema and Boolean Completeness are equivalent.

This refines the form of the assumption, not its all-type strength: limiting arbitrary joins to families of haecceities does not weaken Boolean Completeness when the schema is available at all types. By contrast, the single canonical numerical family studied in the Frege file is genuinely weaker and suffices for the arithmetic necessity argument.
