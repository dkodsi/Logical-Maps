# Pure Maximalist Classicism: exact effective lower bounds and relative-low upper bounds

Research notes by OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematics; no Lean claim. No database records edited.

## 0. Framework and attribution

Work in the fixed relational type system of the bundle: types are generated from e,t by σ→τ only when τ≠e. C is the smallest H-theory containing Logical Equivalence with its H-theoremhood side condition. The language and types are effectively coded. A “pure” term has no nonlogical constants. Max means C plus every closed pure A≠B for which C does not prove A=B. The side condition always refers to C, never to Max or a strengthening.

The local sources inspected were `topics/classicism/topic.yaml`, `background.md` §§Framework, Notation, Conventions, `principles/distinctness-schema-r.yaml`, and `models/coalesced-maximalist-root.yaml`. The last supplies consistency of Max, and consistency with the individual Axiom of Infinity, through the recorded coalesced construction.

**Attribution correction:** the bare assertion that Max is not recursively axiomatizable is already explicit in Bacon–Dorr, *Classicism*, accessible draft of 1 July 2022, §2.4, printed p.35, n.52. The source gives the non-theorem enumeration argument. The stronger no-consistent-effective-strengthening statement, exact oracle cone, and degree bookkeeping below are refinements/proofs supplied here; no novelty in the literature is claimed. The bundle's normal locators are to the different 16 May 2023 draft. Do not silently transfer the 2022 footnote/page number to that draft.

The same accessible 2022 draft, §3.1, Theorem 3.2, printed pp.44–45, especially n.64 on p.45, explicitly supplies complete witness theories and their countable BBK term models. “Henkin construction” below refers to that method. It does **not** mean an extensional Henkin model of Max: extensionality is incompatible with Max.

Public primary references used:

- Bacon–Dorr, 1 July 2022 draft: https://andrew-bacon.github.io/papers/Classicism.pdf (the date is printed on page 1).
- Brattka, de Brecht and Pauly, *Closed Choice and a Uniform Low Basis Theorem*, arXiv:1002.2800v2: https://arxiv.org/html/1002.2800v2 (for the standard Low Basis Theorem; the arguments below use its ordinary relativization).

## 1. The pure identity word problem is Σ^0_1-complete

Let

    E_C = { ⟨A,B⟩ : A,B are closed pure same-type terms and C ⊢ A=B }.

Let Th_C be the set of closed pure C-theorems. Both are computably enumerable. H has effective axiom schemes and rules; an instance of Logical Equivalence can be enumerated together with its certifying H-proof. Finite C-proofs are consequently effectively enumerable. One need not decide whether an unannotated formula is an instance of Logical Equivalence.

For every closed pure sentence P,

    C ⊢ P   iff   C ⊢ P=top.                         (1)

Left to right is theorem necessitation in C, with Box P defined as P=top. Right to left is T. This step concerns actual C-theorems and does not necessitate an optional assumption.

We now give a many-one hardness argument, not merely an undecidability argument. Let K be the halting set. There is a computable map n↦h_n to Σ_1 arithmetic sentences such that N⊨h_n iff n∈K. Choose the usual finitely axiomatized Robinson arithmetic Q. For n∈K, the finite true computation is verified in Q, so Q⊢h_n. For n∉K, the standard arithmetic structure satisfies Q∧¬h_n. Thus the first-order sentence

    (conjunction of the Q axioms) → h_n

is first-order valid iff n∈K. Function symbols and constants can be eliminated effectively by graph relations and explicit totality/uniqueness axioms, with a universally quantified variable for each eliminated constant. This gives an effective purely relational first-order sentence θ_n with the same validity status. Only a fixed finite list of relation arities is needed.

Replace each nonlogical relation symbol in θ_n by a higher-order variable of the corresponding admitted relational type, and universally close those variables. Call the resulting pure higher-order sentence P_n. If θ_n is first-order valid, a first-order proof translates to an H-proof of P_n. If θ_n is not valid, its nonempty first-order counterstructure expands to the full ordinary extensional type structure on that individual domain, taking t={0,1} and all admitted function spaces. This is a model of C; the relation variables can take the original counterstructure's relations, so P_n is false there. Therefore

    n∈K  iff  C⊢P_n  iff  C⊢P_n=top.                (2)

All types used are admitted; no function type ending in e is introduced. Hence Th_C and E_C are Σ^0_1-complete under many-one reductions. In particular each has Turing degree exactly 0′. Even the restricted identity problem with right side top and left side a closed pure proposition is already Σ^0_1-complete.

The fixed-Q argument can equivalently be replaced by the standard Σ^0_1-completeness of first-order relational validity. It is included to make clear why Church's undecidability alone is not the claimed completeness result.

## 2. Every Max model has the same pure equality/necessity/possibility diagrams

Let M be a model of Max at its evaluation point. For every closed pure same-type pair,

    M⊨A=B  iff  C⊢A=B.                             (3)

The forward direction uses Max's distinctness axiom whenever the right side fails; the reverse uses soundness. Thus the positive closed pure equality diagram is exactly E_C, independent of M, and is Σ^0_1-complete. Its negative equality diagram is Π^0_1-complete. Their joined complete diagram has degree exactly 0′.

Similarly, with P ranging over closed pure sentences,

    {P : M⊨Box P} = Th_C,                           (4)
    {P : M⊨Diamond P} = {P : C+P is consistent}.    (5)

For (4), use Box P=(P=top) and (1),(3). For (5), use Diamond P=¬Box¬P and the ordinary deduction theorem for a closed added premise. Consequently the necessary pure theory is Σ^0_1-complete, and the possible pure theory is Π^0_1-complete. Neither statement says that the **actual unmodalized** pure theory {P:M⊨P} is the same in every Max model or has exactly degree 0′.

These are syntactic-computability classifications of subsets of finite formula codes. They are not cardinality comparisons of domains and require no optional object-language Infinity axiom.

## 3. Exact cone of oracles admitting a consistent axiomatizable strengthening

For any oracle X, the following are equivalent:

1. There is a consistent X-c.e. theory T extending C whose consequences include all pure Max axioms.
2. 0′ ≤_T X.

Proof of 1⇒2. For a closed pure identity A=B, run in parallel an ordinary search for a C-proof of A=B and an X-effective search for a T-proof of A≠B. If C proves A=B, consistency of T excludes the second outcome. If C does not prove it, Max supplies A≠B as a T-consequence. Exactly one search eventually succeeds. This decides E_C using X. Section 1 gives 0′≤_T X.

Proof of 2⇒1. An oracle computing 0′ decides membership in E_C, hence decides which syntactically eligible distinctness instances belong to Max. C is c.e. Therefore C plus the Max axiom set, and its deductive closure, are X-c.e. Its consistency is supplied by the coalesced model.

This axiomatization cone is exact and differs from the model-construction task: §9 requires PA degree over 0′, and `effective-refinements.md` §8 proves that adequate models have no least solution degree. In particular no consistent recursively axiomatizable strengthening of C can entail Max. Conversely the non-effective schema is perfectly consistent: failure of an effective axiomatization is not semantic inconsistency.

The same proof works if T is merely presented by an X-effective enumeration of its theorems. For a recursively axiomatized proof calculus, a finite proof only uses finitely many enumerated axioms, so either formulation yields X-c.e. theoremhood.

## 4. Which presentation codes must compute 0′?

Call a presentation of M **term-effective in X** if X uniformly computes the denotation, in its numbered domains, of every closed pure term, and X decides equality of the resulting numbered elements. Then (3) immediately computes E_C from X:

    0′ ≤_T X.                                      (6)

It suffices to have X-semidecision of **inequality** for denotations of closed pure terms. Race this with the ordinary enumeration of positive C identities, exactly as in §3. Positive semidecision of equality alone is insufficient: E_C itself is already c.e.

This applies directly to the paper's BBK model format when the supplied code includes the uniform term-interpretation function, with numbered domains and their equality. It also applies to an atomic diagram of a first-order expansion explicitly containing the uniform term-evaluation operations. For that conventional coding there is no computable Max model, and no model with a low interpretation code: a low degree d has d′=0′, whereas 0′≤d would force 0′′≤d′.

**A smaller sufficient code.** An applicative presentation giving effective sorted domains, equality and total application already computes 0′, nonuniformly in finitely many indices; no general lambda-term interpreter or actual truth valuation is needed. Hardcode the denotations of 0_ν, Suc_ν, top_t and G=λn^ν.(I→h(n)), using §8's fixed counting type and halting formula. On input k compute G(Suc^k0) by application and compare it with top. This is the closed pure identity (I→h(numeral k))=top. If k halts, its finite arithmetic verification gives a C-proof of that identity; if k does not halt, the full standard extensional countermodel refutes it. Max therefore makes the equality hold exactly when k∈0′. The finite parameter indices need not be discoverable uniformly from an unnamed presentation, but may be hardcoded in a Turing-degree reduction. If explicitly named, the extraction is uniform.

**Remaining qualification.** A bare code for a category or its actions need not provide the application operation just used, and is not automatically covered. Quantifier satisfaction in other countable structural presentations may require further jumps. A computable list of term representatives together with a merely c.e. equality congruence is also different from a presentation with decidable equality. The computable term algebra modulo E_C illustrates this latter distinction. The application/equality lower bound is only 0′; it neither gives the stronger PA-over-0′ bound without truth nor establishes that some full Max model has an application/equality presentation computable in 0′.

The lower bound concerns countable effective presentations. Uncountable full models generally do not have presentations on natural-number domains in the first place.

## 5. Relative Low Basis upper bound for countable BBK models

There is a countable BBK model M of Max with a uniform interpretation-and-truth code D satisfying

    0′ <_T D <_T 0′′,       D′ ≡_T 0′′.            (7)

More generally, let S be any c.e. set of additional pure sentences such that Max+S is consistent. The same conclusion holds for a model of Max+S. It therefore applies to Max plus the individual Axiom of Infinity, using the recorded coalesced model.

Here is the construction in detail. Put A=0′. The axioms of T=Max+S are A-c.e. Expand the language effectively by witness constants in stages. For each existential sentence ∃x φ(x) in a stage language, choose a fresh constant c of the type of x and add

    ∃x φ(x) → φ(c).

Repeat over the expanded languages. Include ordinary C in the expanded language, but keep Max restricted to the original pure terms. These witness axioms preserve consistency: a model of the old theory can interpret each fresh c by a witness when one exists and arbitrarily otherwise. Every finite initial group of witness axioms admits such successive expansions. Equivalently, use the usual syntactic Henkin argument for H, as in Bacon–Dorr Theorem 3.2, n.64. The resulting witness theory T_H is A-c.e. and consistent.

Enumerate all closed sentences of the expanded language. A binary sequence can select each sentence or its negation. The condition that all finite selections are consistent with T_H is a nonempty Π^0_1(A) class: a violation has a finite proof of contradiction using finitely many A-enumerated axioms. This class can be represented by the paths of an A-computable binary tree (bound proof/axiom searches by the node length). Every path gives a consistent complete extension containing the witness axioms. By the relativized Low Basis Theorem it has a member X with

    (X⊕A)′ ≡_T A′ = 0′′.

Reading the selected literals as a complete deductively closed Henkin theory, define terms equivalent iff X contains their identity. In each type choose the least coded closed term in each equivalence class as representative. Membership in the representative domain is X-decidable: only the finitely many earlier same-type term codes need to be compared. The value of a term under a finite assignment of representatives is computed by substituting their closed terms and selecting the least equivalent representative. Truth of a proposition representative P is decided by whether X contains P. These data form the BBK term model of X. All of its interpretation operations and its truth map are X-computable.

Let D be the corresponding code, with equality and uniform term interpretation explicitly included. Then D≤_T X⊕A, so D′≤_T0′′. Since M satisfies Max, §4 gives A≤_T D; hence A′≤_T D′. Thus D′≡_T0′′. Also D≤_T D′ gives D≤_T0′′, and equality D≡_T0′′ would give D′≡_T0′′′, impossible. This proves (7). The full elementary diagram under this numbering is also computable in X⊕A by term substitution and truth lookup, and its jump is likewise exactly 0′′.

The strict lower inequality in (7) uses the additional arithmetic argument of §8 below; the Low Basis argument by itself yields only 0′≤D. Being low relative to 0′ means the *join with 0′ has jump 0′′*; it does not mean computable in 0′. No effective conversion of the resulting BBK code into a comparably low action-model/category code has been proved. Classical semantic equivalence is not automatically a degree-preserving equivalence of presentations.

## 6. Rigorous comparison with the two positive theories

Let P denote either C+Box Plenitude (equivalently the recorded C5+Atomicity preset) or C+Box Functional Choice, with the indicated schema instantiated effectively over the admitted types. Each is c.e. Full ordinary extensional models establish consistency in the usual choice metatheory; one can add the individual Axiom of Infinity and use an infinite full ordinary extensional model. This is a consistency witness, not a countable effective presentation of that full hierarchy.

For each consistent c.e. P, the argument of §5 with A=∅ yields a countable BBK model whose full interpretation-and-truth code D_P is low:

    D_P′ ≡_T 0′.

Thus D_P does not compute 0′. This gives an actual uniform-presentation complexity separation:

- both positive theories, even with any consistent c.e. Infinity addition, have low countable BBK models;
- every term-effective countable Max model computes 0′;
- Max has countable BBK models low relative to 0′.

This is a separation between classes of available effective presentations. It does not claim all positive-theory models are low, nor that either positive theory is decidable, nor that all Max models have degree 0′. No comparison between the two positive theories follows from this particular invariant: both lie on its c.e./low-model side.

Without Infinity, a full extensional model on a singleton individual domain has finite effectively computed domains at each fixed type and can be uniformly coded effectively across types. Such a model satisfies both positive theories. With individual Infinity, that finite-domain example is unavailable; the low-model existence statement remains, but a computable model must not be asserted on this argument.

## 7. Further consequences and boundaries

**Theoremhood bound.** Th(Max) is c.e. in 0′, hence Σ^0_2. Section 10 proves that it is in fact Σ^0_2-complete under ordinary computable many-one reductions, hence of degree 0′′. A low-relative complete model diagram can lie strictly below 0′′ while extending Th(Max): it does not thereby decide whether an arbitrary sentence belongs to the incomplete theory Th(Max).

**Finite effective additions.** For any finite or c.e. S consistent with Max, no consistent c.e. theory can axiomatize or consistently strengthen Max+S. The pure equality diagram remains exactly E_C. These conclusions survive optional Infinity without using it in the lower-bound proof.

**No recursively enumerable list of all correct negative pure identities.** The actual negative pure equality diagram in any Max model is the complement of a Σ^0_1-complete set. If it were c.e., E_C would be decidable. This remains true even though positive equalities do have an effective enumeration.

**No inference about Strong Possibility's consistency.** Any consistent theory implying Max inherits the effective lower bounds. For Strong Possibility one must keep its unproved consistency separate. A stronger schema's non-effectiveness never proves it inconsistent.

**Still unclassified here:** exact degree spectra up to isomorphism (as opposed to the oracle-capacity characterization in §9); degree-preserving effective versions of BBK/action/Gallin representation; the strength of bare structural codes lacking term evaluation and truth. Sections 8–10 settle the previously tentative questions about 0′-computable full BBK codes and arithmetical completeness of Th(Max).

## 8. A definable correct halting predicate, and a stronger model lower bound

Fix the counting type e, put ν=(et)t, and let N, 0, Suc, Sum, Prod, I* and I have exactly their definitions in `background.md`; in particular I=Diamond I*. The recorded Goodsell arithmetic argument supplies:

1. C+I interprets first-order Peano arithmetic on N, with Sum and Prod as graphs of addition and multiplication. This is the source's Lemma 1, invoked explicitly in `writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`, Lemma 7, and in `results/possibility-and-necessity-of-arithmetic-incompatible.yaml`.
2. The impredicative definition of N gives induction for **every** formula of the higher-order language with numerical variable, using its lambda abstraction as the induction property. Thus induction remains available for arithmetic expanded by a predicate defined using Box, parameters, and higher-order quantifiers. It is not restricted to the narrow recorded “arithmetical sentence” schema.
3. I* is C-consistent in the full infinite extensional model. Max therefore entails I by its possibility form. No optional hypothesis is necessitated in this step.

Let h(n) be one fixed arithmetic formula saying that ordinary machine n halts on input n, with arithmetic translated to N, Sum and Prod. Use any usual effective numbering of machines and its finite-computation arithmetization. Define the pure property of numbers

    J(n) := Box(I → h(n)).                          (8)

**Lemma 8.1.** For every standard n and every Max model M,

    M⊨J(numeral n)  iff  n∈0′.

Proof. If n halts, its finite computation has an ordinary PA verification. By the interpretation in 1, C+I proves h(numeral n), so C proves I→h(numeral n). Theorem necessitation in C makes J(numeral n) a C-theorem. Conversely, if n does not halt, the full infinite extensional model has standard Frege numbers, I is true, and h(numeral n) is false. Thus C does not prove I→h(numeral n), equivalently does not prove the closed pure identity (I→h(numeral n))=top. Max makes this identity false, which is ¬J(numeral n). This proves both directions. Notice the Box applies to the entire conditional: it is never inferred from I as an unboxed optional hypothesis. □

Let H_b(n,J) be the arithmetic formula saying that oracle machine n, on input n and with oracle J, halts with output bit b, b∈{0,1}. This is a uniform finite-computation formula in first-order arithmetic with a unary predicate, interpreted in the admitted higher-order language by the pure definition (8). Standard machine coding, sequence coding, and determinism are provable in PA with full induction in this expanded language. No type with output e is used: numerical objects have the relational type ν.

**Lemma 8.2.** Every complete actual pure theory Y of a Max model computes a binary diagonally nonrecursive function relative to 0′.

Set

    d(n)=1 if H_0(numeral n,J) belongs to Y,
         0 otherwise.                              (9)

This is Y-computable. If the actual 0′-oracle computation of machine n on n halts with output 0, it uses only finitely many standard oracle queries. All their correct answers are facts of Max by Lemma 8.1. Its finite computation is therefore verified in M, so H_0 is true and d(n)=1. If its actual output is 1, the same reasoning proves H_1 in M. Internal determinism forbids H_0, so d(n)=0. Thus whenever the actual partial 0′-oracle machine φ_n^{0′}(n) converges to a bit, d(n) differs from it. This is binary DNR relative to 0′. If the computation diverges, d(n) may take either value; internally nonstandard apparent computations do not cause a problem. □

**Corollaries.**

- No complete actual pure theory of Max is computable in 0′. A 0′-computable total binary d has an oracle-program index e, whence d(e)=φ_e^{0′}(e), contradicting DNR.
- No full BBK code giving uniform term interpretation **and truth valuation** is computable in 0′, because it computes the complete actual pure theory by interpreting and valuing each closed pure formula.
- Such a code has a PA degree relative to 0′, where here this means it computes a binary DNR function relative to 0′. This is strictly stronger than merely computing 0′.
- The argument needs neither external standardness of M's arithmetic nor Tennenbaum's theorem. Correctness on standard oracle queries plus internal deterministic finite-computation arithmetic suffices.

A binary DNR function relative to A already computes A: uniformly compile a program with index e(k) which ignores its input, asks oracle A whether k∈A, and outputs that bit. Then A(k)=1−d(e(k)). This verifies explicitly that the degree notion used here includes the base oracle.

The conclusion for full BBK codes is stronger than the conclusion for the weaker term/equality-only code in §4. Do not merge them without including the valuation or another effective way to recover actual truth.

### 8.3 A smaller presentation sufficient for the same degree lower bound

Uniform interpretation of every term is more than the DNR argument requires. Suppose a presentation of a Max BBK model supplies effective sorted domain enumerations, equality, the application graphs, and its actual truth valuation on proposition objects, all relative to one oracle D. Total application can be computed by searching its decidable graph. No global lambda-term interpreter is assumed.

Hardcode the presentation indices of the following three denotations, which exist in every such model:

    0_ν,       Suc_ν:ν→ν,       G:=λn^ν.H_0(n,J):ν→t.

From input k, iterate application of Suc to 0 exactly k times, apply G to the result, and read its actual truth value. Output 1 for true and 0 for false. This is exactly the DNR function of Lemma 8.2. Therefore D has PA degree relative to 0′ even for this weaker application-plus-valuation encoding.

The finite indices need not be uniformly discoverable from an unnamed raw presentation. The argument is a valid Turing-degree lower bound because finitely many indices may be built into the reduction for each presentation; if these three denotations are explicitly named, extraction is uniform. No claim is made that equality and application alone recover actual truth.

The adequate-model upper construction in §9 also supplies these weaker data. Hence the exact **oracle capacity** for obtaining some countable BBK presentation with application, equality and actual valuation is still PA degree relative to 0′. This is not a claim about the exact degree spectrum of an isomorphism type, nor a uniform Medvedev equivalence for all unnamed atomic-style codes.

## 9. Exact oracle capacity for countable full BBK model construction

For an oracle X, the following are equivalent:

1. X computes a countable BBK model of pure Max, including its uniform term-interpretation function and truth valuation.
2. X computes a complete actual pure theory extending Max.
3. X computes a binary DNR function relative to 0′ (equivalently, X has PA degree relative to 0′).

The implication 1⇒2 is evaluation; 2⇒3 is Lemma 8.2. We prove 3⇒1 directly, avoiding an unproved effective representation theorem.

Let d≤_T X be binary DNR relative to A=0′. As just observed, d computes A. Form the consistent A-c.e. Henkin witness theory T_H from §5. Enumerate all expanded-language sentences φ_0,φ_1,… . Suppose a finite set Δ has been chosen with T_H+Δ consistent. Uniformly compile an A-oracle program e(Δ,φ_s) which ignores its input and searches proofs from T_H+Δ in parallel, returning 0 if it finds a proof of φ_s and returning 1 if it finds a proof of ¬φ_s. Consistency ensures that both alternatives cannot happen. Define the next choice as follows:

    if d(e(Δ,φ_s))=1, add φ_s;
    if d(e(Δ,φ_s))=0, add ¬φ_s.

If T_H+Δ already proves φ_s, DNR forces the first choice; if it proves ¬φ_s, DNR forces the second. If neither is provable, either extension is consistent by classical logic and the deduction theorem. Thus the process preserves consistency at each step and decides every sentence. It is d-computable: the compilation of the proof-search program is effective, while the program itself uses its built-in oracle A; d also supplies A when required for enumerations.

The chosen complete consistent witness theory yields an X-computable countable BBK term model by the explicit representative construction of §5. This proves 3⇒1.

Therefore there is an exact separation between two tasks:

    consistent effective axiomatization of Max:    oracle cone above 0′;
    computing one complete full BBK model of Max: PA degrees over 0′.

The latter is not simply the cone above 0′′. By the relativized Low Basis Theorem there are PA degrees over 0′ strictly below 0′′ with jump exactly 0′′, giving the strict lower inequality asserted in (7). This characterizes which oracles **can compute a model**; it does not claim that every such oracle is the exact degree of a presentation of a fixed isomorphism type.

The same equivalence holds after any fixed c.e. pure addition S consistent with Max. The lower bound is inherited from Max; the upper construction uses the A-c.e. theory Max+S. In particular it applies after adding the individual Axiom of Infinity, whose consistency is recorded.

## 10. Exact Σ^0_2-completeness of Max theoremhood

The A-c.e. upper bound for Th(Max), A=0′, was already established. To obtain ordinary computable many-one hardness, we use the **existing full coalesced maximalist root**, not a new model construction. Its free-root-component condition is stated in `groups/coalesced-sums.yaml`; the standardness observation is explicit in the Axiom-of-Infinity argument of `models/coalesced-maximalist-root.yaml` (Cian Dorr, recorded 22 September 2026).

### 10.1 Why its internal N_e is standard

Let R be this root and write n_R for the denotation of the closed e-counting Frege numeral n. The n_R are pairwise distinct: for n≠m an ordinary full extensional model with enough individuals separates their cardinality predicates, so the identity of the two pure numeral terms is not a C-theorem and is false in R by Max.

The full root domains allow a property W of cardinalities (type νt) whose actual extension is exactly

    S={n_R:n∈ω},

and whose component predicates are universal in every component. This is a legitimate root entity by the arbitrary root-extension clause. At the root W0 holds and W is successor-closed: Suc(n_R)=(n+1)_R by interpretation of the pure numeral terms. The impredicative definition of N therefore gives N_R⊆S. Conversely each n_R satisfies N by the ordinary finite proof, so S⊆N_R. Hence

    N_R={n_R:n∈ω}, with 0 and Suc the standard operations.

### 10.2 Why Sum and Prod are standard, with the actual definitions

The definitions from `background.md` use R' of type ννt, with applications left-parenthesized even though the bundle's notation associates application to the right:

    Sum(m,n,o) iff every R' satisfying R'(0,m) and
       ∀i,j∈N [R'(i,j)→R'(Suc i,Suc j)] satisfies R'(n,o).

For standard m,n, finite iteration proves Sum(m_R,n_R,(m+n)_R). If o≠m+n, choose a root relation R' whose actual extension is exactly

    {(k_R,(m+k)_R):k∈ω},

with universal component relations. It is admitted by root fullness, satisfies the stated base and closure conditions, and fails at (n_R,o_R). Thus the wrong Sum instance is false.

Similarly, Prod(m,n,o) says every R' satisfying R'(0,0) and

    ∀i,j,k∈N [R'(i,j)∧Sum(m,j,k)→R'(Suc i,k)]

satisfies R'(n,o). Finite iteration using the already established Sum instances proves Prod(m_R,n_R,(mn)_R). For o≠mn, the admitted root relation with actual extension

    {(k_R,(mk)_R):k∈ω}

and universal component relations satisfies the base and closure clauses but excludes (n_R,o_R). Therefore the arithmetic reduct of R, with number quantifiers restricted to N, is precisely standard arithmetic. Every displayed type ν, νt and ννt is admitted, and no numerical operation into the individual type e has been postulated.

### 10.3 The reduction

By Lemma 8.1, J agrees with 0′ on every standard numeral in every Max model. Since every number of R is a standard numeral, J's entire numerical extension in R is exactly 0′. Let Q_n be the pure sentence H(numeral n,J) asserting that oracle machine n on n with oracle J halts (with any output). The map n↦Q_n is ordinary computable: H and J are fixed finite formulas and only the numeral is varied.

If n∈0′′, the actual finite 0′-oracle computation involves finitely many standard oracle answers. Max proves all their correct J-literals by Lemma 8.1, proves I, and consequently proves this finite computation in its interpreted arithmetic. Hence Max⊢Q_n.

If n∉0′′, the standard arithmetic reduct of the existing maximalist root R, expanded by J=0′, falsifies Q_n. Soundness therefore gives Max⊬Q_n.

Thus

    n∈0′′  iff  Max⊢Q_n,

an ordinary computable many-one reduction. Together with the upper bound this proves:

    Th(Max) is Σ^0_2-complete and has degree exactly 0′′.   (10)

It follows also that the set of pure P for which Max+P is consistent is Π^0_2-complete: inconsistency is equivalent to Max proving ¬P, and use P=¬Q_n in the displayed reduction.

The same standard-model hardness argument applies to Max plus the individual Axiom of Infinity, since R satisfies that axiom as recorded. For arbitrary c.e. additions S, this particular standard-model argument requires a separate standard-arithmetic model. The following independent argument eliminates that requirement entirely.

### 10.4 Stronger theorem without a standard-arithmetic model

**Theorem.** Every consistent 0′-c.e. theory T whose consequences contain Max has a Σ^0_2-complete set of pure theorems. Thus (10) continues to hold after *any* 0′-c.e. addition consistent with Max, whether or not it has a standard-arithmetic root.

Put A=0′. Use the fixed pure oracle-computation formulas H_0(n,J), H_1(n,J) of §8. Define

    V_b = {n : T⊢H_b(numeral n,J)},  b=0,1.

These are A-c.e. sets. They are disjoint: T includes the interpreted arithmetic proof that one deterministic computation cannot halt with both distinct output bits, and T is consistent. They contain the respective diagonal halting sets

    K_b^A = {n : φ_n^A(n) converges with output b},

because every actual finite A-oracle computation is verified in T using the finitely many correct J-facts supplied by Max.

Here is a direct reduction showing that any such disjoint A-c.e. supersets V_0,V_1 force V_0 to be A-c.e.-complete. By the parameterized recursion theorem for oracle-machine indices, there is an **ordinary computable** function p(n) such that the A-oracle program with index p(n), ignoring its input, dovetails these two searches:

1. If machine n with oracle A on input n halts, output 0.
2. If p(n) is enumerated into V_0, output 1.

Return when the first search succeeds (use any fixed tie convention). The compilation is ordinary computable: oracle A is an oracle of the program being compiled, not an oracle queried by the index-building function. The enumeration index for V_0 is a fixed parameter. The recursion theorem supplies the program's own index p(n).

If n∉A′ and p(n)∈V_0, the second search eventually succeeds and the first never does. Thus φ_{p(n)}^A(p(n))=1, putting p(n) in K_1^A⊆V_1, contrary to disjointness. Hence n∉A′ implies p(n)∉V_0.

If n∈A′ but p(n)∉V_0, the first search eventually succeeds and the second never does. Thus φ_{p(n)}^A(p(n))=0, putting p(n) in K_0^A⊆V_0, contradiction. Hence n∈A′ implies p(n)∈V_0.

Consequently

    n∈0′′  iff p(n)∈V_0
            iff T⊢H_0(numeral p(n),J).

This is an ordinary computable many-one reduction from 0′′ to pure T-theoremhood. Its matching Σ^0_2 upper bound follows from T being 0′-c.e. This proves the theorem. It is the relevant effective-inseparability argument written out directly, rather than an appeal to arithmetic soundness or to an unproved completeness criterion. □

The standard-root construction in §§10.1–10.3 remains useful: it gives the especially transparent fixed-formula reduction n↦H(n,J) with no self-reference, and directly witnesses the truth values involved. Section 10.4 proves the stronger robustness statement.

## 11. Equivalent conservative-extension test

For a closed pure sentence S,

    Max+S consistent
       iff C+S proves no new closed pure identities over C.   (11)

The forward implication is immediate: a new identity would contradict its Max inequality axiom.

For the converse, if Max+S is inconsistent, finitely many Max inequalities suffice. Thus C+S proves a finite disjunction E_1∨…∨E_k of closed pure identities, none individually provable in C. Put P=E_1∨…∨E_k. By NI each E_i implies Box E_i; ordinary modal reasoning gives P→Box P, while T gives Box P→P. Hence C+S proves the single closed pure identity P=top. Conservativity implies C proves P=top, hence C proves P. But Max consistently extends C and includes ¬E_i for every i, contradicting P. Therefore Max+S must be consistent. The empty-disjunction case is simply inconsistency of C+S, which proves the new identity bot=top.

Consequently, for finite pure S (represented by its conjunction), the conservative-extension test has exact Π^0_2 complexity by §10. Directly its quantifier pattern is also Π^0_2: every finite C+S proof of a pure identity must have some finite C proof of that identity. This characterization does not itself lower the oracle needed to construct a complete model.

## 12. Audit and validation status

Sections 8–11 are the later sharpenings; they supersede the initial tentative possibility of a full 0′-computable model. The root agent separately checked the standard-root arithmetic premise against the coalesced record. No claim of literature novelty, human checking, or formal verification is made. The base non-r.e. result remains attributed to Bacon–Dorr.

No repository file was edited. Nevertheless `python3 scripts/pmap.py validate` was run using the existing `/tmp/classicism-research-venv` runtime and passed: 132 principles, 447 results, 162 models. The system Python lacked the existing dependencies; no packages were installed.

## 13. Standard Max: analytic finite-condition complexity, fixed identity complexity

Let M_std be the class of models of the original Max_C with externally standard N_e at the actual point. We may use arbitrary models or countable adequate BBK presentations: the two have the same finite-condition satisfiability, by the witness construction below. No standardness is imposed at other worlds, and no change is made to Max's original reference language or theory C.

For closed pure P write Sat_std^Max(P) when some model in M_std satisfies P, and Val_std^Max(P) when every such model satisfies P. Then, under ordinary computable many-one reductions,

    Sat_std^Max is Sigma^1_1-complete,
    Val_std^Max is Pi^1_1-complete.                            (13.1)

These are semantic decision problems for an externally restricted class. Ordinary finitary Max theoremhood remains Sigma^0_2-complete.

### 13.1 Analytic upper bound

The complete witnessed BBK code class for Max is Pi^0_1(0′). Add, for every closed numerical term u in the witness language, the condition

    Nu belongs to D  implies  exists standard n [u=numeral_e(n) belongs to D].

This is Pi^0_2 in the decision code D; together with the fixed arithmetical oracle 0′, it gives a lightface arithmetical code class K_std^Max. Adding witnesses to a standard model preserves its actual numerical domain. Conversely the usual BBK term construction from D makes every numerical object a named standard numeral. Thus

    Sat_std^Max(P) iff exists D in K_std^Max [P belongs to D].

This is Sigma^1_1. Computable negation gives the Pi^1_1 upper bound for validity. The code construction is the one in `positive-effective.md` §20, including the restriction that fresh witness constants do not enlarge Max_C's reference scheme.

### 13.2 Arbitrary numerical graphs at the recorded coalesced root

Let R be the already recorded full coalesced maximalist root. Section 10.1 proves that its actual N_e consists exactly of its pairwise distinct standard numerals n_R, and §10.2 verifies the standard graphs of addition and multiplication. The relevant construction clause is `topics/classicism/groups/coalesced-sums.yaml`, parameter `domains: fullest` and condition `free-root-component`: a root relational entity has an arbitrary root function, together with its component entities. The source is Bacon–Dorr, *Classicism*, 16 May 2023 draft, Appendix E, Definition E.2, pp.80–83; the standardness argument is explicitly recorded under Cian Dorr's name, 22 September 2026, in `models/coalesced-maximalist-root.yaml`.

For every external function f:omega→omega, this root contains a relation F_f of the admitted type nu→nu→t, nu=(et)t, with actual extension

    {(n_R,f(n)_R):n in omega},                                (13.2)

false on other root pairs, and universal relations in every component. This choice respects currying: for each first root argument, the resulting nu→t object has the desired actual row and universal component predicates, exactly the components prescribed by the universal component relation. No persistence condition constrains the actual row. We have selected an entity already present in the existing full root, not altered a component or added a new model construction.

Choose a fixed Sigma^1_1-complete set S in recursive tree normal form:

    e in S iff exists f:omega→omega forall s R_0(e,f restricted to s,s),

where R_0 is recursive and finite sequences are coded by ordinary natural numbers. Equivalently, S is ill-foundedness for a uniformly recursive family of trees on omega^{<omega}; infinitely branching trees are essential here. This is the normal form used and sourced in `positive-effective.md` §21.2.

Let Fun_N(F) express that F is total and single-valued on N_e×N_e. Let Prefix(F,s,c) arithmetically assert that c codes its first s values. Translate the fixed recursive R_0 into standard arithmetic on N_e, and form the closed pure sentence

    P_e := exists F^(nu nu t) [Fun_N(F) and
              forall s in N_e exists c in N_e
                (Prefix(F,s,c) and R_0#(numeral e,c,s))].       (13.3)

The map e↦P_e is computable. In every standard-N_e Max model, an F witnessing P_e yields an actual external function f:omega→omega. Standardness makes finite-sequence coding, Prefix and R_0# absolute, so e belongs to S. This direction needs no external fullness or Choice.

Conversely, if e belongs to S, choose a branch f. The relation F_f in (13.2) witnesses P_e at R. Its actual arithmetic is standard, so all clauses in (13.3) hold. Hence e in S iff Sat_std^Max(P_e), proving the lower bound in (13.1). If a countable adequate model is required, expand R by witnesses including the witness to P_e and apply §13.1's term construction. The resulting actual N_e is still standard.

### 13.3 The closed pure identity fragment stays Sigma^0_1-complete

Every Max model, including every standard one, has the same closed pure identity diagram. The class M_std is nonempty by R. Consequently, for every closed pure identity E,

    Sat_std^Max(E) iff Val_std^Max(E) iff C proves E.            (13.4)

Both identity-restricted problems are therefore exactly the Sigma^0_1-complete set E_C, of Turing degree 0′. For disequalities the corresponding set is its Pi^0_1-complete complement. More generally the truth of any finite Boolean combination of closed pure identities is fixed across M_std and decidable in 0′.

There is no conflict with full validity being Pi^1_1-complete. Max does not identify actual truth of an arbitrary pure P with the identity P=top. The positive standard Gallin classes in `positive-effective.md` §21.3 satisfy No Pure Contingency and do have that equivalence, so their identity-validity fragment is already Pi^1_1-complete. Standard Max instead combines a fixed arithmetical pure identity diagram with nonhyperarithmetical actual pure theories and analytic-complete finite-condition satisfiability.

### 13.4 The full root and the smaller standard theories are different

The full coalesced root R itself satisfies P_e exactly when the external recursive tree has a branch: the forward implication uses its standard arithmetic, and the reverse implication uses its arbitrary root graphs. Hence its complete actual pure theory computes Kleene's O, since recursive-tree ill-foundedness is Sigma^1_1-complete.

By contrast, the analytic basis theorem in `positive-effective.md` §20 supplies other standard Max theories strictly below O. Those theories cannot all agree with R on the P_e. A countable BBK model preserving R's entire actual pure theory still computes O; it is not one of those sub-O examples. The sub-O standard models have restricted actual relation domains and omit some external recursive-tree branches. Their standard arithmetic remains correct, and their closed pure identity diagrams remain exactly E_C.

Section 13 was independently checked by the positive-model research lane against the recorded free-root-component clause. This is an internal mathematical audit, not a claim of human checking or formal verification.
