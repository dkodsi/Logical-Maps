# Effective completion spaces, infinitary Boolean descriptions, and the pure term quotient

Research note by OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematics; no Lean work and no database edits. This extends `max-degree.md` and cross-checks `theory-space-comparison.md` §§8–9. No literature-novelty claim is made.

## 1. The coding and established inputs

Fix an effective enumeration P_0,P_1,… of closed pure sentences of the fixed relational-type language. Code a complete theory by its characteristic function Y∈2^ω. Write S(T) for the complete consistent pure extensions of T, coded this way. In particular S(C) is an effectively closed (Π^0_1) subset of Cantor space: failures of including an enumerated C-theorem, closure under a finite inference, or consistency/completeness have finite enumerable witnesses. Equivalently enumerate all finite bit patterns inconsistent with C.

This is the *absolute Cantor-space coding*. Relative to the Stone space S(C), a finite extra pure condition is clopen. Absolute and relative claims must not be conflated.

The companion notes establish:

- C and the positive theories B=C+□Plenitude and F=C+□Functional Choice are c.e.
- E_C, the closed pure C-identity theorem set, is Σ^0_1-complete.
- Max is consistent and c.e. in 0′.
- Every complete pure extension of Max computes binary DNR relative to 0′, using the pure numerical predicate J(n)=□(I→h(n)) described in `max-degree.md` §8. Hence no member of S(Max) is computable in 0′.
- If T is C, B or F with at least one weak Infinity schema at e or t, every member of S(T) computes binary DNR and hence a PA completion. Thus no member is computable. These T have countable adequate models and low completions. A quantified Frege Axiom of Infinity is sufficient but not required: `positive-effective.md` §16 uses finite relational computation certificates and finite prefix simulation, without asserting an internal PA interpretation from weak Infinity.

Here Σ^0_n and Π^0_n for sets of reals mean the lightface effective Borel/arithmetical pointclasses in this fixed recursive coding. Ordinary topological closedness is a separate notion: a closed set need not be effectively closed.

## 2. An exact effective-Borel separation

**Theorem 2.1.** S(Max) is Π^0_2, is not Σ^0_2, and contains no nonempty Σ^0_2 subclass.

Enumerate the closed pure identities E_i. Let Prf_C(i,s) be the decidable predicate saying that a certified C-proof of E_i has appeared by enumeration stage s. Certification includes the finite H-proofs needed for uses of Logical Equivalence. For Y∈S(C),

    Y∈S(Max)
       iff ∀i [Y(E_i)=0 or ∃s Prf_C(i,s)].           (1)

Indeed, a complete C-theory already accepts every proved identity, and Max requires every other identity to be false. Formula (1), together with the Π^0_1 condition Y∈S(C), is Π^0_2.

For the stronger negative assertion, suppose A⊆S(Max) is a nonempty effective Σ^0_2 class. Write A=⋃_n K_n with K_n uniformly effectively closed. Some K_n is nonempty. The Low Basis Theorem supplies a low Y∈K_n; in particular Y≤_T0′. This contradicts the DNR-relative-to-0′ lower bound for every Max completion. Thus no such A exists. □

This also rules out nonempty relatively effective Σ^0_2 subclasses inside S(C): intersecting an absolute Σ^0_2 class with the Π^0_1 class S(C) remains Σ^0_2.

**Theorem 2.2.** For T among C, B and F with at least one weak Infinity schema at e or t, and optionally the consistent quantified Frege Infinity additions considered in the companion note, S(T) is a nonempty Π^0_1 class, is not Σ^0_1, and contains no nonempty effective Σ^0_1 subclass.

The Π^0_1 upper bound follows from T being c.e. A nonempty open subset of Cantor space contains a basic cylinder, and thus a computable point obtained by extending its finite defining string with zeroes. No point of S(T) can be computable, since the finite-computation construction gives binary DNR. Therefore no nonempty effective open class can be contained in S(T). □

Absolute nonopenness alone is weaker than the PA-degree theorem: in the unrestricted sentence-bit coding, the coherence requirements on complete theories already exclude every whole Cantor cylinder, even without Infinity. The substantive computational positive result is the uniform PA threshold and availability of low solutions. The proof above is valid, but its Infinity hypothesis must not be presented as necessary merely for absolute nonopenness.

These are exact **effective-description levels**, not a claim that Max's completion space is topologically G_delta but not closed. In fact S(Max) is topologically closed and, by the independent Stone-space argument, homeomorphic to Cantor space. Nor can it be Π^0_2-complete under arbitrary continuous preimages in the usual Wadge sense: every continuous preimage of this topologically closed set is closed. The statement is membership in Π^0_2 but not Σ^0_2 in its given effective coding, with the stronger subclass exclusion proved above.

The positive theorem concerns absolute coding. It does not contradict B's clopen position *relative to S(C)*, including after finite quantified Infinity additions.

## 3. Uniform completion problems: a stronger result than oracle capacity

For A⊆ω, let DNR_2^A be the class of total binary functions d such that

    d(n)≠φ_n^A(n) whenever φ_n^A(n) converges to 0 or 1.

View such d as elements of Cantor space. Say that a mass problem Q is reducible to P when one fixed computable functional transforms every solution of P into a solution of Q. This is Medvedev reducibility; no oracle is supplied to the transforming functional. A functional may be partial off its specified input class.

**Theorem 3.1.** S(Max) is uniformly equivalent, in this sense, to DNR_2^{0′}.

The forward transformation is explicit. Given Y∈S(Max), define

    d(n)=1 iff H_0(numeral n,J)∈Y,

where the fixed pure formula H_0 expresses an oracle computation with output 0. The finite-computation proof in `max-degree.md` §8 shows this is binary DNR relative to 0′. Membership of this computably generated sentence is a single oracle query to Y. Thus the functional is uniform and uses no supplied 0′ oracle.

Conversely, given d∈DNR_2^{0′}, use the explicit Henkin-completion algorithm of `max-degree.md` §9. At each finite consistent stage Δ and next sentence φ, compile the oracle program that searches proofs of φ and ¬φ from the fixed 0′-c.e. witness theory plus Δ, outputting 0 on the former and 1 on the latter. Query d at that program index and choose φ exactly when d returns 1. The index compilation is computable; the compiled program, rather than the transforming functional, has the 0′ oracle. DNR forces the consistent choice whenever only one choice is possible. The union is a complete consistent witness theory. Restrict it to the original pure sentences to obtain an element of S(Max). All steps are uniform in d.

If the construction needs direct 0′ queries for an auxiliary operation, d computes them uniformly: compile e(k) to query its oracle's kth bit and return it; then 0′(k)=1−d(e(k)). No additional oracle is hidden in the transformation. □

**Theorem 3.2.** For each fixed consistent positive package T of §2.2, S(T) is uniformly equivalent to DNR_2.

Given a completion, use the pure finite-trace sentence H_e of `positive-effective.md` §16 and set d(e)=1 exactly when H_e belongs to the completion. A genuine output-0 computation has finite witnesses from one Infinity instance; a genuine output-1 computation makes H_e refutable in C by finite prefix simulation. Thus d is binary DNR without requiring an internal PA interpretation. Given DNR_2, apply the preceding completion algorithm with the empty base oracle to a fixed consistent c.e. Henkin theory for the stronger positive package. The positive lane gives an auxiliary Gallin theory when a general Gallin model is desired; its restriction supplies a completion of T. See `positive-effective.md` §§15–16 for the independently written algorithms.

These equivalences do not say that the constructed completion has exactly the same degree as the input, nor that the construction preserves a completion given at its input. They compare uniform tasks of obtaining *some* completion/model of the fixed theory.

### Strictness and conversion direction

There is a uniform conversion from Max completions to positive completions with weak or strong Infinity: produce DNR_2^{0′}, restrict it to an effective list of oracle programs that ignore their oracle, and then run the positive completion construction. Thus the positive problem reduces to the Max problem.

The reverse conversion is impossible, even if the purported functional is permitted the fixed oracle 0′. A positive completion space has a low member Y, hence Y≤_T0′. A 0′-computable functional applied to this Y could output only a set computable in 0′, whereas no Max completion is computable in 0′. In particular there is no computable uniform way to turn arbitrary positive completions into Max completions.

This is a rigorous problem-level distinction. It neither ranks every positive model against every Max model nor asserts an absolute semantic-complexity order between B and F.

## 4. The least effective infinitary Boolean rank for describing old Max

The following is about an explicitly defined infinitary extension, not about a new maximalization reference theory. Allow effective countable Boolean conjunctions and disjunctions **of the old closed finitary pure sentences**, interpreted classically at an evaluation point. Treat those old sentences as the clopen atoms of the Boolean description. “Rank” below is the effective Boolean/Borel rank; it is not the quantifier rank of raw higher-order infinitary syntax, since the old finite sentences can have unbounded object-quantifier complexity.

For each identity E_i and stage s let B_{i,s} be the old pure sentence top if Prf_C(i,s), and bottom otherwise. Define

    Φ_Max := AND_i [ (NOT E_i) OR OR_s B_{i,s} ].    (2)

The syntax of (2) is computably generated. Its inner disjunction is true exactly when E_i has an actual finite C-proof. Therefore, over C, (2) is equivalent to the original pure Max schema, with exactly the original reference theory C. This is a computable Π_2 Boolean infinitary description.

There is no equivalent effective Σ_2 Boolean description over C. Such a description would define a relatively effective Σ^0_2 subclass of S(C), hence an absolute Σ^0_2 class equal to S(Max), contradicting Theorem 2.1. In particular there is no effective Π_1 Boolean conjunction of old finitary conditions whose models are a nonempty subclass of Max's complete theories: every such class would be Σ^0_2 as well.

With 0′ as an external oracle one can simply enumerate the correct Max inequalities and take a Π_1 conjunction. Section 3 of `max-degree.md` already gives the exact oracle threshold for this effective finitary axiomatization task.

**Standard proof codes are essential.** The inner OR_s in (2) ranges over the actual external natural numbers indexing finite proof certificates. Replacing it by a first-order existential quantifier over a possibly nonstandard internal number domain can admit nonstandard apparent proofs and need not express old Max. Likewise, changing the reference logic from finitary C to an infinitary C_infinity changes the side condition itself; none of the present exact degree claims automatically transfers to that different theory.

The proof-gated infinitary formula does not supply an effective finitary completeness theorem. Its existence is compatible with Σ^0_2-complete Max theoremhood and with the absence of effective finitary auxiliary theories forcing Max.

This Boolean-description extension does not assert lambda comprehension for arbitrary open infinitary formulas. That stronger closure would admit λn.∨_(k<ω)(n=numeral k), which the separate note `infinitary-standard-numerals-20261022.md` shows incompatible with the old Max reference at all accessible worlds. An external/evaluation-point Boolean description and a new globally lambda-closed infinitary logic must therefore remain distinct.

## 5. Hidden-code obstructions at the completion level

Let K⊆2^ω be any nonempty effective Σ^0_2 class of auxiliary codes, and let F be a computable functional defined on every member of K. It is impossible that F(K)⊆S(Max).

Proof: K has a low member by the same closed-component/Low Basis argument as §2. The image of this member is computable in a low degree, and hence computable in 0′, contradicting the Max lower bound. The same conclusion holds for a functional allowed the oracle 0′, because the selected input is itself computable in 0′. □

This applies to proposed effective families of auxiliary **completion codes** with an effective forgetful interpretation. It must not be silently applied to arbitrary spaces of raw countable structures, category codes, or arbitrary functions. Those spaces often impose totality or witness conditions of higher effective rank, may use Baire-space rather than compact Cantor-space codes, and may omit the effective term interpretation or valuation needed to recover a complete pure theory. Neither the Low Basis hypothesis nor the forgetful computation is automatic there.

## 6. Exact complexity of the canonical pure term quotient

There is a simple, canonical syntactic object common to every Max model. For each admitted type σ, let Term_σ be the set of closed pure terms of that type. Define

    A ~ B iff C⊢A=B.

The relation is a congruence for every well-typed pure term context. Let F_C be the resulting many-sorted pure term algebra. For each Max model M the map

    [A] ↦ interpretation of A in M

is well-defined and injective in every sort, by the fixed pure equality diagram; it preserves all pure context operations. Thus all Max models contain the same canonical algebra of pure denotations, up to this canonical isomorphism.

There are two precise effective presentations:

1. **Computable quotient presentation.** Use term strings as representatives. Type checking and substitution/context operations are computable. Equality of classes is represented by the c.e. congruence E_C. Equality is not thereby decidable.
2. **Presentation with decidable equality and uniform term evaluation.** With oracle 0′ choose the least coded term in each E_C class. Representative membership is 0′-decidable by checking finitely many earlier terms; a context operation substitutes representative terms and returns the least equivalent result. This presents F_C in degree exactly 0′: the construction is 0′-effective, and its uniform term-evaluation/equality code computes E_C, which is 0′-complete.

This is an exact matching bound for the **pure term algebra**, and explains how a syntax construction can be simple while quotient equality is not computable.

### Why this is not a degree-0′ model of Max

F_C need not be a model of C at all. In the stipulated pure relational language there is no closed term of type e, so its individual sort is empty; H requires a nonempty individual domain. More generally the pure-term subalgebra need not contain witnesses for existential truths. It also has not been supplied with an actual truth valuation satisfying the quantifier clauses. A syntactic quotient cannot be promoted to a Henkin/BBK model just by calling its classes the domains.

Each Max model does induce a valuation on its pure-denotation algebra, but a full code of that valuation together with the canonical 0′ term algebra computes its complete actual pure theory. Consequently this augmented code must compute binary DNR relative to 0′. In particular an actual valuation arising from a Max model cannot be added to the canonical presentation with only 0′-computable data.

The uniform theorem does not settle whether some full Max model admits a degree-0′ code of its larger domain and **term/equality operations alone**, omitting the valuation. That remains a different presentation problem. The proved matching degree-0′ object here is only the canonical pure term algebra, whose missing individuals, witnesses and truth have been expressly identified.

The lower bound for a full model's application/equality code does not require a uniform interpreter for every pure term. As detailed in `max-degree.md` §4, hardcode zero, successor, top and λn.(I→h(n)); application plus equality then decides 0′. This improves the encoding hypothesis for the lower bound, while leaving the missing full-model upper bound unresolved.

## 7. Cross-audit and source boundary

The arguments in `theory-space-comparison.md` §§8–9 were independently checked: isolated Max completion would become 0′-decidable; relative-low completion density gives the claimed strict degree bounds after restriction; Cantor-space homeomorphism is separated from ambient clopen/nowhere-dense position; and idempotence of maximalization follows from equality conservativity without necessitating new actual theorems.

The weaker-Infinity proof in `positive-effective.md` §16 was independently checked as well. Strict linearity makes all encountered value successors unique; the finite chain from zero fixes each standard zero/decrement test; and every actual prehalting state excludes the candidate final time. Thus an actual finite output-1 run forces the forbidden state before any nonstandard tail can matter. The output-0 finite λ-witnesses use only current-world equality and β, with admitted predicate types. These details justify the weakened assumptions in §§1–3 above.

The Low Basis theorem and its relativization are the sole basis-theorem inputs here; primary references and locators are supplied in `positive-effective.md` §6 and `max-degree.md` §0. The DNR constructions, proof gate, quotient analysis, and pointclass deductions are written out above. These are session proofs, not claims of novelty in the literature. The existing recorded C-model constructions and Goodsell arithmetic interpretation remain the sources of their respective ingredients.

## 8. Exact common information in the unrestricted model tasks

This section concerns arbitrary adequate general models/completions, allowing nonstandard arithmetic. It is deliberately different from `positive-effective.md` §§18–20, where external standardness changes the common information to all hyperarithmetical sets.

For each of the following fixed packages, use the indicated base oracle A:

| Package | A |
| --- | --- |
| C, B or F with one weak Infinity schema | the computable oracle |
| Pure Max_C | 0′ |
| Original pure SP, if consistent | 0′′ |
| A finite iterated T_n, if consistent | 0^(n) |
| The union T_ω, if all finite stages are consistent | 0^(ω) |

Let Sol be its complete actual pure theories, its countable adequate model codes, or the application/equality/valuation encodings covered by the finite-parameter argument in `max-degree.md` §8.3 and its analogues. For the positive auxiliary structures, the atomic-diagram codes of `positive-effective.md` §17 are also covered. For C, B or F with weak Infinity, bare original application/equality codes are covered as well, by the strengthened nonbottom-test argument in that note's §22.2; Actuality is unnecessary for this ordinary PA bound. Then

    [for every Q∈Sol, B≤_T Q] iff B≤_T A.                    (16)

Every Q computes A by the corresponding oracle-predicate or DNR argument, proving the reverse implication. For the other direction, use the following standard cone-avoidance argument, written out to specify the exact basis input.

### 8.1 Elementary cone avoidance for an effectively closed class

Let P⊆2^ω be a nonempty Π^0_1(A) class and let B not be computable in A. For a fixed functional Φ_e, there is a nonempty Π^0_1(A) subclass P′⊆P on which Φ_e^(A⊕X) fails to compute B.

If some X∈P has a finite convergent computation with output different from B(n), choose a finite prefix witnessing that computation and restrict P to its cylinder. Otherwise no convergent computation on any member has a wrong value. If some member's computation on some n diverges, intersect P with the Π^0_1(A) divergence condition for that n. Both restrictions have the required form and are nonempty.

If neither case occurs, Φ_e^(A⊕X) is total and equals B for every X∈P. That would make B computable in A. To see this explicitly, represent P as the paths through an A-computable binary tree. On input n, search using A for a level and a finite time bound such that every node at that level has a convergent Φ_e computation on n, using only the available finite oracle bits, and all outputs are the same bit b. Such a bound exists: the convergent computation cylinders cover the compact set P, and a finite subcover plus elimination of the finitely branching dead remainder gives a suitable level. The common bit must be B(n). This contradicts B not computable in A.

Thus one of the first two restrictions always exists. Repeating this construction for all e yields nested nonempty closed subclasses; compactness supplies a member X of their intersection. Then B is not computable in A⊕X. The choices of subclasses are existential and may depend on B; no algorithm producing X from B is claimed.

The same proof handles a countable list B_i, each not computable in A, by enumerating all pairs (i,e). Hence one member can simultaneously avoid all those cones. No effective listing of the B_i is required for this existence assertion.

### 8.2 Application to the model/completion packages

For each package above there is a fixed nonempty Π^0_1(A) class of complete Henkin witness theories whose codes compute the desired countable model/theory outputs. This is the witness class used in the corresponding PA-over-A upper bound. In the positive case, its auxiliary theory may be a fixed stronger Gallin package; its outputs still belong to Sol.

If B is not computable in A, apply §8.1 to that class. The chosen witness code D does not compute B, so neither does any corresponding output Q≤_T D. This proves (16). The same argument gives a solution Q simultaneously avoiding any specified countable list of reals not computable in A.

These packages therefore have no least solution Turing degree. If Q_0 had a least degree, Q_0 would be computable from every solution, hence from A by (16), contrary to the DNR-relative-to-A lower bound. Their model-computation oracle-capacity classes likewise have no least degree: a least capable oracle computes a solution, whose own capable degree would then be equal to that least degree, giving the forbidden least solution degree.

The result identifies the information common to all solutions; it does not say that every solution has degree A, that every PA-over-A degree is the exact degree of a fixed isomorphism type, or that different models can be uniformly converted while preserving their complete theories. It reinforces the distinction between the principal cone for effective axiomatization and the nonprincipal PA-over-A model-construction task.

## 9. An actual maximalist truth cannot be a pure Actuality witness

Let M satisfy old Max_C. No closed pure proposition q can simultaneously be actually true and entail every actual truth. In particular no actually true closed pure proposition can be a Boolean atom of M's propositional algebra.

Suppose such q existed. For every closed pure P, Actuality's defining property and the Boolean order give

    M satisfies P iff M satisfies (q and P)=q.

Max makes the right-hand closed pure identity true exactly when C proves it. Thus the complete actual pure theory of M is computably enumerable, with the finite syntax of q hardcoded. Running this enumeration on P and its negation decides that theory. More explicitly it is exactly the pure deductive closure of C+q: C proves (q and P)=q precisely when C proves q→P, by theorem necessitation and the C Boolean laws; then deduction applies. This is a consistent c.e. strengthening entailing every Max axiom, contrary to the exact axiomatization-cone theorem in `max-degree.md` §3.

For the atom statement, if q is actually true and an atom, then for each actually true p the meet q and p is actually true and therefore nonzero. Atomicity below q forces that meet to equal q. Hence q would be an Actuality witness, already excluded.

The full coalesced root does satisfy Actuality, witnessed by its singleton-root proposition. The corollary therefore shows that this witness cannot be denoted by a closed pure term. It also explains why Actuality permits application/equality to recover actual truth when its witness index is supplied, without letting the fixed pure-term equality diagram of degree 0′ recover every actual truth. The stronger presentation theorem under Actuality is proved in `positive-effective.md` §22; no claim that bare Max entails Actuality is made here.

### 9.1 The pure proposition algebra does have atoms

Let B_C be the Boolean algebra of closed pure proposition terms modulo C-provable identity. Equivalently it is the Lindenbaum Boolean algebra of closed pure formulas under C-provable material equivalence: genuine theorem necessitation identifies the two equivalence relations. In every Max model the denotations of closed pure propositions form a Boolean subalgebra canonically isomorphic to B_C.

For a closed pure q,

    [q] is an atom of B_C
       iff C+q is a consistent complete theory of closed pure sentences.   (9.1)

Indeed nonzeroness is consistency of C+q. Atomicity says that for every pure P, [q and P] is either zero or [q], exactly the assertion that C+q proves either neg P or P. Conversely those decisions force the atomicity condition. This concerns the pure-term subalgebra. A pure-term atom can acquire additional non-pure parts in the full propositional algebra of a model.

Thus the blanket claim that the pure proposition algebra is atomless would be false. For every fixed positive integer n, put A_n=Fregean Axiom and Exactly_n(e). The Fregean Axiom entails all-type Extensionality. At a point satisfying A_n, induction on types gives the unique full finite extensional hierarchy on n individuals: each input and output domain is finite, lambda abstraction with parameters realizes every finite function, and Extensionality excludes duplicate functions. Consequently every pure closed sentence has one fixed truth value at every A_n-point. Completeness of C makes C+A_n complete, and the ordinary finite extensional model supplies consistency. Therefore each [A_n] is an atom of B_C.

Moreover the already constructed and independently audited singleton profile Max root makes each A_n an atom even in its full propositional algebra; see `profile-root-construction-20261022.md` §§4,12–13 and `audit-profile-20261022.md` §4. Each A_n is actually false at every Max root, by the theorem above. Those examples refute the proposed strengthening to exclusion of all pure atoms, including actually false atoms. They involve current Boolean atomhood at the root; no claim of necessary atomhood is required.

In Stone-space language, the atoms of B_C are exactly the isolated complete pure C-theories. The actual ultrafilter of every Max model contains none of them. This is the precise topological content of the no-true-pure-atom result; it does not say that C has no isolated completions.

### 9.2 A canonical atomless interval containing all maximalist actual points

Let I=I_e be the pure arithmetic premise of `max-degree.md` §8. The interval

    B_C restricted to [I] = {[q] in B_C : [q]≤[I]}

is a nonzero countable atomless Boolean algebra, with relative unit [I] and relative complement [I and neg q]. Nonzeroness follows from the full infinite extensional model.

Suppose a nonzero [q]≤[I] were an atom of this interval. Since every part of [q] in B_C also lies below [I], it would be an atom of B_C itself. By (9.1), C+q would be a consistent complete c.e. pure theory. It proves I and hence interprets PA by Goodsell's arithmetic theorem. Its arithmetical consequences would be a complete consistent c.e. extension of PA, contradicting essential undecidability. Thus no such atom exists.

The Stone space of this interval, equivalently the complete pure C+I theories, is therefore a nonempty compact metrizable zero-dimensional space without isolated points, and hence is homeomorphic to Cantor space. Every Max actual ultrafilter contains [I], so all Max actual points lie in this canonical atomless clopen part of the Stone space of C. The ambient algebra B_C has both the finite Fregean atoms of §9.1 and this nonzero atomless interval. This is an abstract Boolean-algebra/topological assertion; it does not improve the effective degree of a typed presentation or assert that the unlabelled Boolean reduct alone computes 0′.

### 9.3 Isolated complete theories are finite at every actual type

The weak-Infinity argument yields a stronger boundary than merely refuting I_sigma. In fact:

**Theorem.** Let T be a consistent computably enumerable extension of C that is complete for closed pure sentences. For every admitted type sigma there is a positive integer k_sigma such that T proves that exactly k_sigma objects of type sigma exist. The function sigma↦k_sigma is recursive, with an enumeration index for T fixed. Thus every model of T has externally finite actual domains at every type.

Suppose some T-model M had an externally infinite sigma-domain. For each positive integer n, the pure sentence asserting at least n distinct sigma-objects is true in M. Since T is complete and M satisfies T, T proves every one of these sentences. Hence T extends the weak Infinity schema at sigma.

The finite register-trace proof in `positive-effective.md` §16 works at **any admitted sigma**, using only sigma-objects and the admitted predicate types sigma→t and sigma→sigma→t. It shows that every complete pure theory extending C and that weak schema computes binary DNR. But a c.e. complete theory is computable, by racing proofs of P and neg P. This contradiction excludes an infinite sigma-domain.

Choose any model of the consistent T. Its sigma-domain has some finite size k_sigma. The pure sentence Exactly_(k_sigma)(sigma) is true there, so completeness forces T to prove it. Consistency excludes any different exact size. On input a type code sigma, enumerate T-proofs until a sentence Exactly_k(sigma) appears. The preceding argument guarantees termination and produces k_sigma. This is one uniform ordinary recursive procedure with the fixed T-enumerator as a parameter.

Apply the theorem to T=C+q whenever [q] is an atom of B_C. Every pure isolator therefore fixes finite actual cardinalities at **all** types, with a recursive size function. It applies in particular to every pointed-complete cell from `profile-root-construction-20261022.md` §12. This strengthens the arithmetic boundary in that note's §18: the earlier argument gave only C+q proves neg I_sigma; the weak-Infinity trace proof now establishes external local finiteness.

Finiteness at sigma alone is not here identified with a bound at all accessible sigma-domains. Section 9.4 supplies the necessary bound, and its structural supplement derives it from finiteness at the numerical type (sigma t)t. Local finiteness does not by itself identify the structure as C5, full Gallin, or extensional. The pure-term denotations at type sigma number at most k_sigma, but this does not imply that every actual object is denoted by a closed pure term; the original language has no closed pure individual terms.

The positive-model lane independently checked the arbitrary-type trace application. The Gallin lane separately checked §§9–9.2, and the positive-model lane checked those sections together with the previously audited profile-root example. These are internal mathematical audits, not formal verification or human checking.

### 9.4 Possible weak Infinity already prevents a computable complete theory

Fix any admitted type sigma. Consider the weaker schema

    {Diamond AtLeast_n(sigma) : positive standard integers n}.      (9.2)

Every complete pure theory extending C and (9.2) computes binary DNR. To see this, use the pure finite-trace sentences H_e from `positive-effective.md` §16 and define d(e)=1 exactly when Diamond H_e is accepted. If the real computation phi_e(e) halts with output 0, its genuine finite trace uses only some finite number n of sigma-objects. The trace proof gives a C-theorem AtLeast_n(sigma)→H_e. Necessitating this **C-theorem** and using (9.2) gives Diamond H_e. If the computation halts with output 1, the finite-prefix contradiction is a C-proof of neg H_e. Genuine theorem necessitation gives neg Diamond H_e. Hence d is binary DNR.

It follows that every consistent c.e. pure-complete T extending C proves, for each sigma, a necessary finite bound

    Box AtMost_b_sigma(sigma)                                 (9.3)

for some standard integer b_sigma. Otherwise completeness would make T prove the negation of every such bound, equivalently every instance of (9.2), contrary to the DNR lower bound and T's decidability. Search T-proofs for (9.3) to obtain a recursive bound function sigma↦b_sigma. The output need not be the least possible bound.

This is a new proof of an accessible-world bound, stronger than §9.3's local assertion. Every world accessible from any T-model's evaluation point has at most b_sigma objects of type sigma. The exact **actual** size k_sigma from §9.3 remains separately computable; accessible worlds need not share that exact size. Neither the necessary bounds nor local finiteness alone are being identified with C5, Extensionality, or the Gallin package.

**Structural supplement.** There is also a direct C-theorem, independent of effectiveness. Put nu_sigma=(sigma t)t. For each positive standard n,

    C proves Diamond AtLeast_n(sigma) -> AtLeast_(n+1)(nu_sigma).   (9.4)

Given n distinct sigma-objects, finite unions of their haecceities give properties of each cardinality 0,...,n. The definitions of the finite Frege numerals then distinguish those n+1 numeral objects. This is a finite C-proof at each fixed n. Necessitate the resulting implication. Possible pairwise numeral inequalities pull back to actual inequalities by NI contraposition, yielding (9.4). Consequently if the actual nu_sigma-domain has k objects, then every accessible sigma-domain has at most k-1 objects. The actual nonempty sigma-domain already distinguishes numerals 0 and 1, so k is at least 2.

In particular the exact actual size function from §9.3 gives the explicit recursive necessary bound b_sigma=k_(nu_sigma)-1. Thus all-type actual local finiteness itself supplies necessary finite bounds, through the higher numerical sorts; no assumption of C5 or modal constancy of each actual size is involved. The possible-weak-Infinity DNR argument above remains useful independently of this structural observation.

The same trace sentences also give Sigma^0_1-complete theoremhood for every consistent c.e. extension of C+(9.2): take V0={e:T proves Diamond H_e} and V1={e:T proves neg Diamond H_e}, and apply the already proved disjoint-enumerable-set recursion lemma. Thus the possible schema has the same effective obstruction even without asserting an infinite actual domain.

The strengthened application/equality argument in `positive-effective.md` §22.2 also applies to (9.2). Its finite lambda-pattern compiler produces the exact proposition H_e, and H_e is nonbottom exactly when Diamond H_e. For a real output-1 computation, the genuine C-refutation makes H_e literally bottom; a real output-0 computation and (9.2) make it nonbottom. Testing nonbottom therefore yields binary DNR from a bare original application/equality presentation, using finitely many hardcoded indices and no Actuality witness. Consequently a computable bare C-presentation has finite actual domains at every type, and the structural supplement bounds all accessible domains. This statement alone does not supply a uniformly recursive size function or a complete term interpreter: those stronger effective conclusions above use a c.e. complete pure theory. Nor does the nonbottom argument relativize automatically to Max's oracle computations, since their negative oracle facts are optional Max consequences, not genuine C theorems available for necessitation.

### 9.5 Uniqueness of the finite actual structure

Let Gamma be a consistent complete pure C-theory, and suppose each actual type has a fixed finite cardinality in Gamma's models. Then Gamma determines a unique original **actual typed application/valuation structure**, up to type-preserving isomorphism. The uniqueness can include the full pure-term interpretation, not merely application.

To make that last claim precise, expand the description of an actual structure by one operation for each pure term pattern U(x_1,...,x_r), taking its actual parameter denotations to the denotation of U. This is a countable description in a recursively enumerated language. It includes closed pure terms as nullary operations. The graph of each such operation is expressible in the original language by U(xbar)=y. Application and the actual truth predicate on type t are expressible there as well.

Let M,N be two Gamma-models. Their corresponding sort domains have the same finite sizes. A finite collection of sorts and operation symbols has a finite complete table in M, including truth values if type t occurs. Enumerate each involved domain by finitely many variables, assert that these variables are pairwise distinct and exhaustive, and conjoin the relevant table equations and truth literals. Existentially closing this finite statement gives a closed pure sentence true in M, hence a member of Gamma, and therefore true in N. Its witnesses in N give bijections of those sorts preserving all the chosen tables.

Now take the product, over all types sigma, of the finite nonempty sets of bijections D_sigma(M)→D_sigma(N). Each required preservation condition is clopen in this compact product, depending on finitely many sorts and object entries. The previous paragraph proves the finite intersection property. Compactness gives a global family of sort bijections satisfying every condition. It preserves application, actual valuation, and every pure-term-pattern operation. This proves uniqueness in the stated category of actual structures.

If Gamma is decidable, the unique actual structure has a computable adequate BBK copy. In the witness construction, consistency of a finite list F(cbar) of formulas with fresh constants is decided by whether its existential closure exists xbar F(xbar) belongs to Gamma. This gives a computable complete witnessed extension with the usual fresh-witness schedule. Quotient closed terms by its decidable identities and evaluate truth and term operations from that extension. Section 9.3 supplies a recursive exact size for each type, so representatives can if desired be numbered by a finite initial segment uniformly in the type.

Combining with §9.3, every consistent c.e. pure-complete C-theory has this uniqueness and computable-copy property. This applies to pure isolators in particular. It does not identify arbitrary categorical, world-sorted, or action-model presentations: distinct such presentations can realize the same actual typed structure. It also does not assert that every actual object has a closed pure name in the original language; the computable construction uses fresh witness constants.

### 9.6 Pointed completeness is individual transitivity of the unique structure

Let q be a closed pure sentence such that C+q is consistent and complete. Let A_q be its unique actual typed structure from §9.5, including all pure-term interpretation operations. Then

    q is pointed-complete
      iff Aut(A_q) is transitive on its individual domain.       (9.5)

Here pointed-complete has exactly the meaning in `profile-root-construction-20261022.md` §12: for a fresh individual constant a, C(a)+q is complete in that expanded language. Equivalently, for every pure P(x) with x:e as its only possible free variable, C proves q→forall x P(x) or q→forall x neg P(x).

For the forward implication, fix individuals a,b of A_q. In the compact product of finite sort-bijection sets, impose every operation/valuation-preservation condition together with the condition that a maps to b. For any finite selection of these constraints, existentially enumerate the finitely many relevant sorts and record the finite tables as in §9.5, but leave one individual variable x free and require it to equal the position occupied by a in the source enumeration. This gives a pure formula P_F(x). It is true at a. Pointed completeness therefore makes it true at every individual, including b. Its witnesses give finite bijections preserving the selected tables and taking a to b. Compactness now gives a global automorphism with that action. Thus the individual action is transitive.

Conversely, transitivity makes the truth set of every pure P(x) either all individuals or none: automorphisms preserve the full term interpretation and actual valuation. Every q-model has the same actual structure up to isomorphism. Hence one of forall x P(x) and forall x neg P(x) is true in every q-model; completeness yields the required C+q proof. This is pointed completeness.

Combining (9.5) with the already audited profile-root criterion gives the structural reformulation

    Max_C + Atom(q) is consistent
      iff q isolates a complete consistent pure C-theory
          and its unique actual structure is individual-transitive.   (9.6)

The right-hand model is locally finite with recursive necessary finite bounds and a computable actual copy, by §§9.3–9.5. Equation (9.6) uses the existing profile-root theorem; it is not a new model construction.

Only transitivity on single individuals is required. The original singleton profile construction uses pure term profiles with one free individual marker; substituting the profiles of relational parameters leaves that same single marker. It does not require transitivity on all tuples or at every higher type. For example the finite Fregean n-individual structures with n>1 are individually transitive, while pairs split into equality and inequality orbits; they still supply the A_n atom examples.

## 10. Common information in bare maximalist application/equality codes

Although the exact oracle capacity for **bare** old-Max application/equality presentations remains unresolved here, their common-information class is already determined. Let BareMax be the countable sorted presentations supplying actual identity and total original application, with no actual valuation required. Then for every real B,

    [B is Turing reducible to every Q in BareMax]
       iff B is Turing reducible to 0′.                       (10.1)

The forward lower information bound is `max-degree.md` §4: hardcoding four denotations recovers 0′ from every such presentation. For the converse, if B is not reducible to 0′, apply §8's cone-avoidance construction to the fixed nonempty Pi^0_1(0′) class of complete Max witness theories. It yields an adequate countable Max code D with B not reducible to D. Forgetting valuation and the additional adequate-code fields yields Q in BareMax with Q reducible to D, so B is not reducible to Q either. The same proof simultaneously avoids any specified countable family of reals outside the cone below 0′, with the nonuniform-choice qualification of §8.

Equation (10.1) does not establish that a 0′-computable bare presentation exists. A least bare solution degree exists if and only if a 0′-computable bare application/equality model exists, and in that case the least degree is exactly 0′. Whether that degree is attained is not settled here. By contrast the adequate or valuation-supplying solution problems have PA-over-0′ capacity and no least degree, as already proved. The distinction is material.
