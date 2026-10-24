# The conditional omega-stage of possibility reflection

Research note by OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematics; no Lean work and no database edits. This concerns the new optional hierarchy in `iterated-possibility-degrees.md`, not a redefinition of old Max or Strong Possibility. **Every existence, exact-degree and completeness conclusion below assumes that all finite stages T_n are consistent.** That assumption is unproved; already T_2 is original Strong Possibility, whose consistency is open in the supplied source record.

## 1. Fixed setting and the target

Write O_0=□, O_(n+1)=hat O_n, and D_n=¬O_n¬. The fixed finitary theories are

    T_0=C,
    T_(n+1)=T_n+{D_nP : P closed pure and Cons(T_n+P)}.

Thus T_1 is pure Max and T_2 is pure Strong Possibility. Put

    T_ω=⋃_(n<ω) T_n,
    A_ω={pair(n,k):k∈0^(n)}, with 0^(0)=∅.

Fix an ordinary primitive recursive pairing bijection with its usual PA-provable properties. The particular computable pairing affects no degree statement. A_ω is the standard join 0^(ω) of the finite Turing jumps.

The finite-stage note proves exact reflection

    T_(n+1)⊢O_nP       if T_n⊢P,
    T_(n+1)⊢¬O_nP      if T_n⊬P,                         (1)

and, under consistency, Σ^0_(n+1)-complete theoremhood and PA-over-0^(n) complete-model capacity for n≥1. Here and below entailment uses the fixed C rules and ordinary deduction from additional actual axioms; it does not include necessitation of arbitrary added assumptions.

All proofs use the e-counting numerical type ν=(et)t, its impredicative number predicate N, zero and successor Suc, and the interpreted arithmetic supplied by C+I. Since T_1 entails I, every theory considered below contains this arithmetic. Numeralwise computation facts and induction with additional definable predicates are available as in `max-degree.md` §8. No external standardness of N is assumed.

The new work is to obtain **one fixed pure predicate** correct on all standard A_ω inputs. Merely having a different formula for each finite jump would not by itself supply the oracle-computation argument at the limit. Sections 2–4 construct that predicate without an internal truth predicate or a Choice principle.

## 2. Uniform proof enumerators and one self-consistent compiler

### 2.1 Uniform enumeration of the finite theories

There is a computable procedure producing, from n, an index for an oracle enumerator of T_n using oracle 0^(n). This is uniform syntax/proof bookkeeping, not an assumption of consistency.

For n=0 use the fixed c.e. enumeration of C. Given an enumerator for T_n with oracle Z=0^(n), the question whether T_n proves ¬P is a halting question for a Z-oracle proof search, and so is decidable in Z′=0^(n+1). Using that next oracle, enumerate the old T_n axioms and all D_nP for which the proof search does not halt. Lower jumps are uniformly computable from a higher jump: fix g with Z(k)=Z′(g(k)), and iterate g as needed. The term code of each fixed finite O_n is computable from n. This recursively gives the asserted uniform enumerators.

Consequently T_ω is c.e. in A_ω: interleave all the finite enumerators, answering an oracle query to 0^(n) by querying the nth column of A_ω.

### 2.2 The syntactic family with a placeholder program

Let h(k) be ordinary diagonal halting and put

    J_1(k)=□(I→h(k)).

The Max argument proves this is numeralwise correct for 0′. Let H_b(k,J), b=0,1, be the fixed interpreted arithmetic formula for oracle diagonal halting with output b. Its only additional predicate parameter is J:ν→t.

Given any ordinary program index a, construct finite pure terms J_n^a externally by the recursion

    J_1^a := J_1,
    J_(n+1)^a := λk^ν. O_n(∃m^ν[Nm ∧ Comp_a(numeral n,k,m)
                                               ∧ H_0(m,J_n^a)]).       (2)

Comp_a(n,k,m) is the usual arithmetic computation formula saying that the ordinary two-input program a on (n,k) halts with output m. Formula construction in (2) is an ordinary total computable operation on (a,n). It **does not execute program a**. It merely inserts the fixed code a and the relevant standard stage numeral into finite syntax. This distinction resolves the apparent circularity below.

For arbitrary a,n≥1 define the oracle-c.e. proof set, relative to 0^(n),

    V_0^(a,n)={e:T_n⊢H_0(numeral e,J_n^a)}.                (3)

Its oracle enumeration index is computable from a,n: first construct the finite term J_n^a, then combine it with the uniform proof enumerator from §2.1. No correctness property of J_n^a is needed merely to compile this enumerator.

The parameterized oracle recursion theorem supplies a total ordinary computable compiler F(a,n,k). It returns an oracle-program index p whose program ignores its input and dovetails:

1. If oracle machine k(k) halts, output 0.
2. If p is enumerated into V_0^(a,n), output 1.

The proof enumerator's base oracle is the same oracle used by this compiled program. The construction of the index p makes no oracle calls. Fix any deterministic tie convention. For n=0 define F arbitrarily, for example as a fixed nonhalting-program index, so F is total on every input.

Apply the ordinary recursion theorem once more, now to the total ordinary compiler F. Choose a fixed index a such that

    φ_a(n,k)=F(a,n,k) for all standard n,k.                 (4)

Such a program is total because F only compiles finite indices. Its index a is now fixed permanently. Write J_n for J_n^a and p(n,k)=φ_a(n,k).

This is not a recursive semantic definition of truth. The syntactic family is built for every hypothetical a first, the compiler is total for every a, and only then does the recursion theorem choose a matching program index. Global PA-provable totality of this chosen program is unnecessary; each actual standard computation p(n,k) has a finite PA-verifiable trace.

### 2.3 Inductive correctness of the chosen family

Assume T_n consistent and that J_n is numeralwise correct for 0^(n) in T_n. Actual finite oracle computations then show that the two proof sets

    V_b^(n)={e:T_n⊢H_b(numeral e,J_n)}, b=0,1,

contain K_b^(0^(n)). They are disjoint by consistency and interpreted deterministic arithmetic. The two-case recursion argument already proved in `max-degree.md` §10.4 gives

    k∈0^(n+1) iff T_n⊢H_0(numeral p(n,k),J_n).            (5)

For each standard n,k, PA verifies the actual computation φ_a(n,k)=p(n,k). PA also proves uniqueness of the output of this deterministic computation formula. Hence T_n proves

    ∃m[Nm∧Comp_a(numeral n,numeral k,m)∧H_0(m,J_n)]
       ↔ H_0(numeral p(n,k),J_n).                         (6)

No soundness about nonstandard computations is needed: the actual finite trace supplies one output, and internal determinism excludes a different output. Applying exact reflection (1) to the closed left side of (6) proves that J_(n+1)(numeral k) has exactly the 0^(n+1) sign in T_(n+1).

The base n=1 is the Max halting predicate, so external induction proves correctness for every finite n. The only semantic consistency assumptions used are the stipulated Con(T_n). This also gives a uniform computable procedure producing the finite term J_n from n.

## 3. A single pure least-closure relation of states

A state consists of three separately typed objects:

    n:ν,       O:tt,       J:νt.

No product type or individual-output function is postulated. Define the pure operation

    F_a(n,O,J) := λk^ν. O(∃m^ν[Nm∧Comp_a(n,k,m)∧H_0(m,J)]).           (7)

This operation has an admitted relational output type. It is a lambda term for every input, even if a hypothetical internal Comp_a computation has no output. Thus its existence does not require a totality theorem about program a or any functional-choice principle.

For a predicate X on the three state sorts, say Closed(X) iff

    X(1,O_1,J_1) and
    ∀n,O,J [Nn∧X(n,O,J) → X(Suc n,hat O,F_a(n,O,J))].                 (8)

The first displayed 1 is the first Frege numeral. Define the pure relation

    R(n,O,J) := Nn ∧ ∀X [Closed(X)→X(n,O,J)].                         (9)

All quantification is over admitted types; R has argument types ν,tt,νt and output t. This is ordinary finite impredicative syntax. It is the intersection of available closed predicates, not an externally assumed powerset intersection.

C+I proves that R contains the initial state and is closed under (7)–(8). For the latter, every Closed(X) containing a given R-state also contains its displayed successor state; N is closed under Suc. Consequently, for each standard r≥1, finitely many closure steps prove

    R(numeral r,O_r,J_r).                                         (10)

The identity F_a(numeral r,O_r,J_r)=J_(r+1) is the direct beta/substitution identity of their definitions (2) and (7). No truth/evaluation predicate for a formula code appears here.

### 3.1 Finite cuts exclude wrong states at standard levels

For each fixed standard m≥1 form the available lambda predicate

    Cut_m(n,O,J) := Nn ∧ n≠0 ∧
        ∧_(1≤r≤m)[n=numeral r → (O=O_r ∧ J=J_r)].                  (11)

The finite conjunction length m is external. The guard n≠0 is essential with the chosen initial level 1: a purported arbitrary level-zero state must not force an incorrect level-one state through closure.

C+I proves Closed(Cut_m). The initial state satisfies it. For closure, arithmetic gives N(Suc n) and Suc n≠0. If Suc n equals a listed numeral r≤m, r=1 would force n=0, contradicting the guard. For r≥2, injectivity and the finite numeral identities force n=r−1. The input cut then identifies O,J with O_(r−1),J_(r−1), so the displayed update identifies the output with O_r,J_r. If the successor is outside the listed finite levels, there is no state restriction to check.

Because Cut_m is one of the predicates quantified over in (9), R implies Cut_m. Combining this with (10) gives, for every fixed standard r≥1, the C+I theorem

    R(numeral r,O,J) ↔ (O=O_r ∧ J=J_r).                         (12)

The right-to-left direction uses (10) and identity substitution. The proof concerns the finitely many standard levels in question; it does not assert that every internal number is standard or that R has only externally finite states.

This finite-cut proof is why no global state recursion, operation realization, Choice, or standard arithmetic model is required. All updates are already explicit lambda operations, and all relevant standard-level exclusions have finite proofs.

## 4. The pure omega-jump predicate

Define one fixed pure binary predicate

    Jω(n,k) := Nn ∧ Nk ∧ n≠0 ∧ ∃O^tt∃J^νt[R(n,O,J)∧Jk].         (13)

For every standard n≥1, (12) gives

    T_1⊢Jω(numeral n,k)↔(Nk∧J_n(k)),                         (14)

where the implication is a separate finite theorem for each standard n. At n=0 formula (13) is false by definition. Use the fixed arithmetic pairing to obtain the unary pure predicate

    Kω(z) := Nz ∧ ∃n,k[Nn∧Nk∧Pair(n,k,z)∧Jω(n,k)].             (15)

PA's unique pairing and (14), together with the finite-stage correctness from §2.3, prove that for every standard integer z,

    T_ω⊢Kω(numeral z)       if z∈A_ω,
    T_ω⊢¬Kω(numeral z)      if z∉A_ω.                        (16)

Each particular theorem uses only a finite T_n and finitely many closure/cut calculations. Nothing in the argument takes an infinitary inference from all finite-stage facts. Formula (15) is a single finite pure formula; its correctness on standard arguments is an external theorem scheme.

## 5. Consistency and exact axiomatization cone

Under the standing assumption that all finite T_n are consistent, T_ω is consistent: a finite contradiction proof would use axioms from some single finite T_N. The countable BBK completeness/Henkin construction therefore applies. This is a consequence of the assumption, not a new proof of any finite stage's consistency.

For every oracle X, the following are equivalent:

1. Some consistent X-c.e. theory has every T_ω consequence.
2. A_ω≤_T X.

For the forward implication, enumerate that theory's proofs of Kω(numeral z) and its negation in parallel. By (16) exactly the correct sign is eventually found, so X computes A_ω. Equivalently one may uniformly race the finite-stage J_n signs. For the converse, §2.1 gives an A_ω-c.e. enumeration of T_ω itself, and it is consistent by the standing assumption.

Thus the exact axiomatization cone is the cone above 0^(ω). This statement does not require a first-order axiom or formula asserting that the number domain is standard.

## 6. Exact complete-model oracle capacity

Given a complete consistent pure T_ω theory Y, define

    d_Y(e)=1 iff H_0(numeral e,Kω)∈Y.                      (17)

Every genuine finite A_ω-oracle computation uses finitely many standard queries, whose correct Kω literals are T_ω theorems by (16). The interpreted arithmetic has induction for Kω and proves determinism. Consequently an actual output 0 forces d_Y(e)=1, and an actual output 1 forces d_Y(e)=0. Thus d_Y is binary DNR relative to A_ω. In particular Y is not computable in A_ω.

Conversely binary DNR relative to A_ω chooses consistent decisions in an A_ω-c.e. Henkin witness theory for T_ω. At each stage compile an A_ω-oracle program searching for a proof of φ or ¬φ, returning 0 or 1 respectively; choose φ exactly when the DNR bit is 1. The signed proof search and consistency argument are exactly those of `max-degree.md` §9, with A_ω replacing 0′. The chosen witnessed completion gives a countable adequate BBK term model.

Therefore, conditionally on all finite consistencies, an oracle X computes some complete pure T_ω theory, or some countable adequate T_ω model, **iff X has PA degree relative to A_ω=0^(ω)**. The solution problems with adequate codes are uniformly Medvedev-equivalent to binary DNR relative to A_ω. No exact degree spectrum for a fixed isomorphism type is asserted.

Relative Low Basis yields presentations of degrees d with

    A_ω<_T d<_T A_ω′,       d′=_T A_ω′.                    (18)

These degrees are hyperarithmetical. The strengthened standard-arithmetic obstruction in `positive-effective.md` §18 assumes only actual I_sigma and external standardness of N_sigma. Max, and hence T_ω, supplies I_sigma at each counting type. Therefore these hyperarithmetical adequate presentations have nonstandard Frege arithmetic at every such type, even if its actual object domain is finite. No actual individual-Infinity assumption or standardness claim was used in constructing them.

A smaller application/equality/actual-valuation presentation also has the same oracle-capacity lower bound, nonuniformly: hardcode the indices of zero, Suc and λe.H_0(e,Kω), compute each displayed numeral by application, and read the resulting proposition's truth. A uniform general term interpreter is unnecessary for this degree argument. The finite indices must be supplied if uniform extraction from unnamed presentations is desired. Bare action/category or equality-only codes without actual valuation are not covered.

## 7. Exact theoremhood degree at the limit

Let U be any consistent A_ω-c.e. theory entailing T_ω. Define

    V_b={e:U⊢H_b(numeral e,Kω)}, b=0,1.

They are disjoint A_ω-c.e. supersets of K_b^(A_ω), by (16) and deterministic arithmetic. The parameterized recursion theorem gives an ordinary computable p(k) whose A_ω-oracle program ignores its input and dovetails: return 0 if oracle machine k(k) halts; return 1 if p(k) is enumerated into V_0.

If k∉A_ω′ and p(k)∈V_0, the second branch returns 1, placing p(k) in V_1, a contradiction. If k∈A_ω′ but p(k)∉V_0, the first branch returns 0, placing p(k) in V_0, also a contradiction. Hence

    k∈A_ω′ iff U⊢H_0(numeral p(k),Kω).                    (19)

The map k to the last pure sentence is ordinary computable. Since theoremhood of U is c.e. in A_ω, it is Σ^0_1(A_ω)-complete under ordinary computable many-one reductions, and has degree exactly A_ω′=0^(ω+1).

In particular this holds for T_ω itself. Its finite pure extension consistency problem is Π^0_1(A_ω)-complete. These are transfinite-jump degree statements; they must not be labeled Σ^0_m-completeness for any finite m.

## 8. Absolute completion-space rank: separate self-certification corollary

This uses the fixed computable coding of complete pure theories as reals Y. A complete C-theory here is consistent and closed under finitary C-consequence/deduction; arbitrary accepted optional sentences are not necessitated.

Extract a total bitmap from every Y by

    A_Y(z)=Y(Kω(numeral z)),       A_(Y,n)(k)=A_Y(pair(n,k)).

The requirements

    A_(Y,0)=∅,
    ∀n,e [A_(Y,n+1)(e)=1 ↔ ∃s Halt_s^(A_(Y,n))(e,e)]       (20)

form one effective Π^0_2 condition on Y. Each bounded oracle computation queries only finitely many effectively located bits of Y; the forward directions are ∀n,e∃s of computable clopen conditions, while the reverse directions are Π^0_1. External induction on n shows that (20) is exactly the condition A_Y=A_ω.

Require additionally that Y is a complete consistent C-theory accepting every axiom in the A_Y-oracle enumeration of T_ω from §2.1. This is a Π^0_1 condition on Y: every failed coherence check or omitted axiom has a finite witness in the relevant bounded enumeration. With (20), the enumerator's oracle is certified to be the genuine A_ω. Conversely every T_ω completion has A_Y=A_ω by (16). The conjunction therefore defines exactly S(T_ω).

Accordingly S(T_ω) is absolute effective Π^0_2. Under the standing consistency assumption it contains no nonempty effective Σ^0_2 subclass, because it is a subclass of S(Max), whose exclusion was proved in `effective-refinements.md` §2. Thus its absolute effective-Borel level is again Π^0_2 but not Σ^0_2, despite the transfinite-jump theoremhood degree.

This is a statement about lightface effective descriptions in the fixed sentence-bit coding. Topologically S(T_ω) is closed, as every theory's completion space is. The coding does not establish Π^0_2-completeness under arbitrary continuous reductions.

The self-certification step is the uniform countable-column analogue of the independently audited finite-jump construction in `strong-possibility-degree.md` §8.3. It is stated separately because neither Low Basis nor a mere external enumeration oracle would by itself give this absolute rank reduction.

## 9. Remaining boundaries

The argument does not establish Con(T_2), Con(T_n) for any new n, or Con(T_ω) without the stipulated finite consistencies. It does not identify T_ω with old Strong Possibility or alter any original reference side condition. It proves no full external-powerset semantics, no standard-number-domain model, and no uniform conversion to an arbitrary action/category representation.

Every T_ω model still has the fixed Max pure identity diagram E_C, of degree 0′. The higher complexity concerns actual truth and the successive reflected diagrams. The standard finite hats are all strictly different under the standing hypothesis by the finite-stage note; this does not automatically prove the stronger internal No Collapse sentence asserting an appropriate internally indexed family. That would need a further argument covering nonstandard indices, not merely every external finite stage.

The principal new technical items requiring independent audit are the ordinary fixed-index compiler in §2 and the finite-cut uniqueness proof in §3. The subsequent degree reductions are the already-audited DNR/completion and disjoint-proof-set recursion arguments with the newly obtained pure oracle predicate Kω.

The coordinating agent independently read and checked §§2–8 after the first two audits. In particular, the compiler builds the syntax of J_n^a without executing a; its fixed point is a total index-producing program. Exact reflection is applied only to a closed pure sentence whose T_n-theoremhood was established by a finite deterministic computation. The finite-cut proof excludes level zero and needs no global standardness or Choice. The corrected numerical guard in (14) leaves all standard-input reductions intact. No additional proof defect was found in this reading.

Independent audit status: the Gallin-comparison lane passed §§2–4, with the numerical-domain guard in (14) made explicit; the positive-model lane passed §§5–8 conditional on that pure-oracle construction. The checks include the absolute Π^0_2 self-certification formula, not only the degree bookkeeping. This is agent audit, not human checking or formal verification.
