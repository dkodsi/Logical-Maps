# Arithmetic reflection comparisons and an effective form of full SP

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

Work separately with the pure language L and with exactly L({c:e→t}),
with no original individual names. Write M_L=Max(C_L), H=hat(Box),
and D=dual(H). Arithmetic always uses the fixed Frege interpretation
at e. Original reference theories and SP eligibility tests are unchanged.

## 1. A common natural arithmetic separator

Let Z=Z_<ω be the recursively axiomatized union of the finite-order
extensional arithmetic theories Z_n, n≥2, used in
[the arithmetic study, §36.7](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md#367-identification-with-the-union-of-all-finite-order-extensional-arithmetic).
Each proof uses finitely many orders. This is an ordinary many-sorted
finitary theory, not an infinitary language or a single infinite type.

For a recursively axiomatized arithmetic extension S, let

    RFN₁(S) := forall p,s,
      [Prf_S(p,s) and Sent_Σ₁(s)] -> True_Σ₁(s).             (1)

Proofs carry enumeration certificates when needed, so Prf_S is effectively
checkable. True_Σ₁ is a fixed standard partial truth predicate. Formula
(1) has a Π⁰₂ normal form: a claimed Σ₁ proof must have a numerical witness
for its conclusion. For each standard Σ₁ sentence σ, PA proves the
usual biconditional True_Σ₁(code σ)↔σ.

Put R₀=RFN₁(Z). The common arithmetic theorem already established is

    Th_arith(M_L)=Th_arith(Z+TrueΠ₁).                       (2)

Here and below the right side denotes ordinary first-order arithmetic
consequences, even though Z itself has higher sorts.

**Reflection lemma.** If S is recursively axiomatized, extends PA, and
is standard-arithmetically sound, then S+TrueΠ₁ proves neither RFN₁(S)
nor its negation.

The negation is excluded by standard soundness. For the other direction,
suppose S+TrueΠ₁ proves RFN₁(S). Finitely many true Π₁ axioms suffice;
let their conjunction be π, and put U=S+π. It is a consistent recursive
extension of PA. A U-proof of contradiction effectively transforms into
an S-proof of ¬π. Replace ¬π, if necessary, by a PA-equivalent Σ₁ normal
form σ. PA verifies the proof transformation. RFN₁(S) then gives

    Pr_U(code bottom) -> σ.

But U proves ¬σ, since it contains π. Under the assumed U-proof of
RFN₁(S), U therefore proves Con(U), contrary to Gödel's second
incompleteness theorem. This proves the lemma. It uses the standard
incompleteness theorem; the application to the comparison is the deduction
here.

Apply the lemma to Z and (2). Both exact M_L theories leave R₀ independent.
The constructor fragment K proves R₀, because R₀ is a standard-true Π₂
sentence and K proves every such sentence. Thus R₀ is one common explicit
separator for the two languages. It supplements the earlier Γ_L tests;
none of those definitions or proofs is replaced.

The arithmetic-conservativity results also give consistency of

    B_L+R₀,                 B_L+not R₀,
    Q_L+C_m^H+R₀,           Q_L+C_m^H+not R₀                (3)

for every external m≥1. B_L is the combined structural SP fragment;
Q_L is Max plus StrongActuality, ordinary Barcan and current choice;
C_m^H specifies the finite H-cluster size. Use
[barcan-arithmetic-conservativity.md, §7](barcan-arithmetic-conservativity.md#7-the-combined-structural-sp-fragment-is-also-arithmetically-conservative)
and [finite-hat-clusters.md, §3](finite-hat-clusters.md#3-arbitrary-finite-h-clusters-add-no-arithmetic-consequences).
These are consistency claims for separate models, not embeddings between
the opposed arithmetic choices.

## 2. A strict reflection ladder inside the consistent lower bound

Define recursively

    Z⁽⁰⁾=Z,
    R_n=RFN₁(Z⁽ⁿ⁾),
    Z⁽ⁿ⁺¹⁾=Z⁽ⁿ⁾+R_n,
    B⁽ⁿ⁾_L=B_L+{R_i : i<n}.                               (4)

Every Z⁽ⁿ⁾ is recursive and standard-sound, and every R_n is true Π₂.
The reflection lemma and (2) imply

    Th_arith(B⁽ⁿ⁾_L)=Th_arith(Z⁽ⁿ⁾+TrueΠ₁),
    B⁽ⁿ⁾_L does not prove R_n or not R_n.                   (5)

For the arithmetic equality, the finitely many extra axioms R_i are
arithmetic. By the deduction theorem, adding them commutes with passing
to the arithmetic consequence theory. Thus the existing arithmetic
conservativity of B_L applies directly; no new structural interpretation
is being assumed.

Consequently

    B_L < B⁽¹⁾_L < B⁽²⁾_L < … < B⁽ω⁾_L < K+B_L,           (6)

where B⁽ω⁾_L=B_L+{R_n:n∈ω}. Every displayed theory is consistent: the
standard-arithmetic graft for K+B_L is a model of all of them.

The last inclusion is also strict. Let Z⁽ω⁾=Z+{R_n:n∈ω}; the sequence
of axiom codes is effectively enumerable. Put R_ω=RFN₁(Z⁽ω⁾). The same
lemma shows that Z⁽ω⁾+TrueΠ₁ does not prove R_ω. Every proof in B⁽ω⁾_L
uses only finitely many R_n, so its arithmetic theory is exactly that
of Z⁽ω⁾+TrueΠ₁. It therefore does not prove R_ω, whereas K proves this
true Π₂ sentence. No ordinal iteration beyond the displayed ω-stage
is needed for (6).

For each finite n, and also for n=ω with the preceding definitions,
there are two consistent, incomparable extensions of B⁽ⁿ⁾_L:

    P_n := B⁽ⁿ⁾_L+R_n,
    N_n := B⁽ⁿ⁾_L+D(not R_n).                              (7)

The first is consistent by the standard model. The second has a model
with ¬R_n, using (5) and reflexivity P→DP. That model refutes R_n.
Conversely the standard graft satisfies every R_n and H R_n: its
possibility-fixed new-object indicator is below R_n at every new object.
It therefore refutes D(not R_n). This establishes both strictness and
incomparability in (7).

Full SP entails both branches: it entails B_L and every true Π₂ sentence,
and ¬R_n is M_L-consistent since already B⁽ⁿ⁾_L does not prove R_n.
However the joint theory

    B⁽ⁿ⁾_L+R_n+D(not R_n)                                  (8)

has not been proved consistent or inconsistent here. This keeps the
missing comparison explicit. The two separate consistency proofs in
(7) do not prove the consistency of their union.

If (8) is further strengthened by R_n→H R_n, it is inconsistent. Each
branch separately remains consistent with that implication: the standard
graft witnesses the positive branch, and a ¬R_n model witnesses the
negative branch vacuously. Thus a single precisely stated persistence
assumption already crosses a known inconsistent bound. Full SP does not
include that persistence assumption.

The same independence calculation applies to Q_L+C_m^H after adding the
preceding R_i, for every fixed m. Finite H-cluster size therefore does
not select either side of any reflection stage in this ladder.

## 3. What a countertarget for R₀ must add

Let ρ(k)=RFN₁(Z_k), using one effective presentation of the finite-order
theories and taking k≥2. Equivalently use Z_max(2,k), so all natural k
are covered. PA verifies

    R₀ <-> forall k ρ(k),
    k≤l -> (ρ(l) -> ρ(k)).                                 (9)

Indeed a finite Z-proof has a computable maximum order and is a proof
in the corresponding Z_k; conversely each Z_k-proof is a Z-proof. These
are syntactic transformations of proof codes.

For each external standard k, some finite higher order proves ρ(k).
Here is the needed ordinary argument. In a sufficiently high but fixed
finite-rank set theory, form the finite hierarchy interpreting Z_k over
its own ω, and the set of finite assignments in that hierarchy. A
satisfaction relation for its first-order many-sorted syntax is obtained
by recursion on formula complexity; all relations involved are subsets
of fixed finite products of those sets. Finitely many further powersets
suffice. Separation verifies every internally coded comprehension instance,
and induction verifies soundness of coded proofs. Satisfaction of an
arithmetic Σ₁ sentence agrees with the partial arithmetic truth predicate
over that same ω. This proves uniform Σ₁ reflection for Z_k.

The number-preserving finite-order interpretation used in the earlier
arithmetic study transfers this proof to some Z_m with finite m depending
on k. No uniform finite m for all k is claimed. Its set/sequence coding
input is Colin McLarty, *Interpreting set theory in higher order arithmetic*,
v5, 15 February 2013, §1, Theorem 1.3 (p.1), §2.2 (p.2), and the
interpretation theorems in §§4–5 (pp.5–6). The finite-rank satisfaction
argument above is supplied here, not attributed to McLarty.
[Primary manuscript](https://arxiv.org/pdf/1207.6357).

Hence C_L proves I_e→ρ(k) at each standard numeral. The one-step rule
for K, applied to this fixed arithmetic predicate ρ, yields

    forall k (N_e(k)=top -> (I_e and ρ(k))=I_e).             (10)

This is stronger than simply citing the current truth of R₀: it gives
whole identities for each actual source number, including nonstandard
ones in a nonstandard K-model.

Suppose a full term-algebra embedding f takes a K-model A into an
M_L-model B with ¬R₀. It preserves numberhood and (10). Since I_e is
true in B, we obtain ρ(f(a)) for every source number a. By (9), any
number b of B at which ρ(b) fails must satisfy

    f(a) < b for every a∈N_e(A).                            (11)

Otherwise ρ(f(a)) and b≤f(a) would imply ρ(b). Thus the target's first
failing finite-order reflection level lies above the entire source number
image, not merely above every externally standard numeral. A target
with ¬R₀ has such a level by (9); leastness is available in PA but is
not needed for the inequality.

This is a constraint on the embedding required by the comparison. It
does not show that such an embedding is impossible: nonstandard arithmetic
admits proper images bounded above in larger models. No full-type lifting
theorem is inferred from an arithmetic embedding.

## 4. An exact recursive reformulation of unrestricted SP

There is also a full-scope reformulation, distinct from the lower-bound
results above. Fix a concrete effective proof presentation of C_L, using
certificates for Logical Equivalence. A finite Max proof has a Π₁
correctness condition: each of its finitely many additional Max axioms
asserts nonprovability of a specified original closed identity in C_L.
Thus there is a uniform Σ₂ arithmetic formula Pr_M_L(s) whose standard
extension is exactly M_L-theoremhood. For a closed original sentence P,
put

    Con_M_L(P) := not Pr_M_L(code(not P)).                   (12)

This is Π₂ and is standard-true exactly when M_L+P is consistent.
All displayed arithmetic formulas are translated at e in object-language
axioms. No truth predicate for the whole C language is introduced.

Let E_L be the computably axiomatized theory consisting of C_L+I_e and,
for every closed original-language sentence P, the conditional axiom

    Con_M_L(P)^e -> DP.                                    (13)

The schema is effective because it enumerates P and writes (13); it
does not decide the truth of the antecedent. The reference inside (12)
is the original M_L, not E_L, K, or SP.

**Theorem.** As theories in the fixed original language,

    SP_L = E_L + {π^e : π is standard-true Π₂}.              (14)

For right-to-left inclusion, every licensed SP axiom DP has a true Π₂
antecedent (12), so it follows from (13). For left-to-right inclusion,
SP entails I_e and all true Π₂ sentences by the existing constructor
theorem. For any fixed P, if M_L+P is consistent, SP already has DP,
and therefore (13). If it is inconsistent, Pr_M_L(code(not P)) is a
true Σ₂ sentence. M_L, and hence SP, proves every true Σ₂ arithmetic
sentence by (2). SP therefore proves the negation of the antecedent of
(13), and again proves (13). This case distinction is external proof of
the theory equality; it is not an effective test for eligibility.

In particular,

    Con(SP_L) iff E_L is Σ₂-sound.                          (15)

Here Σ₂-sound means that every ordinary Σ₂ arithmetic sentence whose
Frege translation E_L proves is standard-true. If E_L proves a false
Σ₂ sentence σ, (14) adds the true Π₂ sentence ¬σ and is inconsistent.
Conversely, if the right-hand theory of (14) is inconsistent, finitely
many true Π₂ assumptions suffice. Their conjunction π is Π₂, and the
deduction theorem gives E_L⊢¬π, a false Σ₂ sentence. Normal-form changes
are justified in PA under I_e. This proves (15).

This reduces each full target to the arithmetic soundness of an explicitly
enumerable theory. Merely proving E_L consistent would not establish
(15). No Σ₂-soundness proof or false Σ₂ consequence of E_L has been
found here. The two theories E_L retain their separate original languages
and Max proof predicates; equality of the arithmetic shadows of the two
Max theories does not identify their conditional SP theories.

## 5. Scope of the progress

The comparison now has explicit reflection steps rather than only a
language-specific diagonal sentence. The positive and counterpossibility
branches are separately consistent at every displayed stage, including
the ω-stage. Their required unions remain open. The nonstandard
reflection-level calculation specifies what any full-term embedding for
the first natural test must accomplish.

Independently, (14)–(15) give an exact proof-theoretic route to either full
resolution. A proof of Σ₂-soundness of E_L would prove that SP_L is
consistent; a demonstrated false Σ₂ theorem of E_L would refute it.
Neither conclusion has been established by the comparisons above.
