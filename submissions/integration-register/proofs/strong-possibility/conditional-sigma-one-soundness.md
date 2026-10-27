# A Σ₁-sound presentation of the full conditional theory

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

Fix either original language separately, pure L or exactly L({c:e→t})
without individual names. Put B=C_L+I_e and M=Max(C_L). Arithmetic is
the fixed Frege interpretation at e. H and D retain their original
distinctness-preserving definitions.

## 1. A different proof presentation of the same Max theory

Give M the following redundant presentation, denoted M♯:

* the axioms and certificate-based calculus of C_L;
* I_e as an explicit axiom;
* all the original Max disequalities, with their original C_L side conditions;
* every standard-true Π₁ arithmetic sentence, translated at e.

This has exactly M's consequences in the full original language. Max
already proves I_e and every true Π₁ arithmetic sentence; the original
Max axioms remain present. No new reference theory or signature is used.

Choose the proof predicate P♯ so that the final bullet is recognized by
a standard partial Π₁ truth predicate. Equivalently one can use the
negative-halting normal form NH(numeral k), with its Π₁ truth condition.
Proofs carry certificates for C_L axiom instances and syntactic rules.
Each Max axiom requires the usual Π₁ assertion that its corresponding
identity has no C_L proof. A finite proof therefore has a Π₁ correctness
condition, and

    P♯(s) := there is an M♯-proof with conclusion code s

is Σ₂. On standard sentence codes it expresses exactly original
M-theoremhood. Write P♯A for P♯(code A), including the Frege translation
when A is displayed arithmetically.

One equivalent proof description makes the coding explicit: a proof of A
supplies a true Π₁ sentence π, finitely many original Max disequalities
K, their Π₁ eligibility certificates, and a C_L-proof of
(I_e∧π^e∧K)→A. The empty K and π=top are allowed. Conjunction and
proof certificates can be coded into one numerical witness.

## 2. Derivability facts already hold in B

The explicit true-Π₁ axiom channel gives formalized Σ₂ completeness:

    B proves α -> P♯α              (α arithmetic Σ₂).       (1)

For α=∃u π(u), with π Π₁, a current witness u makes the numeral-substituted
Π₁ instance an eligible explicit truth axiom in the proof predicate.
The uniform arithmetic proof compiler then appends existential
introduction. PA verifies this transformation, including numeral
substitution and the partial-truth biconditionals. This is a formal
implication, not an assertion that B proves every true Σ₂ sentence.

There are also the following facts, for every fixed original sentence A
and every fixed pair A,A':

    if B proves A, then B proves P♯A;                      (2)
    B proves P♯(A→A') -> (P♯A -> P♯A');                   (3)
    B proves P♯A -> P♯(P♯A).                              (4)

For (2), a B-proof is a C_L-proof with I_e, now an unconditional explicit
axiom of the presentation. Its finite certificate needs no oracle axiom.
For (3), concatenate proof certificates and their finite Π₁ conditions.
For (4), apply (1) to the Σ₂ formula P♯A. These arguments do not suppose
that any optional C_L premise can be H-necessitated.

The standard provability input is Sergei N. Artemov and Lev D. Beklemishev,
*Provability Logic*, §8.3, Propositions 120–121, printed pp.82–83, on
truth-augmented proof predicates and formalized completeness.
[Checked primary source](https://sartemov.ws.gc.cuny.edu/files/2012/10/Artemov-Beklemishev.-Provability-logic.pdf).
That source states the result for its arithmetic base. The construction
above supplies the needed extension to this typed presentation: the added
Max proof checks remain Π₁, and (1) uses only the explicit arithmetic
truth axioms and the effective PA interpretation in B.

## 3. Max does not prove consistency in this presentation

Put

    c♯ := not P♯bottom,

a standard-true Π₂ sentence. It is true because M♯ and M have the same
consequences and M has its previously constructed standard-arithmetic
model.

The diagonal lemma gives a Π₂ arithmetic sentence G♯ with

    B proves G♯ <-> not P♯G♯.                              (5)

Facts (2)–(4) prove in B that P♯G♯→P♯bottom: use (4) to get
P♯(P♯G♯), and (2)–(3) applied to the forward implication in (5) to get
P♯(¬P♯G♯). Combining the two proof codes yields a contradiction proof.
Conversely P♯bottom→P♯G♯ by the ex-falso proof transformation. Thus

    B proves c♯ <-> G♯.                                  (6)

Max cannot prove G♯. If it did, P♯G♯ would be standard-true Σ₂. Max
proves all true Σ₂ arithmetic, so it would prove P♯G♯ as well as its
negation from (5), contradicting its established consistency. By (6),
Max cannot prove c♯ either. Hence

    M + not c♯ is consistent.                             (7)

The proof uses the displayed derivability facts, not an application of
the recursive-axiomatization version of Gödel II to nonrecursive Max.
The ordinary equivalence (6) is now proved in B, unlike the earlier
equivalence obtained using extra axioms of the raw conditional theory.

## 4. The whole conditional schema has a Max model

Define the computably axiomatized theory

    E♯ = B + {HA -> P♯A : A any closed original sentence}. (8)

Equivalently its conditional possibility schema is
¬P♯(¬P)→DP for every closed original P. There is no restriction on
types, quantifiers, arithmetic complexity, or occurrences of H in (8).

**Theorem.** M+E♯ is consistent and Σ₁-sound. In particular E♯ is
consistent and Σ₁-sound.

Every model of (7) satisfies P♯bottom. By the B-provable ex-falso
transformation it satisfies P♯A for every fixed original A, so it
satisfies every conditional axiom (8). Thus (7) has a model of M+E♯.

For soundness, if M+E♯ proved a standard-false Σ₁ sentence σ, M would
already prove its standard-true Π₁ negation. This contradicts the
consistency just proved. E♯ is a subtheory, so has the same Σ₁-soundness
conclusion. Equivalently, M+E♯ is conservative over M for closed Σ₁
arithmetic, since M already proves every true sentence of that class.

The witnessing model in this proof satisfies the standard-false Σ₂
sentence P♯bottom. That does not show that E♯ proves this false sentence.
It also does not provide a model of full SP: SP proves the true Π₂
sentence c♯. The established result is consistency and first-level
arithmetic soundness of the entire conditional schema.

## 5. The original full target is preserved exactly

Using P♯ instead of the earlier raw Σ₂ predicate changes no standard
eligibility decision. The same argument as in
[arithmetic-triangulation.md, §4](arithmetic-triangulation.md#4-an-exact-recursive-reformulation-of-unrestricted-sp)
therefore proves

    SP_M = E♯ + TrueΠ₂,
    Con(SP_M) iff E♯ is Σ₂-sound.                          (9)

For completeness, each original SP instance DP has a standard-true Π₂
antecedent ¬P♯(¬P), so follows on the right. Conversely SP contains I_e
and every true Π₂ sentence. For each fixed conditional instance, if M+P
is consistent, its consequent DP is an SP axiom. Otherwise P♯(¬P) is
true Σ₂ and already a Max theorem, so the conditional follows vacuously.
The usual finite-conjunction argument for true Π₂ axioms gives the
soundness equivalence in (9).

Thus the presentation change is legitimate for the exact research target.
The earlier raw conditional theory is not being identified with E♯ over
B alone, nor is its Σ₁-soundness inferred from the theorem above.

Moreover E♯ proves D¬c♯. Its G♯-instance gives ¬HG♯ by (5) and factivity.
The B-equivalence (6) can be transported under H conditional on I_e:
C_L proves I_e→(c♯↔G♯), and I_e→HI_e. Hence E♯ proves ¬Hc♯.
The specific next joint test is consequently

    M + E♯ + c♯.                                         (10)

Both M+E♯ and M+c♯ are separately consistent; their union (10) remains
unsettled. Full SP entails it and requires c♯∧D¬c♯. Proving (10)
consistent would still be short of the all-true-Π₂ requirement in (9).

## 6. A comparison hierarchy, with its changed references explicit

For each external k≥1, let M_k have the original Max axioms, I_e, and
all true Π_k arithmetic axioms, explicitly presented. Its proof predicate
P_k is Σ_(k+1). Let E_k=B+{HA→P_kA : A closed}. The preceding proof
generalizes: formalized Σ_(k+1) completeness supplies (4), and M_k
contains every true Σ_(k+1) sentence. Thus M_k cannot prove
c_k=¬P_kbottom, and M_k+¬c_k is a model of M_k+E_k.

Consequently E_k is Σ_k-sound for every k≥1. At k=1 this is exactly
the theorem about the same original Max reference. At k>1 the reference
has been strengthened to M+TrueΠ_k. Those higher cases do not prove
Σ₂-soundness of E♯ and are not substituted for either original target.

## 7. No new Π₂ arithmetic theorems

**Theorem.** M+¬c♯ is Π₂-conservative over M. Consequently M+E♯
is Π₂-conservative over M as well.

First, B proves

    P♯c♯ -> P♯bottom.                                    (11)

Indeed B proves c♯→G♯ by (6), so (2)–(3) give
P♯c♯→P♯G♯; the proof in §3 gives P♯G♯→P♯bottom.
This is a particular formalized Löb instance, proved here from the
displayed derivability facts.

Let π be a fixed arithmetic Π₂ sentence and suppose M+¬c♯ proves π.
Set σ=¬π, choosing a Σ₂ normal form provably equivalent in B.
The ordinary deduction theorem and classical contraposition give

    M proves σ -> c♯.                                    (12)

Every actual M-theorem A has M⊢P♯A: its provability assertion is
standard-true Σ₂, and M proves all true Σ₂ arithmetic. Apply this to
(12). Under the assumption σ, formalized completeness (1) gives
P♯σ, proof distribution (3) then gives P♯c♯, and (11) gives
P♯bottom. Thus

    M proves σ -> P♯bottom.

Together with (12), this proves M⊢¬σ, hence M⊢π. The reverse
inclusion of Π₂ consequences is immediate. The deduction theorem here
is the ordinary theorem for added premises; it does not necessitate
¬c♯ or any optional axiom.

Section 4 shows the consequence inclusions

    M ⊆ M+E♯ ⊆ M+¬c♯.

The second inclusion is a consequence inclusion, not an inclusion of
the displayed axiom lists. The sandwich proves the claim for M+E♯.
In particular E♯ has no false Π₂ arithmetic consequences either, since
M is arithmetically sound. A model of M+¬c♯ still has false Σ₂
arithmetic; there is no contradiction between these statements.

This sharpens the remaining boundary. In fact

    Con(SP_M) iff M+E♯ is Σ₂-conservative over M.           (13)

For the forward direction, SP_M contains M+E♯ and all true Π₂
sentences. Consistency therefore makes M+E♯ Σ₂-sound. Every Σ₂
consequence is then true and already provable in M. Conversely,
Σ₂-conservativity and arithmetic soundness of M make E♯ Σ₂-sound,
and (9) gives consistency of SP_M. This is a characterization, not
a proof of the missing Σ₂-conservativity. In particular (11)–(12)
do not settle M+E♯+c♯: inconsistency of that union would yield the
Σ₂ consequence ¬c♯, outside the proved Π₂ conservation class.

For the changed-reference hierarchy of §6, the identical argument gives
Π_(k+1)-conservativity of both M_k+¬c_k and M_k+E_k over M_k.
Use Σ_(k+1) completeness in place of (1). Only k=1 retains the original
Max reference and therefore bears directly on the two assigned targets.

## 8. The exact identity fragment and a common embedding target

Let EI be the class of closed formulas ∃x₁…x_n θ, where θ is a finite
Boolean combination of literal typed identities. The typed terms in θ
remain unrestricted, including arbitrary closed coefficients. The empty
existential prefix is permitted. Let UI be their negations, equivalently
universal finite-Boolean identity formulas.

**Proposition.** Over B, the full conditional theory E♯ is equivalently

    B + {F -> P♯F : F in EI}.                             (14)

For the forward implication use C_L⊢F↔HF for every F in EI. For the
reverse, for any closed original A use the existing identity form

    HA <-> J_A,
    J_A := ∃r:t (r≠bottom ∧ r=◇r ∧ r∧A=r).               (15)

Here r is fresh. If HA, its ordinary witness supplies a nonzero
◇-fixed proposition below A; conversely such an r is currently true
because r=◇r and r≠bottom, and is a witness to HA. This is the
previously established C identity characterization, using entity
identity throughout. Thus J_A is in EI. From (14), HA gives P♯J_A;
the B-theorem J_A→A and (2)–(3) then give P♯A. This recovers every
axiom (8). The normalization (14) does not restrict the terms occurring
in the identity matrices, so it retains the entire original schema.

**Theorem.** M+E♯ and M+¬c♯ have exactly the same UI consequences.
More generally they agree on every closed conclusion A for which
B proves ¬A→H¬A. In particular they agree on all conclusions DA.

Only one direction requires proof, because M+¬c♯ proves E♯. Suppose
M+¬c♯ proves ¬F, where B proves F→HF. Deduction gives M⊢F→c♯.
As in §7, M therefore proves P♯(F→c♯). Now in M+E♯, assuming F
gives HF and hence P♯F. Distribution yields P♯c♯ and then P♯bottom
by (11). But F also gives c♯. This contradiction proves ¬F in
M+E♯. Take F in EI for the UI assertion, or F=H¬A for the assertion
about DA. All uses of H-persistence here are B-theorems; none are
obtained by necessitating the added conditional schema.

There is a useful model-theoretic version. Every genuine model A of
M+E♯ has an embedding of its full typed algebra into the typed algebra
of some genuine model N of M+¬c♯. This retains the logical operations,
application, abstraction operations, quantifier operations and original
constants. It need not preserve the current truth predicate or be an
elementary embedding.

To prove this, adjoin names for the elements of A to the external
many-sorted Henkin presentation, and take the atomic and negated-atomic
diagram of its algebraic reduct. If a finite part of this diagram were
inconsistent with M+¬c♯, its existential closure F would be an EI
sentence true in A, while M+¬c♯ would prove ¬F. The theorem just
proved would make M+E♯ prove ¬F as well, a contradiction. Compactness
therefore gives the desired N; the inequalities in the diagram make
the homomorphism injective. The names are only diagram parameters,
not new constants in either original target signature.

This supplies a common kind of extension target once a model of E♯
is available. It does not construct a model of M+E♯+c♯, nor show that
an arbitrary M+c♯ algebra embeds into such a target. That source-model
existence question, and both unrestricted SP questions, remain open.

## 9. The arithmetic embedding can always be supplied

Write Ar(A) for the actual first-order Frege arithmetic of a genuine
M-model A, with its extensional arithmetic equality. This is a PA model.

**Theorem.** For every genuine M-model A there are a genuine model
N of M+¬c♯ and an arithmetic embedding

    j : Ar(A) -> Ar(N)

which preserves and reflects every Σ₁ and Π₁ arithmetic formula with
parameters from Ar(A). In particular N is a model of the full E♯.
No hypothesis that A itself satisfies E♯ is needed for this arithmetic
embedding theorem.

Proof. Use the conservative external many-sorted presentation with a
separate arithmetic sort isomorphic to the actual Frege number structure,
as in [arithmetic-lifting.md, §§2–3](arithmetic-lifting.md#2-a-recursive-presentation-of-max-relative-to-correct-proof-arithmetic).
Add a name for every element of Ar(A). For each Σ₁ formula with
these names, include the formula if it is true in Ar(A), and otherwise
include its Π₁ negation. This also includes every true Π₁ formula,
up to PA-provable normal form. It is the full Σ₁ elementary diagram
of Ar(A).

Suppose a finite part δ(a₁,…,a_m) of this diagram were inconsistent
with M+¬c♯. Its existential closure σ=∃x₁…x_m δ(x₁,…,x_m) is
equivalent over PA to a Σ₂ sentence: move the finitely many Σ₁
witnesses into the existential block, leaving a finite conjunction of
Π₁ matrices. Then M+¬c♯ would prove the Π₂ sentence ¬σ.
By §7, M would already prove ¬σ. But Ar(A) satisfies σ, since the
named tuple realizes δ, contradicting A⊨M.

Compactness supplies a model N of M+¬c♯ and the whole diagram.
The names define j. The atomic diagram preserves the arithmetic
operations and inequalities and makes j injective. Both signs of
every Σ₁ formula were included, so j is Σ₁-elementary and also
preserves and reflects Π₁ formulas. The model N satisfies E♯ by §4.
The auxiliary names and arithmetic sort do not change either original
signature or Max reference.

The statement also gives a precise location for the false proof in N
when A⊨c♯. Choose a Π₁ proof-correctness formula

    Q(u) := ∀v R(u,v),     P♯bottom <-> ∃u Q(u),

with R bounded (using the fixed effective proof coding). If b in Ar(N)
satisfies Q(b), then

    j(a) < b        for every a in Ar(A).                  (16)

Indeed A⊨c♯ gives, for every a,

    ∀u≤a ∃v ¬R(u,v).

PA's finite collection proves that this is equivalent to the Σ₁
formula ∃z ∀u≤a ∃v<z ¬R(u,v). Preservation under j therefore rules
out Q(u) for every u≤j(a) in N. Applying this to b proves (16).
Thus the image is bounded by every purported contradiction-proof
witness in the target. The embedding need not have an initial image;
no such claim is used in the proof.

For the changed-reference hierarchy of §6, the same argument gives a
Σ_k-elementary arithmetic embedding from any M_k-model into an
M_k+¬c_k model. A finite Σ_k elementary diagram has Σ_(k+1)
existential closure, and §7 gives Π_(k+1) conservation. The corresponding
Π_k proof witnesses again lie above the entire source image, by finite
collection and preservation of Σ_k formulas. Only k=1 concerns the
unchanged original references.

This theorem supplies the arithmetic part of an embedding even when the
source satisfies c♯ and the target satisfies ¬c♯. It does not extend j
through all the typed domains or construct a source model of E♯+c♯.
The full typed embedding theorem in §8 assumes that additional source
property; the two hypotheses must not be conflated.

## 10. Formal consistency strength and the first joint test

Let T=M♯+E♯ and S=M♯+¬c♯. Present both by adding their indicated
axioms to the same M♯ proof system. Write P_T and P_S for the resulting
Σ₂ proof predicates; recursive extra-axiom certificates do not increase
their complexity. As before P denotes P♯, and c denotes c♯ only in
the formulas in this section.

**Theorem.** B proves

    P_T bottom <-> P bottom,
    Con(T) <-> c.                                         (17)

Moreover, for each fixed arithmetic Π₂ sentence π, B proves

    P_T π <-> P π.                                        (18)

These are assertions about the specified internal proof predicates,
stronger than just the external conservation claim in §7.

For every original sentence A, B verifies the proof transformations

    PA -> P_T A -> P_S A <-> P(c∨A).                      (19)

The first implication includes an M♯ proof into T. For the second,
replace each conditional axiom HA→PA by its B-derivation from
¬c=Pbottom, using ex falso for P. This replacement is uniform in the
code of A. The last equivalence is the ordinary deduction theorem for
one extra axiom ¬c. It does not apply H-necessitation to that axiom.
On contradiction, (19) and Pc→Pbottom from (11) give the forward
direction of (17); the reverse is the first inclusion in (19).

For (18), let σ=¬π in Σ₂ normal form and put F=c∨π. The reasoning
of §7 is already a B-proof of

    (F ∧ PF) -> π.                                       (20)

Indeed, assuming σ, F gives c; Σ₂ completeness gives Pσ, and PF
then gives Pc and Pbottom. This contradicts c. Applying P to the
B-theorem (20), and using distribution and PF→P(PF), gives

    B proves PF -> Pπ.

Now use (19). The other direction of (18) is proof inclusion.
The transformations are effective for each fixed displayed arithmetic
formula; no reflection principle for optional premises is assumed.

Consequently, for every fixed arithmetic Σ₂ sentence α, B proves

    Con(T+α) <-> Con(M♯+α),                               (21)

with the proof presentations formed by adding α as a single axiom.
Apply (18) to the Π₂ sentence ¬α and use formal deduction. This
includes the false-consistency branch α=¬c; it does not include the
Π₂ sentence α=c that is needed for the first joint test.

In particular the open theory M+E♯+c♯ is exactly T+Con(T), up to
the B-provable equivalence (17). Equation (17) does not imply that this
theory is consistent. The established soundness is insufficient to rule
out T proving its own Σ₂ inconsistency assertion. No consistency verdict
for T+Con(T), or for full SP, is inferred here.

## 11. A branching requirement already realized by a fragment model

Let E₁ say that all individuals are identical. For either unchanged
reference M, the earlier constructions verify both

    Con(M+HE₁),                 Con(M+¬E₁).                (22)

Here is the additional check for the first assertion, not just an appeal
to consistency of M+E₁. At the singleton object S in
[triangulation-ladder.md, §6](triangulation-ladder.md#6-strong-actuality-and-atomlessness-can-be-strongly-possible-together),
the special proposition z is true at the identity coordinate and bottom
after every nonidentity arrow. Hence z=◇z as whole intensions. For any
currently true p, z∧p=z: at the identity coordinate this is truth, and
at every other coordinate z is bottom. Since z is currently true, it
witnesses Hp. Thus this S satisfies H-collapse, and in particular HE₁.
It is a genuine M-model by the existing component and closure checks.
The infinite-individual W in the same construction verifies the second
assertion of (22). Neither auxiliary generator is an original constant.

Full SP therefore entails

    DHE₁ ∧ DH¬E₁.                                        (23)

The first conjunct is licensed directly by (22). For the second, SP
gives D¬E₁, and C proves ¬E₁→H¬E₁ since ¬E₁ is an existential
identity sentence. Normality yields the asserted D-instance.

This yields an explicit failed instance of the local .2 principle:

    SP proves DHE₁ ∧ ¬HDE₁.                              (24)

Indeed C proves DE₁↔E₁, and hence HDE₁↔HE₁. The licensed D¬E₁
is ¬HE₁. Thus SP refutes ∀p(DHp→HDp), without necessitating that
optional principle or presupposing a world representation for H.
In ordinary S4 frame language, (23) requires two possibilities whose
opposed individual-cardinality claims remain true thereafter.

There is already a consistent joint witness to (23): use the R/W/S
model of the cited §6. Its root has DHE₁ by its return argument to S,
and D¬E₁ by its return argument to W, so the same C reasoning gives
DH¬E₁. This shows that the displayed branching requirement is compatible
with Max and the earlier constructor fragment. It is not an inconsistency
argument and does not give arithmetic disagreement between the branches.

There is also an arithmetic version relevant to the present lead. For
each true Π₂ sentence ρ unprovable in M, the standard-arithmetic profile
root in the same construction satisfies Hρ: the admitted new-object
indicator is possibility-fixed and below ρ. Therefore M+Hρ is
consistent, while M+¬ρ is consistent by unprovability. Since ¬ρ is
Σ₂ and hence H-stable in B, full SP entails

    DHρ ∧ DH¬ρ.

In particular this applies to c♯. Unlike (23), a genuine joint model of
these two arithmetic branches has not been constructed. The conditional
theory supplies the ¬c♯ possibility; a full SP model must also allow
the Hc♯ branch. Merely building a single progression toward ¬c♯ would
not meet that further requirement.
