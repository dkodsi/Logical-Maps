# First stage survival suffices for signature SP consistency

Original mathematical argument, direct source misc; unpaginated.

## 1. Framework and precise scope

Keep the original finitary relational C, exactly Σ={c:e→t}, and no individual
names in the original signature. Let a:e be the auxiliary root marker, and put

```math
M=\mathrm{Max}(C(\Sigma)),\qquad
T=\mathrm{Max}(C(\Sigma,a))+E_1,
\qquad E_1:=\forall x^e y^e\,(x=y)
```

Every SP side condition continues to use M. The marker does not enlarge the
target schema. Write HP=∃q(q∧□(◇q→P)) and DP=¬H¬P.

Use the fixed algebra B of closed Σ(a)-terms modulo C(Σ,a)-provable identity,
the compact space K=Stone(T), and

```math
W_F=\widehat{\neg\exists xF(x)}
          \cup\bigcup_{b\in B_\sigma}\widehat{F(b)},
\qquad K_1=\bigcap_F\overline{W_F}^{\,K}
\tag{1}
```

Here F:σ→t ranges over closed predicate terms; lambda abstraction includes
every formula with one displayed free variable and old term parameters.
The theory T is consistent by the standard singleton signature-profile model.
The common term diagram and the identification K=Stone(T) are established in
[REPORT.md](signature-sp-derivative.md), §§3 and 5.

The main new conclusions are

```math
K_1\ne\varnothing\quad\Longrightarrow\quad
\mathrm{Con}(\mathrm{SP}_\Sigma),
\tag{2}
```

and the exact first-stage criterion

```math
K_1\ne\varnothing\quad\Longleftrightarrow\quad
\bigl[\ T\vdash\exists x^\sigma F(x)
\ \Longrightarrow\
\exists b\in B_\sigma\ \mathrm{Con}(T+F(b))\ \bigr]
\quad\text{for every }\sigma,F
\tag{3}
```

No reverse implication from SP consistency to K₁ survival is proved.

## 2. Every licensed SP axiom is enforced at the first stage

The exact C-theorem from [universal-core analysis](../source/research/2026-10-22/notes/reflection-universal-core-20261022.md),
§2, is

```math
DP\ \leftrightarrow\
\forall r^t\bigl(r\ne\bot\ \to\ (P\land\Diamond r)\ne\bot\bigr)
\tag{4}
```

Fix a closed original-Σ sentence P with Con(M+P), and define

```math
F_P(r):=(r\ne\bot)\land\bigl((P\land\Diamond r)=\bot\bigr)
\tag{5}
```

Thus C proves ¬∃r F_P(r)↔DP. Choose an M+P model and interpret a by any
actual individual. Since C proves P→DP, that model refutes F_P(b) for every
closed marked term b:t.

Each F_P(b) is a finite Boolean combination of **ground typed identities**.
Their truth is fixed by the common marked term diagram in every M-model;
REPORT §3 proves this independently of the chosen model or individual.
Consequently

```math
T\vdash\neg F_P(b)\qquad\text{for every closed term }b:t
```

All the named-witness cylinders in W_{F_P} are therefore empty, leaving

```math
W_{F_P}=\widehat{DP}\quad\text{inside }K
\tag{6}
```

This set is clopen, so K₁⊆hat(DP). The argument works for every licensed P,
with the original signature-relative M in each side condition.

If U∈K₁, then U is a complete consistent T-theory containing every axiom
of SP_Σ. Ordinary many-sorted Henkin completeness produces a genuine model
of that theory; its reduct to the original signature is an SP_Σ model.
The completion may add unnamed entities. Such additions are harmless here,
because the full universal sentences DP already belong to U. They need not
leave its domains equal to B.

This last point distinguishes (2) from the older fixed-domain route:
survival of all later derivative stages is needed to make B itself a genuine
Henkin model, but is unnecessary for this first-stage consistency conclusion.

**Independent check from the original definition.** For a named q=Q(c,a),
if Q(c,x) is C-inconsistent then T proves ¬q. Otherwise signature unary
Possibility+ gives M⊢∀x◇Q(c,x). An M+P model then makes
P∧◇Q(c,x) true of an individual, establishing its C(Σ)-consistency.
A second application of unary Possibility+ gives
T⊢◇(P∧◇q). Thus T always proves
q→◇(P∧◇q), and refutes each named instance of
q∧□(◇q→¬P). Its existential closure is H¬P, so its witness open is again
hat(DP). This verifies the same conclusion without using (4).

## 3. The first stage is one application of a term omega rule

Define the following set of finitary sentences metatheoretically:

```math
\Omega(T)=\{\forall x^\sigma\varphi(x):
       T\vdash\varphi(b)\text{ for every closed marked }b:\sigma\}
\tag{7}
```

The premise tests refer only to the original T. This is one application of
the rule, followed by ordinary finitary consequence; it is not iteration of
the rule and does not enlarge the object language to infinitary formulas.

**Theorem.** K₁ is exactly Stone(T+Ω(T)), viewed as a closed subspace of K.

If ∀xφ belongs to Ω(T), take F=λx¬φ(x). Every named F-instance is refuted
by T, so W_F=hat(∀xφ) is clopen. Every K₁-point therefore satisfies the
universal sentence.

Conversely suppose U∈K fails membership in cl(W_F). A finite clopen
neighborhood hat(A) of U is disjoint from W_F. Completeness gives

```math
T\vdash A\to\exists xF(x),\qquad
T\vdash A\to\neg F(b)\quad\text{for every }b
```

Thus Ω(T) contains ∀x(A→¬F(x)). Together with A, which belongs to U,
this contradicts the displayed existential consequence. Such a U cannot
extend T+Ω(T), proving the reverse inclusion.

## 4. Total deletion compresses to one globally empty witness open

**Theorem.** K₁ is empty if and only if some single W_F is empty on all K.
Equivalently,

```math
K_1=\varnothing\quad\Longleftrightarrow\quad
\exists\sigma,F\
\bigl(T\vdash\exists x^\sigma F(x)
\ \land\ \forall b\in B_\sigma\ T\vdash\neg F(b)\bigr)
\tag{8}
```

The reverse direction is immediate from (1). For the forward direction,
the complement of K₁ covers compact K by interiors of failed witness sets.
Choose a finite clopen refinement hat(A_i), for i=1,…,n, with associated
predicates F_i:σ_i→t. Then

```math
T\vdash\bigvee_i A_i,\qquad
T\vdash A_i\to\exists x_iF_i(x_i),\qquad
T\vdash A_i\to\neg F_i(b)\quad\text{for every named }b:\sigma_i
```

Put Ψ(x₁,…,x_n)=∨_i(A_i∧F_i(x_i)). Nonempty type domains and the displayed
sentences give T⊢∃x₁…x_n Ψ, while T refutes every ground tuple instance
Ψ(b₁,…,b_n).

No individual-sort requirement has a bad region: T proves
∃x^e F(x)↔F(a). Hence the finite cover may use only relational σ_i.
Finite tuples at these types have an exact C-definable coding with term
projections. Write σ_i=α_i1…α_ik_i t, allowing k_i=0, and put

```math
\tau=(\sigma_1t)\cdots(\sigma_nt)t,\qquad
\kappa(\bar x)=\lambda f_1^{\sigma_1t}\cdots f_n^{\sigma_nt}.
                     \bigvee_i f_i(x_i)
```

Define π_i(z):σ_i by applying z to n arguments, taking argument j≠i to
be λu_j.⊥ and argument i to be λu_i.u_i[y₁,…,y_{k_i}], then abstracting
the y variables. Application to a displayed tuple is explicitly left-nested,
as in the topic convention. Beta reduction, Boolean identities, and the
C abstraction/eta laws give

```math
C\vdash\pi_i(\kappa(\bar x))=x_i
\tag{9}
```

All types used are relational; no function returning an individual, choice
operator, or optional extensionality axiom is introduced.

Now F(z):=Ψ(π₁(z),…,π_n(z)) has T-provable existential closure, using
κ to code a witness tuple. Each named z has named projections, so its
F-instance is refuted by T. This proves (8).

Since T is consistent, W_F is nonempty exactly when either T does not
prove ∃F, or some ground F-instance is T-consistent. This proves (3).
It also proves the useful special feature of this family:

```math
K_1\ne\varnothing\quad\Longleftrightarrow\quad
\forall F\ (W_F\ne\varnothing)
\tag{10}
```

This is not a general assertion about arbitrary countable open families.
It uses the definability, clopen conditioning, and tuple coding just proved.
Nonemptiness here does not assert that each W_F is dense in K.

## 5. Constructive fragments that do survive

Let R be the ordinary singleton signature-profile model from REPORT §§2–3,
and let U_R∈K be its closed marked truth theory.

**All numerical witness requirements hold at U_R.** For ν=(et)t and the
numerical predicate N, take F(n)=N(n)∧φ(n), where φ may contain arbitrary
higher-type quantifiers and marked term parameters. R has an externally
standard numerical domain. Any true existential ∃nF(n) in R therefore has
a numeral witness k̄. Consequently U_R∈W_F for all these requirements at
once. Individual requirements also hold there, as they do everywhere in K.
Numerical complexity alone cannot produce a certificate of (8); an omitted
witness must escape the standard-number and individual domains.

**Boolean proposition witnesses also admit simultaneous replacement,
including their actual truth.** Write B for B_t, so R's proposition
algebra is 2×B and named propositions embed as j(b)=(u(b),b). The
ultrafilter u contains no B-atom. This is the signature-relative version
of [minimal-Henkin analysis](../source/research/2026-10-22/notes/sp-henkin-minimal-20261022.md),
Lemma 6.1: a B-atom b with u(b)=1 would make the consistent recursively
enumerable theory C(Σ,a)+b entail every pure Max axiom, contradicting
the established undecidability argument. The extra finite signature does
not affect that proof-search contradiction.

The finite-cell proof of that note's Lemma 6.2 can preserve actual truth
as well as Boolean equations and disequations. Partition top by the
finitely many named coefficients. Exactly one coefficient cell c_* lies
in u. Inside every other cell retain the original B-coordinate partition
induced by the proposed witnesses (ε_i,b_i). Inside c_*, let m be the
number of variable-pattern cells required to be nonzero in 2×B. Since
u contains no atom, c_* admits a partition into m nonzero pieces. Exactly
one piece belongs to u. Assign that piece to the pattern (ε₁,…,ε_k),
which is necessarily one of the required nonzero patterns; assign the
other pieces to the remaining nonzero patterns. Set all other cells to
zero and reconstruct the b'_i from the pattern bits.

All Boolean polynomial zero/nonzero tests are preserved. Also
u(b'_i)=ε_i, so every actual-truth test on a Boolean polynomial is
preserved. Hence every quantifier-free formula in Boolean operations,
literal equality, and actual truth, with named coefficients, has named
witnesses in R whenever it has arbitrary witnesses there. Arbitrary
modal or quantified expressions are allowed as witness-free coefficients;
applying those operations to a witness is outside this fragment.

Thus U_R simultaneously meets all W_F from this Boolean fragment as well
as the numerical and individual requirements. This is a genuine partial
survival result, not a claim that U_R∈K₁.

## 6. Why finite Herbrand extraction does not settle the target

A tempting stronger property would say that each T-provable existential
has a finite list of closed terms whose instances have T-provable
disjunction. That property is false here, even for a C-theorem.

Let Atom(p) be Boolean atomhood, and define

```math
A:=\exists p^t\bigl(p\land\mathrm{Atom}(p)\bigr),\qquad
G(p):=A\to\bigl(p\land\mathrm{Atom}(p)\bigr)
\tag{11}
```

C proves ∃pG(p): if A holds, take its witness; otherwise any proposition,
such as bottom, works. This is classical case analysis, with no choice
schema.

In R, the proposition w=(1,0) is an actual true Boolean atom, so A is
true. Every named proposition has diagonal form (u(b),b). If it is true,
then b≠0 because u(0)=0, and w is a proper nonzero part of it. If it is
false it cannot satisfy p∧Atom(p). Thus R refutes G(b) for **every** named
proposition b simultaneously. In particular no finite disjunction of
named G-instances is T-provable, although C already proves ∃pG(p).

This does not refute (3): that property permits a named witness in some
other T-model, and does not require a finite disjunction covering all
T-models. It does rule out the proposed stronger proof-normalization
shortcut. The first-order presentation's quantifier-truth clauses have
genuine existential witness requirements; their Skolem functions are
not supplied by ordinary lambda abstraction.

The R-only calculation of G(b) above does not by itself establish
first-stage deletion: conditional refutation on a clopen neighborhood
would suffice, but simultaneous failure in just one model would not.
There is, however, a stronger uniform argument here. In any M-model,
if a named proposition j(b) were a true Boolean atom, b would be an
atom of B: any nonzero proper B-part would embed as a nonzero proper
part of j(b). The no-true-B-atom argument in §5 applies to the truth
ultrafilter of every such model, giving a contradiction. Therefore

```math
T\vdash\neg\bigl(b\land\mathrm{Atom}(b)\bigr)
\qquad\text{for every named }b:t
```

For F(p)=p∧Atom(p), it follows that W_F=hat(¬A), a clopen set. Thus
K₁⊆hat(¬A), and U_R, which contains A, is deleted at the first stage.
Equally, T proves G(b)↔¬A for every named b, so W_G=hat(¬A) as well.
This still does not establish total deletion: the argument does not
make A a T-theorem.

## 8. Sources and audit

The fixed framework and published SP formulation are Bacon–Dorr,
*Classicism*, draft of 16 May 2023, §1.3 and §2.6 p.42. The new first-stage
deductions are not attributed to that paper. Local inputs and exact source
boundaries are [REPORT.md](signature-sp-derivative.md), §§2–5 and 7;
[universal-core analysis](../source/research/2026-10-22/notes/reflection-universal-core-20261022.md),
§2; and [minimal-Henkin analysis](../source/research/2026-10-22/notes/sp-henkin-minimal-20261022.md),
§§6–7. The ordinal analysis in
[HYPERARITHMETIC-BOUNDARY.md](signature-sp-effective.md) is unchanged.
