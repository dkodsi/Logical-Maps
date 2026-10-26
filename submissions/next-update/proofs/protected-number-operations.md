# Arithmetic operations from protected numerical cardinalities

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Definitions and the small C toolkit

Fix a counting type σ and abbreviate `ν=(σt)t`, `N=Nσ`, `S=Sσ`, and
`0=0σ`. Write `bσ:=⊥ν` for the bottom cardinality. Bottom and zero are
different: zero counts empty properties, while bottom counts none.

    PNσ   := ∀n∈Nσ, □(n≠bσ).
    NNDσ  := ∀m,n∈Nσ, m≠n → □(m≠n).
    Predσ := ∃P^(νν), ∀n∈Nσ, P(Sn)=n.

PN says that **current numerical cardinalities are protected from
bottom**. It says neither that every future number is current nor that
noncollapse holds necessarily. The existing compact condition is

    Iσ := ◇I*σ  ↔  ¬Nσ(bσ).

The following C facts are the only arithmetic input needed:

1. Numerical induction, numberhood persistence, and zero/successor
   decomposition. Zero is never a successor; `S(bσ)=bσ`.
2. **Boxed Exclusivity:** distinct current natural cardinalities are
   necessarily disjoint. Equivalently, for current numbers m≠n,
   `m∧n=bσ` as an identity of relational intensions.
3. **Collision only at bottom:** for numerical m,n,
   `Sm=Sn ∧ Sm≠bσ → m=n`.

These are recorded or proved in
[`frege-infinity-20261022-1726.md`, §§18 and 26](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md).
The identity formulation of (2) follows from boxed Exclusivity by
Intensionality. Item (3) is Lemma 26.1. We use Necessity of Identity
(NI), not necessitation of optional assumptions.

The canonical graph Jσρ is the least relation containing the zero pair
and closed under synchronized successor. In C it is persistent, contained
in `Nσ×Nρ`, total on the source numerical field, and satisfies

    J(x,y) ↔ [(x=0σ ∧ y=0ρ) ∨
      ∃u v(J(u,v) ∧ x=Sσu ∧ y=Sρv)].

See [positive-transport.md, §§1–2](numerical-transport.md). Totality uses
only number induction; it does not require Iσ.

## 2. The exact single-type protection principle

**Theorem 2.1 (C).**

    Predσ  ↔  PNσ  ↔  (Iσ ∧ NNDσ).

**Predσ→PNσ, directly.** Fix a predecessor P and induct on n with
`□(n≠bσ)` as the induction property. The zero case is a necessitated C
theorem. For the step, the current identities

    P(Sn)=n,                  P(S²n)=Sn

are necessary. If Sn became bottom, S²n would also be bottom, so their
P-values would coincide. Thus n would equal Sn and bottom, contradicting
the induction hypothesis. Hence Sn remains different from bottom.
This replaces the earlier detour through numerical ND and no-fixed-point
induction.

**PNσ→Predσ, directly.** Use the fixed pure operation

    Dσ(y)(X) := (y=0σ ∧ 0σ(X)) ∨
                ∃m(Nσm ∧ Sσm=y ∧ m(X)).

For a current n∈Nσ, its numberhood persists and it remains a predecessor
of Sn. PN at the current number Sn makes `□(Sn≠bσ)`. At any future
point, collision only at bottom makes n the unique numerical predecessor
of Sn. Zero is never a successor, so the first disjunct contributes
nothing. Therefore Dσ(Sn) and n are necessarily universally coextensive;
Intensionality gives `Dσ(Sn)=n`. Also **`Dσ(0σ)=0σ` is a C theorem**.
Thus the existential predecessor witness can always be replaced by this
explicit pure operation, normalized at zero. No bounded collection is
needed for this implication.

**PNσ→Iσ∧NNDσ.** PN immediately excludes a numerical bottom, giving Iσ.
For distinct current numbers m,n, boxed Exclusivity gives the identity
`m∧n=bσ`; NI makes it necessary. If m and n became equal, Boolean
idempotence would make their common value bottom, contradicting PN.
This argument uses equality of whole intensions, not mere emptiness at
the prospective merging point.

**Iσ∧NNDσ→PNσ.** Current Peano induction under Iσ gives `n≠Sn` for
every current number. NND makes that necessary. If n became bottom,
the identity `S(bσ)=bσ` would make `n=Sn` there. Contradiction. ∎

The Iσ conjunct cannot be silently dropped: finite full one-world models
have numerical ND while containing bottom as a number, and hence cannot
have a predecessor operation.

## 3. Protected sources give transport; upward homomorphisms give protection

**Lemma 3.1 (C).** Jσρ has a unique output at every numerical source
which is not bottom:

    Nσn ∧ n≠bσ → ∃!m Jσρ(n,m).

Existence is unconditional source-number induction. For uniqueness,
induct on n with the conditional assertion `n≠bσ → uniqueness`.
At zero, the unfolding and zero-not-successor leave only target zero.
At Sn≠bσ, also n≠bσ because S fixes bottom. Any unfolded predecessor u
has `Su=Sn` and is numerical, so collision only at bottom gives u=n.
The induction hypothesis identifies the target predecessors and hence
their successors. This uses local nonbottomness, not global Iσ.

**Corollary 3.2 (C).** PNσ makes the fixed pure operation

    Fσρ(n)(X) := ∃m(Jσρ(n,m) ∧ m(X))

canonical on all current σ-numbers, for **every** target ρ, without Iρ.
For a current n, choose its J-mate m. J persists; n's numberhood and
nonbottomness are necessary. Necessitate Lemma 3.1 to obtain necessary
uniqueness at n. Thus Fσρ(n) and m are necessarily universally
coextensive, giving `Fσρ(n)=m`. J's zero pair, successor closure and
current uniqueness give the zero and successor identities for Fσρ.

Here is the short converse through an adjacent predicate type. Put
`κ:=σt`. Define **Upσ** by the explicit homomorphism equations

    ∃U^(νσ νκ), U(0σ)=0κ ∧
      ∀n∈Nσ, U(Sσn)=Sκ(U(n)).

Do not replace this unguarded definition by mere J-membership: without
Iσ, a selection from a multivalued J need not preserve successor.

**Lemma 3.3 (fresh-tag identity, C).** Suppose j:σ→τ is necessarily
injective and c:τ is necessarily outside its image. Put

    j_*X := λy. ∃x(Xx ∧ y=jx),
    A_X  := j_*X ∪ {c},
    T(k)(X) := k(A_X),           F_j(k)(X) := k(j_*X).

For every τ-number k,

    T(Sτk)=F_j(k).

The Frege fixed-deletion lemma says that when A(c),
`(Sτk)(A) ↔ k(A−c)`. Its forward direction exchanges the successor's
deleted witness with c by Swap; its reverse direction deletes c.
For A_X, membership of c is necessary, and `A_X−c=j_*X` is an identity
because c necessarily lies outside the image. Numberhood persists.
Necessitate the discharged fixed-deletion theorem, apply it at every
future X, and use Intensionality. This proves the identity without Iσ
or Iτ. The same injection gives the C-canonical downward operation F_j.

Take `j=H`, the haecceity injection `H(x)=λz(z=x)`, and `c=⊥κ`.
Given Upσ's homomorphism U, its numerical values are κ-numbers by
induction. The canonical endomorphism `F_H∘U` fixes zero and commutes
with successor, so numerical induction gives `F_H(U(n))=n` on Nσ.
Set `P:=T∘U`. Then

    P(Sσn)=T(Sκ(U(n)))=F_H(U(n))=n.

Thus Upσ→Predσ without an I premise. Corollary 3.2 gives PNσ→Upσ.
Together with Theorem 2.1:

    Upσ  ↔  Predσ  ↔  PNσ  ↔  (Iσ ∧ NNDσ).

The ordinary guarded instance AT_(σ,σt) is therefore exactly
`Iσ→PNσ`, equivalently `Iσ→NNDσ`. Here one uses the C implication
`Iσ→I_(σt)` to activate AT's target guard; after Iσ is present,
J-realization and the homomorphism equations have their established
equivalence. One adjacent upward instance hence supplies every outgoing
canonical transport from that noncollapsed source.

## 4. Collection at one protected bound is already a theorem of C

For completeness define the prefix relation without a global I premise:

    B(b,x) := ∀Z [(∀n(Nn→Z(n,n)) ∧
                   ∀n x(Z(n,x)→Z(Sn,x))) → Z(b,x)].

Leastness gives numerical diagonals, closure under successor in the
first coordinate, and `B(b,x)→Nb∧Nx`. Its exact unfolding is

    B(b,x) ↔ [(Nb ∧ x=b) ∨ ∃a(B(a,x) ∧ b=Sa)].

To prove the reverse inclusion, the displayed right side contains every
numerical diagonal and is successor-closed, since it is itself contained
in B. Thus it is one of the relations quantified in B's definition.
The other inclusion uses B's diagonal and closure clauses. Consequently

    B(0,x) ↔ x=0;
    Nb ∧ Sb≠bσ → [B(Sb,x) ↔ (x=Sb ∨ B(b,x))].

The second identity uses collision only at bottom. Also B is comparable
on N: `B(a,b)∨B(b,a)`. To check this without I, first obtain B(n,0) by
induction. Leastness against `Z(a,b):=B(Sa,Sb)` gives simultaneous
successor preservation. Induct on a, decompose b as zero or a successor,
and apply that preservation to the induction hypothesis.

**Theorem 4.1 (protected bounded collection, C).**

    Nb ∧ □(b≠bσ) →
      ([∀x(B(b,x)→□Xx)] → □∀x(B(b,x)→Xx)).

Induct on b with the entire conditional, universally over X, as the
induction property. At zero, use its singleton prefix. At Sb, the
assumption `□(Sb≠bσ)` implies `□(b≠bσ)` because S fixes bottom.
The prefix premise restricts to b, so the induction hypothesis covers
its prefix necessarily; it also supplies `□X(Sb)`. Numberhood of b
persists. Necessitate the discharged C prefix-step theorem and apply
the necessary properness of Sb to cover the whole future prefix.

This removes Predσ from the collection theorem's hypotheses. Only the
particular bound being used must be protected. Neither global □Iσ nor
standardness of b is required.

## 5. The reusable least-preimage argument

Suppose `f:νσ→τ`, with τ relational, and assume PNσ plus stability of
distinctions on f's current numerical image:

    ∀m,n∈Nσ, f(m)≠f(n) → □(f(m)≠f(n)).            (SI)

Define

    L(y,a) := Na ∧ f(a)=y ∧
               ∀z[(B(a,z) ∧ z≠a) → f(z)≠y].

PN gives current Iσ. A current nonempty fiber has a least member a:
induct below any supplied preimage bound, using B's zero and successor
decomposition. If the old prefix has a witness, retain its least member;
otherwise the new endpoint is least. Uniqueness of L needs no I premise:
two distinct numerical candidates are B-comparable, so one's leastness
excludes the other.

For current L(y,a), each current z in B(a,−) satisfies
`□(z≠a→f(z)≠y)`: use NI if z=a, otherwise use SI and NI of f(a)=y.
The bound a is protected by PN. Theorem 4.1 therefore boxes the entire
leastness clause. Numberhood and f(a)=y persist, giving □L(y,a).
The unconditional uniqueness theorem can be necessitated.

Thus the fixed operation

    μ_f(y)(X) := ∀a'(L(y,a')→a'(X))

is necessarily universally coextensive with a, hence equal to a by
Intensionality. It selects numerical preimages on the current image.
This is the only graph-realization step needed for sections.

**SI is also necessary, given PNσ.** If an admitted g selects numerical
preimages on f[Nσ], distinct current image points y,z have distinct
numerical g-values, since applying f recovers y,z. PNσ makes those
g-values necessarily distinct. Were y,z to coincide, application of g
would make the values coincide. Thus image distinctions must be stable.
Consequently, under source protection, **a preimage selector with
numerical values exists exactly when the image's distinctions are
necessary**. The output stability requirement is therefore exact.

For a numerical map `f:νσ→νρ`, PNρ gives SI by Theorem 2.1. Therefore
**PNσ+PNρ gives numerical sections for every numerical surjection**,
and inverses for every numerical bijection. The proof needs only the
chosen preimage bound's protection and the distinctions that exclude
earlier preimages; the stated global PN/SI hypotheses package these
local requirements uniformly.

## 6. The simplified all-type package and its exact boundary

Over C, the following guarded schemata are equivalent:

    AT  ↔  CInv  ↔  NInv  ↔  NSections
        ↔  [Iσ→Predσ, for every σ]
        ↔  [Iσ→PNσ, for every σ]
        ↔  [Iσ→NNDσ, for every σ].

AT supplies the adjacent upward instances and hence protection by §3.
Protection at source and target supplies sections by §5. A section of
a numerical bijection is its inverse. Numerical inverses supply AT via
the canonical maps induced by necessary injections into a common
relational counting type; the exact short reduction is in
[`numerical-inverses.md`, §3](numerical-inverses.md). Canonical inverses
and AT are equivalent there already. The predecessor/protection/ND
formulations are equivalent type by type by §§2–3.

All guards remain present: the package makes no noncollapse claim at a
type where Iσ is false. Nor does it assert full ND, arbitrary relational
graph realization, or full choice. Necessary global noncollapse is
strictly stronger, by the reviewed
[Henkin countermodel](predecessor-henkin-countermodel.md).

Compared with the longer proof, the reusable changes are structural:
protection replaces the predecessor parameter in the collection argument;
successor-fiber pooling proves protection→predecessor directly; local
nonbottom functionality of J proves protection→transport directly; and
the fresh-tag identity isolates the single finite-cardinality step needed
for upward transport→predecessor. The old proofs remain available in
[`numerical-predecessor-sections.md`](numerical-sections.md).
