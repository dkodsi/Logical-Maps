# Predecessor operations supply numerical sections

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Exact framework and imported inputs

All types are fixed admitted closed types in the original finitary language
of C. Fix a counting type σ and abbreviate

    ν := (σt)t,    N := Nσ,    S := Sσ,    0 := 0σ,
    ⊥ν := λX^(σt).⊥.

The bottom cardinality ⊥ν differs from zero. `Iσ := ◇I*σ` is numerical
noncollapse, not the quantified Axiom of Infinity. C proves `Iσ ↔ I*σ`.
Define

    PredOpσ := ∃P^(νν) ∀n (Nn → P(Sn)=n).

There are no requirements on P(0) or P at nonnumerical arguments. The
schema compared with AT below is **guarded**: `Iσ → PredOpσ`.

AT, CInv, NInv and NSections have exactly their definitions in
[`numerical-inverses.md`, §1](numerical-inverses.md). All pairwise instances
are guarded by `Iσ ∧ Iρ`. In particular NSections concerns an admitted
operation already known to be a surjection between current numerical
fields; it does not represent every arbitrary relational graph.

The imported C theorems are:

* Numerical induction for arbitrary admitted predicates; numberhood
  persistence; zero is not a successor; and
  `Nn → (n=0 ∨ ∃m(Nm ∧ n=Sm))`.
* `S(⊥ν)=⊥ν`.
* **Successor collision only at bottom:** if `Nm`, `Nn`, `m≠n` and
  `Sm=Sn`, then `Sm=⊥ν`. This is Lemma 26.1 of
  [`frege-infinity-20261022-1726.md`](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md),
  proved by boxed Exclusivity and Frege Swap.
* Necessity of Identity and Intensionality. Necessitation is applied only
  to discharged C theorems, never to the optional predecessor assumption.
* `Iσ ∧ AT_(σ,σt) → PredOpσ`, Theorem 4.1 of
  [`numerical-inverses.md`](numerical-inverses.md).
* `NSections → NInv → AT ↔ CInv`, established in §3 of that note.

The new proof does not assume standardness, extensional fullness,
Plenitude, ND, numerical collection, or `□Iσ`.

## 2. A predecessor stabilizes the current numerical field

Fix a predecessor operation P witnessing PredOpσ. It immediately makes
successor injective on current numbers: apply P to `Sm=Sn`. Together with
zero-not-successor this gives current `I*σ`, hence current `Iσ`.

**Lemma 2.1.** Under PredOpσ,

    ∀m,n∈N, m≠n → □(m≠n).                         (ND-N)

**Proof.** Use N-induction on m with the displayed universal condition
over n as the induction property; P is an allowed parameter.

At zero, a current number n distinct from zero has a current numerical
predecessor a, with `n=Sa`. Numberhood of a persists, the identity
`n=Sa` is necessary, and zero-not-successor is a C theorem. Thus
`□(0≠n)`.

At `Sm`, fix a current number n with `Sm≠n`. If `n=0`, use the same
zero-not-successor argument. Otherwise choose current a∈N with `n=Sa`.
Then `m≠a`, so the induction hypothesis gives `□(m≠a)`. The current
predecessor equations

    P(Sm)=m,                  P(Sa)=a

are identities and hence necessary. At a possible point where `Sm=Sa`,
application congruence and those equations would yield `m=a`, a
contradiction. Therefore `□(Sm≠Sa)`, and the necessary identity `n=Sa`
gives `□(Sm≠n)`. This completes the internal induction. ∎

**Lemma 2.2.** Under PredOpσ, every current number remains different from
the bottom cardinality:

    ∀n∈N, □(n≠⊥ν).                               (proper-N)

Current `Iσ` gives `n≠Sn` for each current number n, by the ordinary
Peano induction excluding successor fixed points. Lemma 2.1 makes this
inequality necessary. If n became bottom, the C identity
`S(⊥ν)=⊥ν` would make `Sn=n` there. Contradiction. ∎

These conclusions quantify over **current** numbers. Neither says that
all future numbers are current or that `□Iσ` holds. A new future number
could be bottom without contradicting either lemma.

## 3. Prefixes and unconditional bounded numerical collection

Define an admitted binary relation B on ν by

    B(b,x) := ∀Z^(ννt) [PrefixClosed(Z) → Z(b,x)],

    PrefixClosed(Z) :=
      [∀n (Nn → Z(n,n))] ∧
      [∀n x (Z(n,x) → Z(Sn,x))].

Its intended reading is “x is at or before b.” This definition works
without noncollapse. In particular it does not build the optional I
assumption into B.

**Lemma 3.1 (all clauses in C).**

1. `B(b,x) → Nb ∧ Nx`; `Nn → B(n,n)`; and
   `B(b,x) → B(Sb,x)`.
2. The exact unfolding is

       B(b,x) ↔ [(Nb ∧ x=b) ∨ ∃a(B(a,x) ∧ b=Sa)].

3. `B(0,x) ↔ x=0`.
4. If `Nb` and `Sb≠⊥ν`, then

       B(Sb,x) ↔ [x=Sb ∨ B(b,x)].                 (prefix step)

5. `B(b,x) → B(Sb,Sx)`.
6. For all numerical b,x, `B(b,x) ∨ B(x,b)`.

**Proof.** For (1), use the defining leastness against the relation
`Nb∧Nx`; diagonal containment and closure follow directly from the
definition. For (2), call the displayed right side T. Diagonal containment
and closure give `T⊆B`. Conversely T contains every numerical diagonal;
if T(b,x), then B(b,x), so T(Sb,x) by the predecessor b. Thus T is
PrefixClosed and B⊆T.

Clause (3) follows from the unfolding and zero-not-successor, using the
numberhood of a supplied by B(a,x). For (4), a predecessor a with
`Sa=Sb` is numerical. The successor-collision lemma and `Sb≠⊥ν` force
`a=b`; the converse uses closure and the numerical diagonal.

For (5), apply the leastness of B to `Z(b,x):=B(Sb,Sx)`. This Z contains
the numerical diagonal and is closed in its first coordinate.

For (6), first N-induction gives B(b,0) for every numerical b. Then
N-induct on b to prove comparability with every numerical x. At zero
the preceding fact applies. At Sb, decompose x into zero or Sa. In the
successor case the induction hypothesis compares b with a; clause (5)
compares Sb with Sa. No noncollapse premise is used. ∎

**Theorem 3.2.** Under PredOpσ, for every current numerical b and every
admitted predicate X on ν,

    [∀x (B(b,x) → □Xx)]
        → □∀x (B(b,x) → Xx).                      (BBF-P)

**Proof.** N-induct on b, including universal quantification over X in
the induction property. At zero, B has only zero as a member, necessarily
by the C theorem (3), and the premise supplies `□X0`.

At Sb, the premise supplies both the hypothesis of BBF-P at b, by
closure of B, and `□X(Sb)`, by the numerical diagonal. The induction
hypothesis gives `□∀x(B(b,x)→Xx)`. Numberhood of b persists, and
Lemma 2.2 at the current number Sb gives `□(Sb≠⊥ν)`. Necessitate the
discharged C prefix-step theorem and instantiate it at b. Its premises
therefore hold necessarily, yielding

    □∀x [B(Sb,x) ↔ (x=Sb ∨ B(b,x))].

Combine the three boxed conclusions to obtain BBF-P at Sb. ∎

There is no unbounded Barcan principle here, and no replacement of the
current b by a standard numeral. The entire argument is internal
N-induction and covers nonstandard current bounds. Its improvement over
the earlier I-relative bounded lemma is that each old bound stays
strictly before overflow, by Lemma 2.2, even if I fails elsewhere.

## 4. Least-preimage realization from a predecessor and image stability

Let `f:νσ→τ`, with τ relational, and assume PredOpσ. Suppose also that
distinctions on its current numerical image are stable:

    ∀m,n∈Nσ, f(m)≠f(n) → □(f(m)≠f(n)).            (SI)

Define

    L_f(y,a) := Na ∧ f(a)=y ∧
                ∀z [(B(a,z) ∧ z≠a) → f(z)≠y].

**Current existence.** Every current y in f[N] has an L_f-preimage.
For completeness, induction on a proves that every nonempty predicate
restricted to the B-prefix at a has a least member in this sense. The
precise induction property, for a numerical bound b, is

    ∀Y [(∃x(B(b,x) ∧ Yx)) →
      ∃a(B(b,a) ∧ Ya ∧
        ∀z((B(a,z) ∧ z≠a) → ¬Yz))].

The zero case is immediate. At Sb, if the predicate has an instance in the
old B-prefix, use the induction hypothesis; otherwise its only possible
instance in the enlarged prefix is Sb, by the prefix-step clause.
Current PredOp gives I and hence all the needed current properness
conditions. Apply this to `z↦f(z)=y` below any current preimage a.

**Unconditional uniqueness.** C proves that L_f has at most one value
for each y, without I or PredOp. If a,a' are two distinct values, they
are numerical and comparable by Lemma 3.1(6). Whichever belongs to the
other's B-prefix contradicts that other's leastness clause.

**Persistence of a current witness.** Fix current `L_f(y,a)`. Numberhood
of a and the identity `f(a)=y` persist. For each current z with B(a,z),
if z=a, NI gives

    □(z≠a → f(z)≠y).

Otherwise current leastness gives `f(z)≠f(a)`; B implies Nz, so SI and
NI for `f(a)=y` give the same boxed implication. Apply BBF-P at a to
the admitted predicate `X(z):=(z≠a→f(z)≠y)`. It yields the necessary
universal leastness clause. Therefore **`□L_f(y,a)`**.

Necessitating the unconditional C uniqueness theorem now gives a
necessarily unique witness for the fiber at this current y. Define
the admitted operation

    μ_f(y)(X) := ∀a'^(νσ) [L_f(y,a') → a'(X)],
                                      X:σt.

At every possible point its value and a are universally coextensive,
because the fiber consists exactly of a. Intensionality gives the
actual identity `μ_f(y)=a`. Thus μ_f takes numerical values on the
current image and satisfies `f(μ_f(y))=y` there. When f is injective on
current numbers, it also satisfies `μ_f(f(a))=a` on that field.

This proves the strengthened least-preimage theorem:

    PredOpσ + SI
      ⇒ an admitted decoder selecting least current numerical preimages.

The chosen current a occurs only in a proof by existential elimination.
The single operation μ_f is defined uniformly before choosing an input;
no simultaneous choice operation or new type constructor is assumed.

## 5. Numerical sections and the exact equivalence

Suppose `f:νσ→νρ` is a current numerical map and both PredOpσ and
PredOpρ hold. Distinct current f-values are distinct current ρ-numbers,
so Lemma 2.1 at ρ supplies SI. Section 4 therefore gives a numerical
preimage selector on f[Nσ]. In particular, every current numerical
surjection has a numerical section, and every current numerical
bijection has a numerical inverse.

Consequently, over C, the following all-type guarded schemata are
equivalent:

    AT  ↔  CInv  ↔  NInv  ↔  NSections
        ↔  [Iσ → PredOpσ for every fixed counting type σ].

For the new direction, assume AT and fix σ,ρ with `Iσ∧Iρ`. The adjacent
instances AT_(σ,σt) and AT_(ρ,ρt) give the two predecessor operations by
Theorem 4.1 of `numerical-inverses.md`. The preceding argument supplies
the numerical section of any numerical surjection. Thus AT→NSections.
The reverse chain `NSections→NInv→AT↔CInv` is already established.
Guarded predecessors give NSections by the same argument, and AT gives
them by the adjacent instances.

This proves both requested arrows **AT→NInv** and **NInv→NSections**.
It also shows that the
adjacent predicate-type AT instances suffice for the whole AT schema:
they supply every guarded predecessor, which gives NSections and hence
all AT.

## 6. Scope and relation to the earlier semantic theorem

The conclusion concerns arbitrary C-models, including nonstandard
Henkin models. It does not prove `AT→(Iσ→□Iσ)` or
`PredOpσ→□Iσ` in unrestricted C. The new bounded argument was designed
to avoid precisely that inference: all old bounds remain proper, but
there need not be a common bound on genuinely new future numbers.

The complementary construction in
[`predecessor-henkin-countermodel.md`](predecessor-henkin-countermodel.md)
has all AT and predecessor instances, both quantified Infinity axioms,
and `Iσ ∧ ¬□Iσ` at every counting type. The present equivalence gives
NInv and NSections in that same model. Thus the gap from necessary
noncollapse is a proved separation, not merely a limitation of this proof.

The equivalences with local numerical stability in
[`model-separations.md`, §8](numerical-models.md) therefore retain their
every-object extensional-fullness premise. The AT/NInv/NSections and
guarded-predecessor part of that classification, by contrast, no longer
needs that semantic restriction. The earlier proofs remain valid; this
note strengthens their arithmetic-operation conclusions.

For arbitrary relational images τ, Section 4 still requires SI. Nothing
here asserts all-type ND or a decoder for every injective numerical map
with arbitrary nonnumerical image. Those stronger decoding principles
are distinguished in `numerical-inverses.md`, §§5–6.
