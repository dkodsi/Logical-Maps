# One alternating bit gives higher-type numerical recursion

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Scope and the new result

Work in the map's fixed relational Classicism C. Fix a counting type σ,
write ν=(σt)t, and abbreviate its Frege numbers, successor and zero by
N,S,0. Write b=bottom_ν for the empty cardinality, distinct from zero.

The previously proved condition

    PNσ := ∀n∈N, □(n≠b)

is equivalent to predecessor existence and to current noncollapse Iσ
plus necessary distinctness restricted to current numbers. See
[streamlined-proof.md](protected-number-operations.md). The new theorem is that
this condition supplies **uniform primitive recursion with outputs at
every relational type**, including higher operation types. Conversely,
even one proposition-valued operation alternating under successor forces
the condition.

Thus the alternating-bit requirement is a test for a broad mathematical
closure property, not merely another failure of a particular operation
under Max. The positive direction supplies concrete pure recursor terms
and, in particular, higher-type definitions satisfying the Ackermann
recursion equations.

## 2. The least computation graph

Fix any relational output type τ=ρ₁…ρₖt (k may be zero), an initial
value a:τ, and an admitted step operation f:ν→τ→τ. Write f(n,y) for
left-nested application. Define R=R_(a,f) by

    R(n,y) := ∀Z^(ντt),
      [Z(0,a) ∧ ∀m z (Z(m,z) → Z(Sm,f(m,z)))] → Z(n,y).

This is a least relation, constructed by ordinary abstraction. C proves:

1. R(0,a), and R(n,y)→R(Sn,f(n,y)).
2. R(n,y)→Nn.
3. ∀n∈N ∃y R(n,y).
4. R(n,y)→□R(n,y).
5. The exact unfolding

       R(n,y) ↔ [(n=0 ∧ y=a) ∨
         ∃m z (R(m,z) ∧ n=Sm ∧ y=f(m,z))].

For (2), N applied to the first coordinate is a closed candidate relation.
For (3), numerical induction applies to the property ∃y R(n,y).
For (4), use Z(n,y):=□R(n,y) as the closed candidate: its base follows
by necessitating the discharged C base theorem, and its closure follows
from K and the necessitated C successor theorem. The parameters a,f
are arbitrary throughout these C derivations; no optional correctness
assumption about f is necessitated.

For (5), let V be its displayed right side. Base and successor closure
give V⊆R. Since V contains (0,a), and V⊆R makes V successor-closed,
leastness gives R⊆V. These arguments use no Choice, BF, noncollapse,
numerical standardness, or stability of distinctions in the output type.

## 3. Local functionality and a pure recursor

**Lemma (C).** At each nonbottom numerical source the graph has exactly
one output:

    Nn ∧ n≠b → ∃!y R(n,y).

Existence was just proved. For uniqueness, induct on n with the conditional
property n≠b→uniqueness. Zero is never a successor, so unfolding gives
only a at zero. Suppose Sn≠b. Since Sb=b, also n≠b. Every predecessor
m appearing in the unfolding at Sn is numerical and has Sm=Sn.
The C successor-collision theorem, whose only exceptional output is b,
therefore gives m=n. The induction hypothesis identifies the predecessor
outputs z; congruence for f identifies their successor outputs. This
proves the conditional induction step.

Define the fixed pure term

    Rec_τ(a,f,n)[x₁,…,xₖ] :=
      ∃y^τ (R_(a,f)(n,y) ∧ y[x₁,…,xₖ]).

**Theorem.** Under PNσ, for every a,f and every current n∈N,

    R_(a,f)(n,Rec_τ(a,f,n)),
    Rec_τ(a,f,0)=a,
    Rec_τ(a,f,Sn)=f(n,Rec_τ(a,f,n)).

Choose the graph output y at a current numerical input n. R(n,y)
persists. The numberhood of n persists, and PN makes n necessarily
nonbottom. The necessitated local functionality theorem therefore makes
y the unique graph output at n necessarily. At every future argument
tuple, the displayed existential pooling is consequently equivalent to
y's application. Intensionality gives Rec_τ(a,f,n)=y as whole-object
identity. Base and successor closure now give the equations.

The zero equation is actually a theorem of C without PN, since zero is
necessarily nonbottom. For the successor equation at a particular n,
protection of Sn alone suffices. The theorem above gives the uniform
package at all current numerical inputs.

This is one explicit pure recursor for the fixed pair of types σ,τ,
not a use of Choice to assemble separately existing solutions. It is
uniform in the initial value and the step operation. If g,h both satisfy
the same recursion equations, numerical induction gives g(n)=h(n) on
all current numbers. No equality of their values outside N, or of the
whole operations g,h, is asserted.

## 4. A single alternating bit is enough

Let Altσ be the simple assertion

    ∃A^(νt) ∀n∈N, A(Sn)=¬A(n).

Neither a zero normalization nor an Iσ guard is included.

**Theorem (C).** Altσ↔PNσ.

Suppose A witnesses Altσ. For a current number n, the actual identity
A(Sn)=¬A(n) is necessary by NI. C proves necessarily that a proposition
differs from its negation. Hence □(A(Sn)≠A(n)), and application congruence
gives □(Sn≠n). If n became b, the C identity Sb=b would make Sn=n
there, a contradiction. Thus every current number is protected from b.

Conversely apply the pure recursor with output type t, initial value
bottom_t, and step f(n,p):=¬p. Its successor equation is Altσ. Current
numerical induction also makes every output either bottom_t or top_t.
Thus the witness can be chosen as a genuinely two-valued parity operation,
normalized to bottom at zero.

Putting the previous results together, over C the following are equivalent:

    an alternating propositional operation;
    a normalized two-valued parity operation;
    PNσ;
    predecessor existence;
    Iσ ∧ numerical NDσ;
    primitive recursion into every relational output type.

For the last-to-first direction one may take output type t and negation.
Alternatively recursion at output type ν, with f(n,y)=n, directly gives
predecessor. The forward direction is stronger than the existential
recursion schema: the displayed pure Rec term supplies every instance.

## 5. Positive computational consequences

Zero, successor and projections are admitted pure operations. Composition
is admitted by abstraction. The recursor therefore represents every
primitive-recursive numerical function on the current numerical field.
This is an external induction on finite function definitions, with all
correctness claims quantified over the internal numbers. It does not
assume that those numbers are externally standard.

The output type may itself be ν→ν, so the construction goes further than
first-order primitive recursion. Here is an explicit higher-type example.
For an operation g:ν→ν define

    It(g,0,a)=a,
    It(g,Sn,a)=g(It(g,n,a))

using Rec_ν with step (n,y)↦g(y). Define a sequence of operations G by
Rec_(νν), with initial operation S and step

    F(m,g) := λn. It(g,Sn,1),       where 1:=S0.

Put Ack(m,n):=G(m)(n). Under PNσ the recursor equations give

    Ack(0,n)=Sn,
    Ack(Sm,0)=Ack(m,1),
    Ack(Sm,Sn)=Ack(m,Ack(Sm,n))

for all current numerical m,n. These are the usual Ackermann recursion
equations. The second uses It(g,1,1)=g(1); the third unfolds one more
iteration. Numerical induction shows that It preserves numerical outputs
when g does, and then that every G(m) maps numbers to numbers. Thus the
equations are assertions about numerical values, not merely arbitrary
objects at numerical type.

Both the inner and outer recursors are the fixed pure terms of §3. No
functional-choice principle is used to choose a sequence of operations.

## 6. Scope, separations, and significance

The result turns a very modest computational demand—one alternating
truth bit—into an exact criterion for arbitrary higher-type numerical
primitive recursion. This broad positive closure theorem and its explicit
higher-type constructions are the new content. The earlier finite-collapse
obstruction already excluded parity under Max; that exclusion alone is
not being counted again.

The existing model separations transfer through the theorem. The
finite-support monotone-map model satisfies the numerical package and
quantified Infinity at e and t while failing global ND, Actuality and
Atomicity. It therefore supports all these recursors without those global
principles. The Henkin predecessor model supports the recursors while
Iσ∧¬□Iσ holds: new future numbers can appear beyond the protected current
ones. See [model-separations.md](numerical-models.md) and
[predecessor-henkin-countermodel.md](predecessor-henkin-countermodel.md).

Pure Max excludes the package by the earlier predecessor theorem. None
of these arguments proves Max alone inconsistent, makes current recursion
correct on every future number, or asserts that every arithmetically
definable total relation has an operation representative.

## Sources

- [Exact framework](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/topic.yaml) and
  [Frege definitions](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/background.md).
- [Protected-number equivalence and local comparison functionality](protected-number-operations.md),
  §§1–3, for the C arithmetic toolkit and the earlier pooling template.
- [Frege research note](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md),
  §§18 and 26, for persistent numberhood and collision only at bottom.
- This note, §§2–5, supplies the new least-computation-graph, alternator
  equivalence and higher-type recursion arguments; source identifier `misc`.
