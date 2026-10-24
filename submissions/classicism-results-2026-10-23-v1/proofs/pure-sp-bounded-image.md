# The bounded image obstruction to a pure SP construction

Original mathematical argument, direct source misc; unpaginated.

## Fixed target and inputs

Retain the original finitary pure language, relational types, and fixed
theory `Max(C)`. Write `H = Box_ne` and `D = Diamond_ne`. The target is

    Con(Max(C) + U_G + D(not G#)),

equivalently `Con(Max(C) + G# + D(not G#))`. Here `G` is **the same** true
independent arithmetic Pi^0_2 sentence specified by the fixed-point
construction in [strong-possibility.md](../source/research/2026-10-22/followup/strong-possibility.md),
“An effectively specified arithmetic sentence independent of Max.” In
particular PA proves `G <-> not Pr_Max(code(G#))`. Write its fixed Pi^0_2
presentation as

    G = forall n exists m delta(n,m),

with bounded arithmetic `delta`, allowing the standard finite tuple coding
and including the finite computation witnesses in `m` when taking the
Sigma^0_1 normal form. This is a PA-equivalent presentation of the specified
fixed-point sentence, not a newly chosen independent sentence.
The displayed arithmetic notation is interpreted by the original relational
Sum/Prod translation; it adds no function symbols or types to C. `U_G` is
the previously specified universal identity presentation. Its identity terms
can contain quantifiers; its outer universal/finite-Boolean-identity grammar
does not say that those terms are quantifier-free.

The source already proves the following local criterion in
[strong-possibility-one-way.md](../source/research/2026-10-22/followup/strong-possibility-one-way.md),
section 3:

    M satisfies D(P)
      iff some genuine Max+P model N admits an L_alg embedding
          Alg(M) -> Alg(N).

Here `L_alg` contains every pure term operation, including quantified term
values, and omits actual truth. The criterion uses the complete algebraic
diagram, finite Max supports, compactness and Henkin completeness; it does
not construct a new Henkin truth on an arbitrary algebra. Applying it with
`P = not G#` reduces the target to genuine Max models `M,N` and such an
embedding `f`, with `M` satisfying `G#` and `N` satisfying `not G#`.

The same source, sections 1 and 4, proves that `f` restricts to an arithmetic
embedding of actual number fields, and that an `N`-counterexample to `G`
cannot be in its image. The new point below is stronger: **every such
counterexample is greater than every number in that image.**

## Bounded-segment transfer

**Lemma.** Let `M,N` be genuine `C+I_e` points and `f` a homomorphism between
their full pure-term algebras. Suppose `M` satisfies `G#`. For every actual
number `b` of `M`, `N` satisfies

    forall n <= f(b), exists m delta(n,m).

This statement ranges over **all** actual numbers of `N` below `f(b)`,
including ones not in the image. We do not assume that the numerical image
is an initial segment, or that the map preserves arbitrary truth.

**Proof.** Work first in the PA interpretation of `M`. By induction on `b`,
the sentence `G` implies

    forall b exists d forall n <= b exists m <= d delta(n,m).       (1)

For `b=0`, take a witness for `delta(0,m)`. At the successor step, combine
the preceding bound `d` with a witness `w` for `delta(b+1,w)`, taking a
number at least both `d` and `w`. The PA ordering laws show it bounds all
the required witnesses. This is an ordinary internal finite induction,
valid also for nonstandard `b`; it is not an external enumeration of the
source number field and does not use Choice.

Fix any actual number `b` of `M`, and choose `d` supplied by (1). Set

    theta(b,d) := forall n <= b exists m <= d delta(n,m).

This is bounded arithmetic. The bounded conditional-rigidity lemma in
[strong-possibility.md](../source/research/2026-10-22/followup/strong-possibility.md),
“Max already decides the first arithmetic level,” gives, at `M`, the literal
proposition identity

    I_e meet theta#(b,d) = I_e.                                    (2)

That lemma uses necessity of numberhood, numerical distinctness, and the
conditional rigidity of Sum/Prod, followed by bounded arithmetic induction.
It retains `I_e` as an antecedent; neither `G` nor any Max premise is
necessitated. In particular it is available here for nonstandard numerical
parameters, not merely standard numeral substitutions.

The full-term homomorphism preserves (2), its pure coefficient `I_e`, and
the value of the **whole quantified term** `theta#`. Its numerical images
are actual numbers in `N`, by necessary numberhood. Thus

    I_e meet theta#(f(b),f(d)) = I_e

holds at `N`. Since `N` satisfies `I_e`, this gives
`theta#(f(b),f(d))`, and hence the lemma. The transport step would be
unjustified for an arbitrary atomic arithmetic embedding. Here it uses
preservation of the quantified term operation; alternatively the established
Sigma^0_1 preservation theorem for these full-term maps gives the same
transfer. QED.

## The bounded-image obstruction

**Theorem.** Suppose `M,N` are genuine Max models, `M` satisfies `G#`, `N`
satisfies `not G#`, and `f:Alg(M)->Alg(N)` is a full-term embedding. Every
actual numerical counterexample `c` to `G` in `N` satisfies

    f(b) < c   for every actual number b of M.                      (3)

**Proof.** If `c <= f(b)`, bounded-segment transfer gives a witness to
`delta(c,m)` in `N`, contradicting the choice of `c`. The PA linear order
then gives `f(b)<c`. This applies to every `b` of `M`, including its
nonstandard numbers. QED.

Full PA least-number induction in `N` supplies a least counterexample `c`:
the formula `not exists m delta(n,m)` defines a nonempty numerical set there.
Thus (3) holds for its least element. In particular:

- The numerical image is bounded above in `N`; a cofinal numerical map is
  impossible. Properness alone was the weaker earlier obstruction.
- Every counterexample, including the least one, is nonstandard and lies
  strictly above every source number, not just above every standard numeral.
- The downward closure of the numerical image in `N` contains only numbers
  satisfying `exists m delta(n,m)`. This does not say that image equals its
  downward closure or that it is elementary.
- The conclusion also holds for full-term homomorphisms, where the local
  model-existence criterion happens to supply an embedding: numerical
  injectivity already follows from the `C+I_e` hypotheses and preservation
  of the pure term operations.

Consequently the exact target can be restated as the existence of genuine
Max models `M,N`, with `M` satisfying `G#`, and a full-term embedding into
`N`, together with an `N`-number `c` such that

    not exists m delta(c,m),
    forall b in Num(M), f(b) < c.

The forward direction is the existing local embedding criterion plus the
theorem just proved; the reverse direction uses the criterion, since the
counterexample makes `N` a Max+not-G model. The final displayed universal
condition is an external statement about the embedding; it does not extend
the original pure language.

In particular the following finite package of semantic requirements is
inconsistent:

    M,N are genuine Max models;
    f is a full pure-term embedding Alg(M) -> Alg(N);
    M satisfies G# and N satisfies not G#;
    for every c in Num(N), some b in Num(M) has c <= f(b).

Only the last requirement, numerical cofinality, is extra. Removing it
returns to the still-unsettled original pair. This is not a claim that the
background full-term operation diagram itself is finitely axiomatized.

## What finite numerical approximations do and do not do

For every external standard `k`, Max already proves the standard finite
restriction of `G` to `n<=k`: all its finitely many Sigma^0_1 instances are
true and PA-provable. The guarded universal-identity presentation of that
finite restriction follows by the same conditional-rigidity argument.
Accordingly adding every such **standard** finite restriction to
`Max+D(not G#)` leaves a consistent theory, because each restriction is
already a Max theorem and `Max+not G#` is consistent. This is only a check
on a possible proof strategy: arbitrarily long standard numerical tests
cannot replace `U_G` at a nonstandard point.

By contrast, the new theorem uses internal finite bounding at **each source
number**, even a nonstandard one, and transfers its single bounded formula
through a full-term map. That distinction is why the conclusion is stronger
than the earlier exclusion of witnesses at image numbers.
