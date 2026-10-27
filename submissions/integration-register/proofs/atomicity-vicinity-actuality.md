# Atomicity and Vicinity imply Actuality

Source: original mathematical argument, 26 October 2026, §§1–4 (`misc`, unpaginated).

## 1. Result

Over C,

```math
\boxed{\mathrm{Atomicity}_t+\mathrm{Vicinity}
\ \Longrightarrow\ \mathrm{Actuality}.}
\tag{1}
```

Consequently, because current propositional ND implies Vicinity,

```math
\boxed{ND_t+\mathrm{Atomicity}_t
\ \Longrightarrow\ \mathrm{Actuality}.}
\tag{2}
```

All three premises in these statements are unboxed. No Barcan formula,
Functionality, choice, or Boolean completeness is assumed. Since Actuality
always implies Vicinity, (1) also gives the exact equivalence

```math
\boxed{\text{over }C+\mathrm{Atomicity}_t:\qquad
\mathrm{Actuality}\ \longleftrightarrow\ \mathrm{Vicinity}.}
\tag{3}
```

Here $`p\le q`$ is Boolean-algebraic entailment, equivalently
$`\Box(p\to q)`$, rather than material implication. An atom is a nonzero
proposition with no nonzero strict lower bound. Atomicity at t says every
nonzero proposition has an atom below it. Actuality says that some true
proposition entails every true proposition. Vicinity weakens the last
requirement to entailing the possibility of every truth. Finally,
$`ND_t`$ is $`\forall p^tq^t(p\ne q\to\Box(p\ne q))`$.

The proof uses the common-core lemma already established in §1 of
[The supported C5 interpretation from Vicinity](../../next-update/proofs/vicinity-supported-interpretation.md).
That lemma develops the mechanism of Christopher Sun's 19 October 2026
argument recorded under the 5-necessity variant of
[Vicinity](../../../logical-maps/topics/classicism/principles/vicinity.yaml).
Section 2 repeats its proof so that the precise quantifier scope is visible.
The new step here is its application to atom decisions, in §3.

## 2. The true core and its quantified-bound property

Let $`w`$ witness Vicinity. Put

```math
A_w:=\forall r^t(r\to w\le\Diamond r),
\qquad s:=w\land A_w.
```

Both $`w`$ and $`A_w`$, hence $`s`$, are true. For every admitted type
$`\sigma`$ and every admitted predicate $`F^{\sigma t}`$,

```math
\boxed{\forall x^\sigma(s\le F(x))
\ \Longrightarrow\ s\le\forall x^\sigma F(x).}
\tag{4}
```

This is a bound on the proposition denoted by the quantified formula; it
does not assert an unrestricted Barcan formula.

To prove it, suppose $`T:=\forall x(s\le F(x))`$ is true. Since $`w\land T`$
is true, Vicinity gives

```math
w\le\Diamond(w\land T).
\tag{5}
```

Work at any accessible evaluation where $`s`$ is true, and suppose that
an available $`x`$ satisfies $`\neg F(x)`$. The $`A_w`$ conjunct of $`s`$
applied there to the true proposition $`s\land\neg F(x)`$ gives

```math
w\le\Diamond(s\land\neg F(x)).
\tag{6}
```

Every algebraic bound is a positive identity and persists by Necessity
of Identity, or equivalently by S4 in its boxed formulation. Thus (5)
still holds. As $`w`$ holds, there is a further accessible evaluation
where $`w\land T`$ holds. The parameter $`x`$ is still available there;
this uses the converse-Barcan direction supplied by C, not BF. At that
evaluation $`T`$ yields $`s\le F(x)`$, whereas the persistent bound (6)
and the truth of $`w`$ yield $`\Diamond(s\land\neg F(x))`$. These are
incompatible. Every available $`x`$ therefore satisfies $`F(x)`$ at every
accessible evaluation where $`s`$ holds, which proves (4).

This is the usual S4/converse-Barcan derivation expressed using accessible
evaluations. No optional premise was necessitated: the only transported
assertions are the already obtained boxed bounds (5) and (6). In
particular, $`T`$ itself was not transported from the original evaluation;
Vicinity supplies a new evaluation at which $`T`$ is true.

## 3. Collecting the decisions of an atom

Write $`\mathsf A`$ for the closed Actuality proposition. Fix any current
atom $`a`$. For every current proposition $`q`$, Boolean atomicity gives

```math
D_a(q):=(a\le q\ \lor\ a\le\neg q).
\tag{7}
```

Indeed $`a\land q\le a`$, so $`a\land q`$ is either $`a`$ or zero. In the
first case $`a\le q`$, and in the second $`a\le\neg q`$.

Whichever disjunct in (7) is true is an algebraic identity, and so is
necessary by NI. Hence each current $`D_a(q)`$ is necessary. In particular
$`s\le D_a(q)`$ for every current $`q`$. Applying (4) with
$`F(q)=D_a(q)`$ gives

```math
s\le\forall q^t\,D_a(q).
\tag{8}
```

C proves the universally closed implication

```math
\left(a\land\forall q^t(a\le q\lor a\le\neg q)\right)
\ \longrightarrow\ \mathsf A.
\tag{9}
```

For if $`a`$ is true and $`q`$ is true, the alternative $`a\le\neg q`$
is impossible, leaving $`a\le q`$; thus $`a`$ is an Actuality witness.
Since (9) is a theorem of C without optional assumptions, its
necessitation is legitimate. Combining this theorem with the algebraic
bound (8) gives

```math
s\land a\le\mathsf A,
\qquad\text{equivalently}\qquad a\le(s\to\mathsf A).
\tag{10}
```

The atom $`a`$ was arbitrary. The dual form of Atomicity says that a
proposition entailed by every current atom is necessary. Applying it to
$`s\to\mathsf A`$ yields

```math
\Box(s\to\mathsf A).
```

Since $`s`$ is true, $`\mathsf A`$ is true. This proves (1).

Equivalently, if $`s\land\neg\mathsf A`$ were nonzero, Atomicity would
give an atom below it, and (10) would put that atom below both
$`\mathsf A`$ and its negation. Thus $`s\le\mathsf A`$.

Notice the exact role of (4): it collects the necessities of the individual
atom decisions only below the true core $`s`$. We never infer
$`\Box\forall qD_a(q)`$ from $`\forall q\Box D_a(q)`$, and we never infer
that a current atom remains an atom everywhere.

## 4. The answer with current ND

The recorded [ND_t implies Vicinity](../../../logical-maps/topics/classicism/results/distinctness-necessary-t-implies-vicinity.yaml)
argument is short. If $`q`$ is true, then $`q\ne\bot`$. Current $`ND_t`$
gives $`\Box(q\ne\bot)`$, which is $`\Box\Diamond q`$. Thus $`\top`$
entails $`\Diamond q`$ for every current truth $`q`$, so $`\top`$ is a
Vicinity witness. Combining this with (1) proves (2).

This also identifies a concrete core for (2): take

```math
s=\forall r^t(r\to\Box\Diamond r).
```

It is currently true by $`ND_t`$; its truth at other evaluations is used
only where $`s`$ is explicitly assumed. It need not be identified with
$`\top`$.

## 5. Pointwise reversible separation

Let Sₚₜ assert separation by admitted operations whose current outputs preserve conjunction and whose current square is the identity. Write OneAtom for the existence of a Boolean atom among propositions. The [atom-swap construction](pointwise-atomicity.md#4-principal-atom-evaluators-and-a-current-atom-swap) gives the converse in

```math
S_{\mathrm{pt}}+\mathrm{OneAtom}
\quad\longleftrightarrow\quad ND_t+\mathrm{Atomicity}_t.
```

Separation and one atom give NDₜ, Actuality and Atomicityₜ: send the atom to a true atom, and transport that true atom below any given nonzero proposition. Conversely NDₜ and Atomicityₜ supply Actuality by §4, and swapping a suitable atom with a true atom gives the required observers. Thus under Atomicityₜ, Sₚₜ is exactly NDₜ.
