# The atomic part of current pointwise reversible separation

26 October 2026. Ordinary mathematical research by OpenAI Codex in the fixed
relational theory C. Direct source: `misc`, this note, sections 1–6, unpaginated.

## 1. Exact statement

Use the definitions from [the main report](pointwise-reversible-separation.md), section 1:

```math
\begin{aligned}
K_{\rm pt}(E)&:=
\forall p,q\,[E(p\land q)=Ep\land Eq]
\land\forall p\,[E(Ep)=p],\\
S_{\rm pt}&:=\forall p,q\,[(\forall E^{tt}\, .\,
K_{\rm pt}(E)\to(Ep\leftrightarrow Eq))\to p=q]
\end{aligned}
```

All proposition variables have type t. Preservation and involution are
pointwise **identities**, rather than material biconditionals; neither is a
whole-operation identity. Every observer is an admitted term of type tt.

Write $`\mathrm{OneAtom}:=\exists a\,\mathrm{Atom}(a)`$, and use
the database's Boolean-order definitions of Atomicity at t and Actuality.
In C, Actuality is equivalently the existence of a true Boolean atom. The
proof of that equivalence is included below.

**Theorem.** Over C,

```math
\boxed{
S_{\rm pt}\land\mathrm{OneAtom}
\quad\longleftrightarrow\quad
ND_t\land\mathrm{Atomicity}_t}
\tag{1}
```

All assumptions in (1) are current. No BF, C5, necessary atomhood, necessary
Atomicity, or quantifier preservation is used in either direction.

Consequently, under current $`S_{\rm pt}`$,

```math
\mathrm{OneAtom}
\longleftrightarrow\mathrm{Atomicity}_t
\longleftrightarrow\mathrm{Actuality}
\tag{2}
```

## 2. Current order automorphisms and true atoms

If $`K_{\rm pt}(E)`$, E is a bijection of the current Boolean algebra of
propositions, with inverse E. Meet preservation makes it order preserving.
If $`Ep\le Eq`$, then
$`E(p\land q)=Ep\land Eq=Ep`$, so applying E gives $`p\land q=p`$.
Thus it also reflects order. It therefore preserves endpoints, complements,
joins, and atoms as current algebraic facts. These claims require no
Functionality or whole-operation identities.

A true atom w entails every true proposition: if q is true, then
$`w\land q`$ is true and hence nonbottom; atomhood yields
$`w\land q=w`$. Thus w witnesses the database's Actuality formula.
Conversely, suppose w is true and entails every true proposition. For any p,
either p or its negation is true, so w entails one of them. Since w is
nonbottom, this makes it an atom. Hence Actuality is exactly a true atom.

## 3. From one atom and separation to the atomic package

The main report's equality-reflection argument gives
$`S_{\rm pt}\to ND_\sigma`$ at every admitted type; in particular it gives
the displayed $`ND_t`$ conjunct of (1).

Choose any atom a. It is nonbottom. Separating a from Bottom gives a
$`K_{\rm pt}`$-observer E with Ea true, because E fixes Bottom. Since E
preserves atoms, Ea is a true atom. Section 2 gives Actuality; fix a true
atom w.

Now let d be any nonbottom proposition. Separate d from Bottom by a
$`K_{\rm pt}`$-observer T, so Td is true. Actuality gives $`w\le Td`$.
Apply the inverse T to obtain $`Tw\le d`$. The proposition Tw is an atom,
so every nonbottom proposition has an atom below it. This is Atomicity at t.

This proves the forward implication of (1). Atomicity applied to Top yields
OneAtom, and Actuality supplies one directly; these observations establish
(2) once the converse below is proved.

## 4. Principal atom evaluators and a current atom swap

Assume $`ND_t`$ and Atomicity at t. The [Atomicity and Vicinity theorem](atomicity-vicinity-actuality.md#4-the-answer-with-current-nd), together with NDₜ ⇒ Vicinity, supplies Actuality. For a current atom a define
the admitted operation

```math
A_a(p):=\Box(a\to p)
\tag{3}
```

We need only current pointwise facts about this operation. For each current
p, atomhood gives $`a\le p`$ or $`a\le\neg p`$. In the first case
$`A_a(p)`$ is true and is necessary by 4, so $`A_a(p)=\top`$. In the
second case, $`a\le\neg p`$ persists: it is an algebraic identity, so NI
applies. Moreover $`a\ne\bot`$ persists by the current $`ND_t`$ premise.
Necessarily, therefore, $`a\le p`$ fails, giving $`A_a(p)=\bot`$.

Thus

```math
A_a(p)=\top\quad\Longleftrightarrow\quad a\le p,
\qquad
\forall p\,[A_a(p)=\top\lor A_a(p)=\bot]
\tag{4}
```

No universal quantifier has been moved across a box: the argument treats
each current p and then generalizes at the current point. In particular it
does not assert $`\Box\mathrm{Atom}(a)`$.

The set of propositions above a is a Boolean ultrafilter. Together with the
endpoint values in (4), this shows that $`A_a`$ is a Boolean homomorphism
in the pointwise-identity sense. It fixes Top and Bottom. Also, for every p,

```math
a\land A_a(p)=a\land p
\tag{5}
```

For arbitrary nonbottom d, if d is true, the identity observer already
accepts it. Otherwise choose an atom $`a\le d`$ and a true atom w. Since
d is false, a and w are distinct and therefore disjoint. Put
$`r=\neg(a\lor w)`$ and define the admitted operation

```math
T(p)=(a\land A_w(p))\lor(w\land A_a(p))\lor(r\land p)
\tag{6}
```

The three guards a,w,r form a Boolean partition. Each operation
$`A_w,A_a,I`$ is a current pointwise Boolean homomorphism. Distributivity
therefore proves, for every current p,q,
$`T(p\land q)=Tp\land Tq`$.

To check involution, note that $`A_a(a)=A_w(w)=\top`$,
$`A_a(w)=A_w(a)=\bot`$, and both evaluators send r to Bottom. Since each
evaluator fixes endpoint values and the other evaluator is endpoint-valued,
expansion of (6) gives

```math
A_a(Tp)=A_w(p),\qquad A_w(Tp)=A_a(p)
```

A second expansion, followed by (5), yields

```math
\begin{aligned}
T(Tp)
&=(a\land A_a(p))\lor(w\land A_w(p))\lor(r\land p)\\
&=(a\land p)\lor(w\land p)\lor(r\land p)=p
\end{aligned}
```

Hence $`K_{\rm pt}(T)`$. Since $`a\le d`$, we have $`A_a(d)=\top`$.
The term $`w\land A_a(d)`$ is true, so Td is true. Thus every nonbottom d
has a qualifying observer accepting it.

Finally, if $`p\ne q`$, their Boolean symmetric difference d is nonbottom.
Choose the observer just constructed for d. Pointwise Boolean preservation
turns the truth of Td into $`\neg(Tp\leftrightarrow Tq)`$. This proves
$`S_{\rm pt}`$, completing (1).

The proof deliberately concludes only pointwise laws for T. Upgrading them
to whole-operation identities would erase the genuine boundary witnessed
by the two-object retract in the main report.

## 5. Modal consequence and limits

Combining (1) with $`\Box S_{\rm pt}\leftrightarrow\mathrm{Rev}`$ from the
main report gives

```math
\boxed{
\Box S_{\rm pt}\land\mathrm{OneAtom}
\quad\longleftrightarrow\quad
\mathrm{C5}\land\mathrm{Atomicity}_t}
\tag{7}
```

For the forward direction, Rev supplies C5, and section 3 supplies current
Atomicity. For the reverse, the established endpoint-separation theorem
supplies Rev and hence $`\Box S_{\rm pt}`$; Atomicity supplies OneAtom.
Equivalently, (7) is the full endpoint-separation package.

The same package is equivalent to the separately explicit sentence

```math
\Box\bigl(ND_t\land\mathrm{Atomicity}_t
\land\mathrm{Actuality}\bigr)
\tag{8}
```

Indeed (8) gives boxed ND at t and current Atomicity; boxed type reduction
gives C5. Conversely C5 plus current Atomicity gives necessary Atomicity
and necessary Actuality by the recorded background theorems.

The current package in (1) is strictly weaker than (7): the full two-object
retract satisfies current $`S_{\rm pt}`$ and has propositional atoms but
fails BF at t and Rev.

## 6. Which hypotheses are needed?

**ND cannot be omitted.** In the established
[full two-object chain](../../classicism-results-2026-10-24-v2/source/topics/classicism/models/full-two-object-chain.yaml),
the root propositions are all subsets of its two outgoing arrows,
$`1_r,h:r\to s`$. Thus the root Boolean algebra is atomic, and
$`\{1_r\}`$ is a true atom, giving Actuality. But transport along h sends
this atom to Bottom. It is currently distinct from Bottom and later
identical to it, so ND at t fails. Since $`S_{\rm pt}`$ implies ND,
Atomicity and Actuality alone do not imply pointwise separation.

**Atomicity cannot be omitted, even with all-type current ND and necessary
Actuality.** Use the established
[finite-support sections-and-projection model](../../classicism-results-2026-10-24-v2/source/topics/classicism/models/finite-support-sections-and-projection.yaml).
Its objects have individuals $`\mathbb N`$ and
$`\mathbb N\times\{0,1\}`$. The outgoing arrows at the first object are
the identity and the sections $`f_T(n)=(n,T(n))`$, one for every binary
sequence T; the projection $`\pi(n,i)=n`$ satisfies
$`\pi f_T=1`$. Therefore transport along each outgoing arrow has a left
inverse at every admitted type. It preserves distinctness, so full current
ND holds. The model's recorded argument proves necessary Actuality; at the
root, the singleton identity arrow is already a true atom, admitted because
it is the only outgoing arrow returning to that object.

Nevertheless the admitted proposition
$`d=\{f_T:T(0)=0\}`$ has no atom below it. A nonempty subproposition
pinned by finitely many individuals contains all sections agreeing with
one of its members on those individuals. Choose an additional coordinate
m. Splitting according to $`T(m)=0`$ or $`T(m)=1`$ gives two nonempty
admitted pieces. Thus Atomicity at t fails. Were $`S_{\rm pt}`$ true, its
true root atom and section 3 would imply Atomicity, a contradiction.

A sharper model-class consequence holds in the standard ideally full
finitely pinned action models over categories of sets. In that family,
$`ND_e+\mathrm{OneAtom}`$ already implies Actuality. To see this,
choose an arrow f belonging to a propositional atom A. Codomain tests and
single-coordinate cylinders are admitted. They distinguish f from every
other arrow, so intersecting them with A shows that $`A=\{f\}`$.
Let a finite set M pin this singleton. ND at e makes every outgoing arrow,
in particular f, injective. If a root endomorphism u agrees with the
identity on M, then $`f\circ u`$ agrees with f on M and has its codomain;
pinning gives $`f\circ u=f`$, and injectivity gives $`u=1`$.
Consequently M also pins the singleton identity arrow, a true atom.
Since ND at t already implies ND at e, the same conclusion holds there with ND at t. The argument
depends on ideal fullness and the finite-coordinate cylinder semantics;
it is not asserted for arbitrary Henkin restrictions.

**The unboxed type reduction is already known.** No novelty is claimed for
the consequence of (1) that ND holds at all types. Over C, ND at t alone
already implies modal 5, then modal B, and then ND at every admitted type.
Those are the proved records
[ND at t implies 5](../../classicism-results-2026-10-24-v2/source/topics/classicism/results/distinctness-necessary-t-implies-modal-five.yaml),
[5 implies B](../../classicism-results-2026-10-24-v2/source/topics/classicism/results/modal-five-implies-modal-b.yaml),
and [B implies all-type ND](../../classicism-results-2026-10-24-v2/source/topics/classicism/results/modal-b-implies-distinctness-necessary-r.yaml).
Directly, if $`a\ne b`$ at any type, put $`c=(a=b)`$. Then
$`c\ne\top`$, so ND at t gives $`\Box(c\ne\top)`$. Necessitated NI
gives $`\Box(c\to c=\top)`$, hence $`\Box\neg c`$.

## Sources and status

The new current equivalence and its atom-swap proof are the original
arguments in this note. The framework and exact principle definitions are
recorded in [background.md](../../classicism-results-2026-10-24-v2/source/topics/classicism/background.md),
[Atomicity at t](../../classicism-results-2026-10-24-v2/source/topics/classicism/principles/atomicity-t.yaml),
[Actuality](../../classicism-results-2026-10-24-v2/source/topics/classicism/principles/actuality.yaml), and
[ND at t](../../classicism-results-2026-10-24-v2/source/topics/classicism/principles/distinctness-necessary-t.yaml).
Their source is Bacon and Dorr, *Classicism*, draft of 16 May 2023,
Proposition 2.2, p. 22, and section 2.2, pp. 24–25.

The swap in section 4 adapts the previously recorded construction in
[Logical observer separation and its hierarchy](../../classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md),
section 4, while reducing its scope to current pointwise laws and removing
BF from this local argument. The necessary atomicity and actuality facts
used only in section 5 are recorded in
[C5 and Atomicity imply necessary Atomicity](../../classicism-results-2026-10-24-v2/source/topics/classicism/results/c5-and-atomicity-imply-necessary-atomicity.yaml)
and [Atomicity at t and BF imply necessary Actuality](../../classicism-results-2026-10-24-v2/source/topics/classicism/results/atomicity-t-and-bf-imply-necessary-actuality.yaml):
*Classicism*, Propositions 2.6–2.7, pp. 25–26, and the concluding equivalences
on p. 33. Type-t Atomicity lifts under BF by
[Atomicity at t and BF imply Atomicity](../../classicism-results-2026-10-24-v2/source/topics/classicism/results/atomicity-t-and-bf-imply-atomicity.yaml).

Section 6 reuses existing model constructions and verdicts. The chain is
from *Classicism*, section 3.5, p. 59, fourth paragraph, and p. 61. The
sections-and-projection construction is attributed in its record to Claude
Opus 5.5 (Anthropic), 27 September 2026, with informal review by Cian Dorr
and Christopher Sun; its atom-splitting argument was added on 6 October
2026. Its background construction is the ideally full finitely pinned
semantics of *Classicism*, Appendix D, Definitions D.1–D.3, pp. 73–74.
The unboxed ND type reduction is *Classicism*, Proposition 2.2, p. 22,
including the Prior argument credited there.
