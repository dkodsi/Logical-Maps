# Atomicity and Rigid Comprehension imply Weakly Rigid Power

Original adaptation by Codex (OpenAI), prompted by Daniel Kodsi, 22 October
2026; written out for the database by Codex (OpenAI), prompted by Daniel
Kodsi, 23 October 2026. The direct source is the research note
[Modal principles in Maximalist Classicism, §16](../source/research/2026-10-22/notes/maximalism-modal.md),
unpaginated. It adapts the atom-pullback method in the existing
[Rigid Power proof](../source/topics/classicism/writeups/atomicity-and-rigid-comprehension-imply-rigid-power.md),
which uses Bacon's *Could the truths of mathematics have been different?*,
Appendix C.2, Lemma C.6, pp. 15–16 of the separately paginated appendix,
and Christopher Sun's coextensive-weak-rigidity lemma. The strengthening
proved here is not attributed to those sources.

## Statement and conventions

Fix a relational type $\tau=\bar\sigma t$, allowing the empty tuple and
therefore $\tau=t$. Over the fixed logic C,

$$
 \mathrm{RC}_{\tau}\ \land\ \mathrm{Atomicity}_{\tau t}
 \quad\Longrightarrow\quad \mathrm{WRP}_{\tau}.
$$

Both premises hold at the evaluation point. Here RC is Rigid
Comprehension, and WRP is the **W,W,W** principle: for every weakly rigid
$F^\tau$, the property

$$
 P_F:=\lambda Y^\tau\,.\,
       \mathrm{WeaklyRigid}(Y)\land Y\le F
$$

is weakly rigid. It has type $\tau t$. This implies the all-type result
recorded in the database. We do not assume BF, necessitate an optional
premise, or use RC at $\tau t$.

Write $\mathrm{WP}(A)$ and $\mathrm{WI}(A)$ for weak persistence and weak
inextensibility. In particular,

$$
 \mathrm{WI}(A)\ \equiv\
 \forall B\,.\,
  \bigl(\forall\bar x\,.\,A[\bar x]\to\Box B[\bar x]\bigr)
       \to A\le B.
$$

Entailment is necessary universal inclusion. C proves that weak rigidity
implies persistence: apply WI to $\lambda\bar x\,.\,\Box A[\bar x]$,
using WP and modal 4. Rigidity is necessary weak rigidity, and is itself
persistent. These are the conventions of the database's Background.

We use the following C lemma. If $A,B$ are weakly rigid and currently
coextensive, then every current $A$-tuple necessarily satisfies $B$, by
coextension and WP of $B$. WI of $A$ yields $A\le B$. Interchanging
$A,B$ gives $B\le A$, hence $A=B$ by antisymmetry of the relational
Boolean algebra. Thus RC at $\tau$ makes every current weakly rigid
$Y^\tau$ rigid: choose a rigid coextension and apply the lemma.

Fix a weakly rigid $F^\tau$ and abbreviate $P_F$ by $P$.

## 1. Weak persistence of the weak-power property

If $P(Y)$ currently holds, RC at $\tau$ and the preceding lemma make $Y$
rigid. Consequently $\Box\mathrm{WeaklyRigid}(Y)$ holds. Also,
$Y\le F$ persists, by NI (or the boxed form of entailment and 4).
Together these give $\Box P(Y)$.

This proves only the required current weak persistence of $P$. It does
not move the current universal quantifier over $Y$ through a box.

## 2. Pulling back a member selected by an atom

Let $W^{\tau t}$ be an atom with $W\le P$. We show that some current
$X^\tau$ satisfies

$$
 P(X)\qquad\text{and}\qquad
 \Box\forall Y^\tau\,.\,W(Y)\to Y=X.                 \tag{1}
$$

RC at $\tau$ supplies a rigid $X$ currently coextensive with

$$
 Q:=\lambda\bar x\,.\,
 F[\bar x]\land
 \Box\forall Y^\tau\,.\,W(Y)\to Y[\bar x].
$$

First, every current $X$-tuple belongs to $F$ and hence necessarily
belongs to $F$, since $F$ is persistent. WI of $X$, tested against $F$,
gives $X\le F$. As $X$ is rigid, this proves $P(X)$.

Second, each current $X$-tuple necessarily satisfies
$\forall Y\,.\,W(Y)\to Y[\bar x]$. WI of $X$, tested against this
relation on tuples, gives

$$
 \Box\forall Y\,.\,W(Y)\to
           \forall\bar x\,.\,X[\bar x]\to Y[\bar x]. \tag{2}
$$

The quantifiers have only been rearranged inside the same box.

For the reverse inclusion, fix a current $F$-tuple $\bar x$.
If $X[\bar x]$, persistence of $X$ gives $\Box X[\bar x]$.
If $\neg X[\bar x]$, coextension with $Q$, together with
$F[\bar x]$, gives

$$
 \neg\Box\forall Y\,.\,W(Y)\to Y[\bar x],
 \quad\text{that is}\quad
 W\not\le\lambda Y\,.\,Y[\bar x].
$$

An atom lies below each element of its Boolean algebra or below its
complement. Hence in this second case
$W\le\lambda Y\,.\,\neg Y[\bar x]$. In either case,

$$
 \Box\forall Y\,.\,W(Y)\to
                  \bigl(Y[\bar x]\to X[\bar x]\bigr).
$$

Apply WI of $F$ to
$\lambda\bar x\,.\,\forall Y\,.\,W(Y)\to
(Y[\bar x]\to X[\bar x])$. This yields

$$
 \Box\forall\bar x\,.\,F[\bar x]\to
      \forall Y\,.\,W(Y)\to
                    \bigl(Y[\bar x]\to X[\bar x]\bigr).
$$

At a reached world, $W(Y)$ implies $Y\le F$, because $W\le P$.
By T, every $Y$-tuple there is an $F$-tuple. Thus

$$
 \Box\forall Y\,.\,W(Y)\to
           \forall\bar x\,.\,Y[\bar x]\to X[\bar x]. \tag{3}
$$

Now take any reached world and any $Y$ there with $W(Y)$.
It is weakly rigid **at that world**, directly from $W\le P$.
The chosen $X$ is rigid there, because its rigidity persists.
Equations (2) and (3) make them coextensive there, so the C lemma gives
$Y=X$. This establishes (1). No future RC instance or necessary
Atomicity was used. The argument works with weak rigidity of the
possibly new $Y$; this is the point that gives W,W,W.

## 3. Weak inextensibility of the weak-power property

Let $Z^{\tau t}$ satisfy

$$
 \forall Y^\tau\,.\,P(Y)\to\Box Z(Y).              \tag{4}
$$

Suppose $P\not\le Z$. Then
$P\land\neg Z:=\lambda Y\,.\,P(Y)\land\neg Z(Y)$ is nonbottom.
Atomicity at $\tau t$, at the evaluation point, supplies an atom
$W\le P\land\neg Z$. In particular $W\le P$, so (1) supplies a
current $X$ with $P(X)$ and necessary identity of every $W$-member
with $X$.

By (4), $\Box Z(X)$. But $W$ is nonbottom, so it is possibly
instantiated. At a world with a $W$-member $Y$, we have both $Y=X$
and $\neg Z(Y)$, contradicting $\Box Z(X)$. Therefore $P\le Z$.
This is WI of $P$. Section 1 gives WP of $P$, so $P$ is weakly
rigid, as required.

Every construction uses only the admitted relational types, and the
argument also covers the nullary case by the empty-tuple conventions.

## Scope and verification

The typed result uses RC only at $\tau$ and Atomicity only at $\tau t$.
It strengthens the W,R,W intermediate conclusion stated in the older
Rigid Power write-up without changing that write-up. The database's
all-schema WRP-to-RP implication additionally uses WRP, and hence Tame
Rigidity, at the higher type $\tau t$; this proof does not replace that
step by a same-type inference.

The submission's [catalog entry rigidity.02](../CATALOG.md#rigidity.02)
and corresponding entry in CATALOG.json record research checks for
RigidityClosureResearchAtomicPower, its certificate module, and
RigidityClosureResearchContinuationSchemas, under manifest
20261023T044252100669Z-9b8e2beb. These are separate research evidence.
No compiler was run for this registration, and the new database record
has lean: none until its own generated statement is audited.
