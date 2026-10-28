# Strong Possibility excludes every strong world

Ordinary mathematical proof, reviewed for integration on 28 October 2026.
The new argument is due to OpenAI Codex, prompted by Daniel Kodsi, *Strong Possibility: density,
universal theory, and algebraic embeddings*, §3, and *Strong Possibility:
products, reduced products, and minimal identity algebras*, §5, both
22 October 2026, unpaginated. It uses the already recorded atomless
Maximalist model identified below. No human or Lean certification is claimed.

## Statement and scope

Over the fixed C, pure Strong Possibility implies, at every relational type
\(\tau\),
\[
  \forall w^\tau\,\neg\operatorname{SWorld}_\tau(w),\qquad
  \operatorname{SWorld}_\tau(w):=
  w\ne0_\tau\land\Box\forall Y^\tau
        (w\le Y\lor w\le\neg Y).
\]
Consequently Strong Possibility and Strong Actuality are incompatible.
This excludes arbitrary current strong-world entities, not merely pure-named
ones. It does not exclude weak atoms or Actuality, and does not settle the
consistency of Strong Possibility. No BF or optional extensionality is used.

## 1. Universal identity reflection

Write \(D=\Diamond_{\ne}\) and
\(H p=\exists q(q\land\Box(\Diamond q\to p))\), so \(D p=\neg H\neg p\).
If \(U=\forall\bar x\,\theta(\bar x)\), where \(\theta\) is a finite Boolean
combination of identities between typed terms, then C proves
\[
                         D U\longrightarrow U.                 \tag{1}
\]
Terms may themselves contain abstractions and quantifiers; it is the outer
Boolean matrix that has finitely many identity atoms.

For a current counterexample tuple to \(U\), let \(q\) be the conjunction
of its currently false identity atoms' negations (or Top if there are none).
Thus \(q\) is true. The currently true identity atoms are necessary by NI.
Wherever \(\Diamond q\) holds, none of the false identity atoms can be true:
NI at that point would make that identity necessary and exclude every
further \(q\)-point. Thus the same finite Boolean pattern, and the same
counterexample tuple, persists wherever \(\Diamond q\) holds. Hence
\(\Box(\Diamond q\to\neg U)\). This true \(q\) witnesses \(H\neg U\),
proving (1) by contraposition. No quantifier collection or BF occurs.

## 2. One admissible Strong Possibility instance

Put \(D_t(w)=\forall p(w\le p\lor w\le\neg p)\), and consider
\[
                  U_t:=\forall w\,[w=0\lor D_t(w)\ne\top].       \tag{2}
\]
This is a closed pure universal Boolean identity sentence. Since
\(\Box A\) is \(A=\top\), (2) says exactly that there is no strong
propositional world.

The recorded model
[coalesced-pinned-substitutions-root](coalesced-pinned-substitutions-root.html)
has pure Maximalism and propositional Atomlessness: use its `maximalism`
and `atomlessness` arguments and pass from the stated signature theory to
its pure reduct. Every strong world is a weak atom by T. Thus that recorded
model witnesses consistency of \(\operatorname{Max}(C)+U_t\).
The precise side condition for the pure Strong Possibility schema is
therefore met: it supplies \(D U_t\), and (1) supplies \(U_t\).

This use of the existing model does not upgrade its verification status.
Its construction is attributed to Cian Dorr, with a verification by Claude
Opus 5.5 dated 19 October 2026; its record expressly notes the lack of a
second-reader check of C-soundness. The present argument is conditional on
that recorded proved construction in exactly the ordinary manner of using
a database lemma, and introduces no new model verdict.

## 3. The same instance excludes every relational strong world

For \(\tau=\sigma_1\cdots\sigma_k t\), define admitted terms
\[
 \pi(W)=\exists x_1\cdots x_k\,W[\bar x],\qquad
 K(p)=\lambda\bar x.p.
\]
The empty tuple gives identity maps. The H-equivalence inside the following
boxes, together with C's relational order identities, gives the unconditional
C theorem
\[
 W\le K(p)\quad\longleftrightarrow\quad\pi(W)\le p.              \tag{3}
\]
In particular \(W=0_\tau\) iff \(\pi(W)=0_t\). The universal closure of
(3) may be necessitated because it is a theorem of C, not an optional
hypothesis.

If \(W\) is a strong world, instantiate its necessarily quantified decision
law at \(K(p)\), at each accessible point. Since
\(\neg K(p)=K(\neg p)\), (3) gives
\(\Box\forall p(\pi(W)\le p\lor\pi(W)\le\neg p)\).
Its nonzeroness follows from the zero equivalence. Thus \(\pi(W)\) is a
strong propositional world, contrary to (2).

A Strong Actuality witness is true, hence nonzero, and satisfies this same
boxed decision law. The displayed incompatibility follows. No boxed
Strong Possibility or boxed incompatibility is asserted here.
