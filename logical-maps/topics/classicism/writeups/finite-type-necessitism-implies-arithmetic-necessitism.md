# Finite-Type Necessitism gives Arithmetic Necessitism

GPT-6 Astra, prompted by Daniel Kodsi, *Finite-Type Necessitism and Analytic
Non-Contingency*, §3, Proposition 5. The rigid-union proof below is a
refinement by OpenAI Codex, prompted by Daniel Kodsi, 29 October 2026.

Fix a source type \(\sigma\) and assume exactly the guard of Arithmetic
Necessitism, \(\Box I^*_\sigma\). Write \(N=\mathbb N_\sigma\) and
\(P=\mathsf P(N)=\lambda A\,[\operatorname{Rigid}(A)\land A\leq N]\).
The height-zero FTN instance makes \(P\) rigid and gives

\[
\Box\forall F\exists A\in P\,\forall x\in N\,(Fx\leftrightarrow Ax).
\tag{1}
\]

Let \(U=\lambda x\,\exists A\,(PA\land Ax)\). A rigid family of rigid
properties has a rigid union. For persistence, preserve both witnesses and
membership. For inextensibility, if every current union member necessarily
satisfies \(Q\), inextensibility of each current \(A\in P\) gives
\(A\leq Q\). This condition is persistent, so inextensibility of \(P\)
propagates it to every possible member. Hence \(U\leq Q\). The hypotheses
have necessary versions, supplying the leading box of inextensibility.

Necessary support in the definition of \(P\) gives \(U\leq N\).
At every possibility, apply (1) to the always-true predicate: some member
of \(P\) contains every member of \(N\). Thus \(N\) and \(U\) are
necessarily coextensive. C identifies necessarily coextensive relations,
so \(N=U\) and \(N\) is rigid. This base-descent argument needs no
preliminary persistence assumption on its base.

Necessary distinctness of the canonical numbers follows from the retained
Peano guard. Induction compares numbers by their successor distance;
zero is never a successor, and injectivity of successor holds at every
possibility. Distinct canonical numerals therefore cannot merge. Equivalently,
use the necessary-distinctness part of the proof of
[[necessary-rigid-comprehension-implies-arithmetic-necessitism]], which uses
the guard alone: canonical sums and numberhood persist, and a nonzero
successor distance remains nonzero under the necessary Peano axioms.
That part does not use its RC premise.

We have obtained rigidity of \(N\) and necessary distinctness of its
members under precisely \(\Box I^*_\sigma\). Those are the two conclusions
of [[arithmetic-necessitism]]. Only the first represented power was needed;
no guard was removed and no arithmetic was asserted at an unactivated type.
