# Boxed Rigid Comprehension and current Rigid Power give Finite-Type Necessitism

OpenAI Codex, prompted by Daniel Kodsi, 29 October 2026. This is the finite-generator argument of
*Simple generators for finite-type mathematical non-contingency*, §§1–3,
using the definitions and rigidity lemmas of GPT-6 Astra, prompted by Daniel
Kodsi, *Finite-Type Necessitism and Analytic Non-Contingency*, §§2–3.

## Statement and definitions

In C, assume boxed Rigid Comprehension and **current** Rigid Power. For every
source type \(\sigma\) and externally specified finite \(n\geq0\), we prove

\[
\Box I^*_\sigma\ \to\
\operatorname{RepPower}_1(H_{\sigma,n+1},H_{\sigma,n}).
\]

Here \(H_{\sigma,0}=\mathbb N_\sigma\), the canonical Frege-number carrier,
and \(H_{\sigma,i+1}=\mathsf P(H_{\sigma,i})\), where
\(\mathsf P(X)=\lambda A\, .\,\operatorname{Rigid}(A)\land A\leq X\).
The order means necessary inclusion. Rigidity has its two leading boxes.
A carrier is *fixed* when it is rigid and its current members are necessarily
distinct. Necessary fullness of a power means

\[
\Box\forall F\exists A\in\mathsf P(X)\,
   \forall x\in X\,(Fx\leftrightarrow Ax).
\tag{1}
\]

The type of \(\mathsf P(X)\) is the next native predicate type. We do not
require all levels to lie in a common host.

## Fullness and iteration

First let \(X\) be rigid. At the current point, apply Rigid Comprehension
to \(\lambda x\,(Xx\land Fx)\). Its rigid representative \(A\) is currently
included in \(X\). Persistence of \(X\) makes every current member of \(A\)
necessarily belong to \(X\); inextensibility of \(A\) therefore gives
\(A\leq X\). Thus \(A\in\mathsf P(X)\) and represents the prescribed
predicate on \(X\).

This proves in C the conditional from current RC and rigidity of \(X\)
to current fullness. Necessitate that **theorem**, then use boxed RC and
\(\operatorname{Rigid}(X)\to\Box\operatorname{Rigid}(X)\), which follows
from the leading boxes and 4. This gives (1). No choice of a representative
uniformly across possibilities has been made.

Now assume the displayed guard \(\Box I^*_\sigma\). The existing theorem
[[necessary-rigid-comprehension-implies-arithmetic-necessitism]] says exactly
that \(H_{\sigma,0}\) is fixed. Its rigidity argument uses RC at each
possibility to represent the least number carrier: canonical numberhood is
persistent, the representative contains zero and is successor-closed
necessarily, and leastness identifies it with numberhood. Its ND conclusion
uses the necessary Peano guard.

Suppose \(H_{\sigma,i}\) is fixed. Current Rigid Power makes
\(H_{\sigma,i+1}\) rigid; (1) makes it necessarily full. Its members are
necessarily distinct as well. Indeed, two distinct rigid properties
\(A,B\leq H_{\sigma,i}\) cannot be currently coextensive: persistence of
either and inextensibility of the other would give mutual necessary
inclusion and hence identity. Choose a current point of disagreement \(x\).
Its membership in one property persists. Every current member of the other
is necessarily different from \(x\), by ND of the fixed base;
inextensibility of that property therefore gives its necessary absence at
\(x\). Thus the two properties remain distinct.

External induction now supplies every required finite level and (1) at
each step. Rigidity plus (1) is exactly the canonical represented-power
clause, proving FTN. Each use of RP is current. No optional RP premise is
necessitated, and no infinite sequence of witnesses is collected.

## Scope

Boxed RC is used to obtain fullness at every possibility. Current RC alone
supplies only the current fullness established in the first paragraph.
The necessary arithmetic guard is retained in every instance. Consequently
this result asserts no unconditional arithmetic existence, no cumulative
hierarchy and no same-host finite coding theorem. Boxed Plenitude already
implies both premises through existing results, so its FTN consequence
requires no additional edge.
