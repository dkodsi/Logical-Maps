# Rigid domains propagate positive modal witness laws

Over C,
\[
\operatorname{Rigid\ Rigidity}+\operatorname{Rigid\ Power}
\quad\Longrightarrow\quad\Box\operatorname{Rigid\ Power}.
\]

Fix a relational type \(\tau\). Write
\[
R(F):=\operatorname{Rigid}(F),\quad
Z(F):=\operatorname{Rigid}
 (\lambda X^\tau.\operatorname{Rigid}(X)\land X\le F).
\]
The premises say that \(R\) is rigid and that
\(\forall F(R(F)\to Z(F))\) currently holds. A rigidity assertion is
a conjunction of boxed conditions, so C proves \(Z(F)\to\Box Z(F)\)
by 4. Hence every current \(R\)-member necessarily satisfies \(Z\).
Weak inextensibility of \(R\) now gives
\[
R\le Z,\quad\text{that is}\quad
\Box\forall F(R(F)\to Z(F)).
\]
This is exactly necessary Rigid Power at \(\tau\).

The argument is an instance of a simple principle: a weakly inextensible
domain transfers a currently universal, persistent test to a necessary
universal test over that domain. It does not move an arbitrary current
universal quantifier through a box.

The existing theorem
[□BF + Rigid Power → Rigid Rigidity](necessary-barcan-and-rigid-power-imply-rigid-rigidity.html)
therefore gives □BF + Rigid Power → □Rigid Power by closure, with no new
edge. At a fixed \(\tau\), rigidity of \(\top_\tau\) is another
sufficient replacement for Rigid Rigidity: apply Rigid Power to
\(\top_\tau\), whose rigid-power property is exactly \(R\).
These statements retain their Rigid Power premise; they do not settle
Rigid Rigidity → Rigid Power.

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Recurrent finite-colour approximations*,
26 October 2026, §11, unpaginated; simplified 28 October 2026. The existing
□BF/Rigid Rigidity bridge keeps its original attribution. Ordinary
independent AI proof review only; no human or Lean certification.
