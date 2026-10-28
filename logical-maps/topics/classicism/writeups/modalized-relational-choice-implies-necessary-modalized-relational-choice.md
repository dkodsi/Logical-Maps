# One universal modal selector makes Modalized Choice necessary

Over C, full Modalized Relational Choice (MRC) is equivalent to its
separately necessary version. More sharply, for any admitted output type
\(\tau\), including \(e\),
\[
MRC_{\tau t,\tau}\ \Longrightarrow\
\Box MRC_{\sigma,\tau}\land\Box RC_{\sigma,\tau}\land\Box IC_\tau
\tag{1}
\]
for every fixed admitted input type \(\sigma\). The change of input type
in the premise is essential to the statement; no BF is assumed.

## 1. Choose once from the universal membership relation

Define
\[
U(F,y):=Fy\lor\neg\exists z^\tau Fz.
\]
The type is \((\tau t)\tau t\). Inhabitation makes
\(\forall F\exists yU(F,y)\) an unconditional H theorem. Apply the
given MRC instance to its necessitation. Obtain one admitted \(S\) with
\[
\Box\operatorname{Functional}(S),\qquad S\le U. \tag{2}
\]
At every accessible evaluation, \(S\) chooses exactly one object from
each inhabited property; its output for an empty property is arbitrary.

## 2. Refine every relation with the same selector

For any \(R^{\sigma\tau t}\), define an admitted relation
\[
(T_S(R)x)y:=(Rx)y\land(S(\lambda z^\tau.(Rx)z))y. \tag{3}
\]
Its output is relational even when \(\tau=e\). The bound
\(T_S(R)\le R\) is unconditional. At each accessible evaluation (2)
makes every inhabited row of \(R\) have exactly one \(T_S(R)\)-output.
This holds for all relations and inputs available there, including ones
not available at the original evaluation: their row abstractions are
formed there and (2) already quantifies over all its property inputs.

Consequently, at any such evaluation, if \(R\) is necessarily serial
from there onward, (3) is necessarily functional from there onward and
entails \(R\). It witnesses MRC there. The original witness \(S\) remains
available by C's converse-Barcan direction, and its boxed laws persist by
4. Equivalently, necessitate the unconditional row-refinement implication
and use K on (2). No current universal statement has been moved through a
box by an unstated BF premise. This proves \(\Box MRC_{\sigma,\tau}\).

The existing unconditional MRC-to-RC implication then gives
\(\Box RC_{\sigma,\tau}\). Directly, for a property \(F\) use
\(G_F(y):=Fy\land(SF)y\). Whenever \(F\) is necessarily inhabited,
this is necessarily uniquely instantiated and entails \(F\). The same
argument at all accessible evaluations gives \(\Box IC_\tau\).

## 3. Full-schema consequences without extra records

Full MRC contains the required membership instance at every \(\tau\).
Therefore
\[
MRC\ \longleftrightarrow\ \Box MRC
\ \longleftrightarrow\ (\Box RC+IC)
\ \longleftrightarrow\ (\Box RC+\Box IC).
\]
The reverse directions use T and Cian Dorr's existing
[chooser-of-graphs theorem](necessary-relational-choice-and-intensional-choice-imply-modalized-relational-choice.html).
The native boxed-MRC consequences already record the other forward arrows;
only MRC-to-boxed-MRC needs a new edge. This does not assert RC-to-TC,
RC+IC-to-MRC, or necessity of an isolated MRC instance from itself.

## Sources and review

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Universal modal selectors and persistence
of MRC*, 26 October 2026, §§1–5, unpaginated; simplified 28 October 2026.
The MRC definition and its entailing form are Cian Dorr's, 11 October
2026, as is the separately cited chooser-of-graphs converse. The universal
membership selector and its cross-instance persistence are the new proof.
Ordinary AI mathematical review only; no Lean or human certification.
