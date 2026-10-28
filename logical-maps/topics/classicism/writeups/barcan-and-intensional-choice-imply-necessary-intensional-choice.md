# Barcan persistence of Intensional Choice

In C, at every fixed admitted type \(\sigma\),
\[
BF_{\sigma t}+IC_\sigma\ \Longrightarrow\ \Box IC_\sigma.
\]
Only the indicated predicate-type Barcan instance is needed. Neither ND
nor a necessary Barcan premise is assumed.

## 1. Put the witness entirely inside positive modal tests

Let \(I(F):=\exists xFx\) and \(U(F):=\exists!xFx\). Intensional Choice
is equivalent over C to
\[
\forall F^{\sigma t}\exists G^{\sigma t}
 \bigl[G\le F\land\Box(I(F)\to U(G))\bigr]. \tag{1}
\]
The reverse implication follows by K when \(I(F)\) is necessary. For
the forward direction, totalize \(F\) by
\(F'(x):=Fx\lor\neg I(F)\). Inhabitation of \(\sigma\) makes \(I(F')\)
an unconditional H theorem, hence necessary. IC supplies \(H\le F'\)
with \(\Box U(H)\). Take \(G(x):=Hx\land Fx\). Necessarily, wherever
\(I(F)\) holds, \(F'\) and \(F\) have the same extension and \(G\)
has the unique instance of \(H\). This proves (1); its bound \(G\le F\)
is an unconditional Boolean identity.

## 2. Persist the witness, then collect the inputs

C proves the positive-witness law
\[
\exists y\Box B(x,y)\ \longrightarrow\
\Box\exists y\Box B(x,y). \tag{2}
\]
For a current witness, use 4, then necessitated existential introduction;
ordinary existential elimination discharges the witness. No BF is used
in (2).

In (1), \(G\le F\) is \(\Box\forall x(Gx\to Fx)\). Thus its matrix is
a conjunction of boxed propositions, and (2) makes the existential
\(G\)-claim necessary for each current \(F\). The single instance
\(BF_{\sigma t}\) collects those necessities over \(F\), giving the box
of (1). The C equivalence in §1 and its legitimate necessitation then
give \(\Box IC_\sigma\). T gives the converse.

This proof does not give persistence of the negation of IC. It does not
replace \(BF_{\sigma t}\) by individual-type Barcan.

## Sources and review

Direct source: OpenAI Codex, prompted by Daniel Kodsi, *Barcan persistence of modal choice*,
26 October 2026, §§1–3, unpaginated; simplified 28 October 2026.
The starting IC formulation is Bacon's, as recorded in the native
[principle](https://github.com/zwlgzwlg/Logical-Maps/blob/6f15ef5c491fcb117d4d11d8837545a9baaa042d/logical-maps/topics/classicism/principles/intensional-choice-r.yaml).
The new contribution is the positive entailing form and its use to remove
ND from positive persistence. Ordinary AI review only; no Lean claim.
