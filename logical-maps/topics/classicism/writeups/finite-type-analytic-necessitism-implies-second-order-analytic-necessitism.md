# Finite-type analytic powers give all finite relation arities

GPT-6 Astra, prompted by Daniel Kodsi, *Finite-Type Necessitism and Analytic
Non-Contingency*, §4, Theorem 8, using §2 and the companion
*Finite-type necessitism*, companion proof notes, 29 October 2026, §§4.0–4.5.

Fix a host \(\tau\), an external arity bound \(k\geq1\), and a possible
real structure at that host. The goal is the native SOAN instance: one
fixed necessarily-real structure at \(\tau\), with rigid necessarily-full
carriers of relations of each arity \(1,\ldots,k\) on its real carrier.

## Finite descent

For a persistent carrier \(Y\), rigidity of \(\mathsf P(Y)\) implies
rigidity of \(Y\). Each current member's singleton is a rigid necessarily
supported property of \(Y\); the union of \(\mathsf P(Y)\) is therefore
necessarily coextensive with \(Y\). That union is rigid, so C identifies
it with \(Y\).

Likewise, a full represented power above \(\mathsf P(Y)\) supplies the
full represented power of \(Y\). To see the fullness step explicitly,
given an arbitrary predicate \(F\) on \(Y\), apply upper fullness to
the property of being the singleton of an \(F\)-member of \(Y\).
Its rigid representative is a family of exactly those singletons at
the current point. Inextensibility propagates the singleton condition:
being a singleton of a member of persistent \(Y\) persists. The rigid
union is therefore a rigid subproperty of \(Y\) agreeing with \(F\).
This works at every possibility because the upper fullness is necessary
and the support and rigidity hypotheses have necessary versions.

Every canonical power is persistent in C. A real carrier returned by FTAN
is already fixed. Thus an FTAN instance at a sufficiently high finite
height supplies all preceding fixed, full powers of that **same** carrier.
Necessary distinctness propagates upwards by a point of disagreement
between distinct rigid supported properties.

## Encoding the required tuples

Write the returned real carrier as \(X\). The singleton term embeds a
fixed carrier into its canonical power. Finite unions of rigid properties
are rigid. Hence the Kuratowski code
\(\langle a,b\rangle=\{\{a\},\{a,b\}\}\) lies two power stages
above a common carrier and is necessarily injective there. The ordinary
pair-identity calculation is legitimate for these intensions: the finite
sets are rigid, and current coextension of rigid properties gives literal
identity. It does not assume global extensionality.

For arity \(j\leq k\), use a fixed external nested-pair bracketing.
When arguments are at different intermediate levels, iterate singleton
embeddings to raise them to a common level before forming the next pair.
This gives a term-defined injective code \(c_j(\bar x)\) at some finite
power level \(L_j\). For \(j=1\), the identity code suffices. The finite
construction depends only on \(j\), so choose the FTAN height in advance
large enough to include every \(L_j\) and its next power.

The graph of \(c_j\) is persistent and necessarily supported, total and
functional on the fixed product \(X^j\). The graph lemma in
[[finite-type-necessitism-and-analytic-necessitism-imply-finite-type-analytic-necessitism]]
makes it rigid. Its image \(K_j\) is a fixed subcarrier of \(L_j\).

Restrict the full power of \(L_j\) to \(K_j\). More explicitly, within
that power take the properties supported on \(K_j\). Current support
is equivalent to necessary support for these rigid properties, by
persistence of \(K_j\) and their inextensibility. The support condition
is stable over the fixed carrier with rigid incidence, so this is the
rigid canonical power \(\mathsf P(K_j)\). Restricting an arbitrary test
predicate to \(K_j\) and applying fullness over \(L_j\) proves its
necessary fullness.

Pull each member \(A\) of this power back to the ORIGINAL argument type:

\[
R_A(\bar x):=X^j\bar x\land A(c_j(\bar x)).
\]

The graph of this transformation is a rigid necessary bijection between
the rigid supported unary properties on \(K_j\) and the rigid supported
\(j\)-ary relations on \(X\). Its inverse is pushforward along the
coding bijection. The range of the rigid input carrier is therefore a
rigid carrier \(Q_j\) of such relations. To represent an arbitrary
admitted \(j\)-ary relation, push it to a predicate on the codes, use
fullness of \(\mathsf P(K_j)\), and pull back. All steps hold necessarily.
Thus \(\operatorname{RepPower}_j(Q_j,X)\).

There are only finitely many required \(Q_j\). Finite existential
elimination assembles them for the one returned real structure; no Choice
schema or infinite collection is used. The result is precisely SOAN at
host \(\tau\) and bound \(k\). The host of the real field never changes;
only the auxiliary code carriers use higher types.

The existing SOAN results already yield Analytic Necessitism, Necessity
of Second-Order Analysis and Non-contingency of CH. No extra direct arrows
or assertion deciding CH are required. The implication is strict: [[full-present-continuum-closed-henkin]] satisfies SOAN
but fails FTAN at host \(et\), height 1. Its first real power contains
all unary subsets; the failed clause represents subsets of that first power
in the next power. See [[henkin-finite-type-powers]] for the all-candidate-field
cardinality argument.
