# Finite-Type Necessitism and Analytic Necessitism give finite-type analysis

OpenAI Codex, prompted by Daniel Kodsi, 29 October 2026. This strengthens the analytic bridge in GPT-6 Astra, prompted by
Daniel Kodsi, *Finite-Type Necessitism and Analytic Non-Contingency*, §4.
The fixed-carrier transport and cut constructions are from *Finite-type
necessitism*, companion proof notes, 29 October 2026, §§4,6–8.

## What must be preserved

Assume FTN and existing Analytic Necessitism (ANA). Fix an admitted host
\(\tau\), a finite height \(n\), and
\(\Diamond\exists\mathfrak R\,\operatorname{Real}_\tau(\mathfrak R)\).
ANA gives a particular structure \(\mathfrak R\), with carrier
\(X^{\tau t}\), such that

\[
\operatorname{RigidStr}(\mathfrak R)\land
\Box\operatorname{Real}_\tau(\mathfrak R).
\tag{1}
\]

We will add the required powers to **this carrier**. No real field is moved
to a more capacious host. All functions with individual values are expressed
as admitted relational graphs.

## Fixed carriers and power transport

Call a rigid carrier with necessarily distinct members fixed. The following
elementary facts explain the modal steps used below.

1. Currently coextensive rigid relations are identical. Persistence of one
   and inextensibility of the other give necessary inclusion in each
   direction. Necessary coextension identifies arbitrary relations in C as
   well, even before their rigidity is known.
2. Fixedness has a necessary version. Rigidity persists by 4. For ND,
   apply inextensibility of the rigid product of a carrier with itself;
   necessary identity handles equal pairs, and 4 handles the necessary
   inequality of unequal pairs. Finite products of rigid carriers are
   rigid by successive applications of inextensibility.
3. A rigid relation necessarily supported on a fixed product has stable
   positive and negative instances there. A positive instance persists.
   If the instance at \(a\) is false, every current related tuple is
   necessarily different from \(a\); inextensibility applied to the
   complement of its haecceity gives necessary falsity. Formula induction
   therefore works over fixed carriers with rigid, necessarily supported
   primitive relations. Restricted quantifiers use carrier inextensibility
   in the true universal case and persistent counterexamples in the false
   case. Stable definable subcarriers are rigid and inherit ND.
4. A persistent graph which is necessarily supported on, total on and
   functional over a rigid domain is rigid. If its current pairs
   necessarily satisfy \(Q\), take the unique image of each current
   input. Persistence and necessary functionality give
   \(\Box\forall y(Jxy\to Qxy)\) for that input. Inextensibility of
   the domain makes this true of every possible input. Necessary support
   excludes stray graph pairs. Necessitating this proved conditional,
   using the necessary hypotheses, supplies the leading box. Ranges of
   rigid graphs are rigid by pulling a test predicate back along the graph.

For a rigid necessary bijection \(J:A\cong B\) between fixed carriers,
define the pushforward of a rigid supported property by

\[
T_J(R)=\lambda b\,[Bb\land\exists a(Aa\land Jab\land Ra)].
\tag{2}
\]

The restriction of \(J\) to \(R\) is a persistent necessarily supported
functional graph, so (2) is its rigid range. Pullback along the inverse
shows that (2) is a necessary bijection between the canonical powers of
\(A\) and \(B\). Its graph is rigid by fact 4. If \(\mathsf P(A)\)
is rigid, its image under (2) is rigid and necessarily coextensive with
\(\mathsf P(B)\). Identify these carriers **before** inferring rigidity
of the latter. Fullness transfers by pulling back an arbitrary predicate,
representing it over \(A\), and pushing the representative forward.
This argument holds at every possibility and iterates at finite height.
It never assumes that an arbitrary intersection of rigid relations is rigid.

The same facts restrict a tower to a fixed subcarrier \(K\leq A\).
Inside a fixed full power of \(A\), the condition of having every member
in \(K\) is stable: use fixed \(A\), rigid incidence and rigid \(K\).
Its carrier is exactly \(\mathsf P(K)\), because current inclusion of
a rigid property in persistent \(K\) implies necessary inclusion.
Restrict any test predicate to \(K\) and use fullness over \(A\) to
obtain fullness over \(K\). Repeat at the next levels. Necessary
distinctness passes to rigid subproperties by a persistent point of
disagreement. Thus all these represented carriers are fixed.

## Activation of the canonical arithmetic

The included number carrier of (1) is fixed. Successor, given by adding
the distinguished one, is a persistent, necessarily supported functional
graph on it and hence rigid. The real-structure axioms say necessarily
that this is a Peano presentation \((K,z,S)\), with induction over all
admitted subproperties.

Here is an explicit reason this activates \(\Box I^*_\tau\), rather
than merely resembling an infinite carrier. At a current point extend
successor to the whole type by the admitted relation

\[
T(x,y)=(Kx\land Ky\land Sxy)\lor(\neg Kx\land y=x).
\tag{3}
\]

It is total and injective, and omits \(z\). The internal finite-cardinal
Dedekind lemma therefore shows that no finite Frege cardinality counts
the whole type. Its finite induction removes a point from a supposed
finite carrier, bypassing that point's predecessor when necessary; the
restricted or redirected graph would again inject the smaller carrier
properly into itself. The base case is empty. This argument is about
internal finite cardinalities and admitted graphs, not external standard
natural numbers.

Consequently every internal finite cardinality is realizable: zero is
realized by the empty property, and a finite realization cannot exhaust
the whole type, so adding one outsider realizes its successor. This is
induction proving existential witnesses, not selection of witnesses at
all numbers. If two canonical successors are identical, realize their
common cardinality. Removing their respective distinguished points gives
predecessor realizations; the definable transposition interchanging the
two points gives a common realization when they differ. The finite
cardinality Exclusivity lemma identifies the predecessors. This proves
successor injectivity; zero-not-successor is already a theorem of C.

These are the Dedekind, Swap and Exclusivity arguments in the existing
Frege proofs. Their composition proves
in C that a supplied Peano presentation at \(\tau\) implies
\(I^*_\tau\). Necessitate that closed conditional and use the boxed
Peano premise from (1), obtaining \(\Box I^*_\tau\). No optional
assumption has been necessitated and no existential has been moved across
a box.

## A reference continuum and its finite powers

The activated \(\tau\)-source instances of FTN now give as many fixed,
necessarily full canonical powers of \(N_\tau\) as the requested finite
height needs. The base is fixed by
[[finite-type-necessitism-implies-arithmetic-necessitism]].

Peano recursion supplies the arithmetic graphs on \(N_\tau\); their
least recursion graphs are persistent and necessarily total-functional,
so fact 4 makes them rigid. Use canonical number codes for rationals.
In the first power \(\mathsf P(N_\tau)\), take those represented
subsets of rational codes that are nonempty proper downward-closed cuts
with no greatest member. This is a fixed subcarrier \(X_0\), by stable
definition over the fixed arithmetic and its rigid incidence relation.
Cut order and arithmetic have rigid, necessarily supported graphs.

At every possibility, an arbitrary admitted nonempty bounded family of
cuts has the admitted union predicate on rational codes. Necessary
fullness of the first power supplies its representative. The ordinary
union-of-cuts argument gives the least upper bound, so the field is
necessarily complete. The image of the canonical numbers is its fixed
least inductive number carrier. This proves that the cut structure is
fixed and necessarily real. It does not require a selected representative
for every family simultaneously.

Restrict successive canonical full powers to \(X_0\) using the
restriction argument above. Thus this reference real carrier has the
required finite full tower.

The reference and (1) have a rigid necessary ordered-field isomorphism.
Match their Peano numbers, hence their rationals, and relate real elements
exactly when they determine the same rational cut. The Peano matching is
the least relation closed under the paired successors; the usual induction
proves it necessarily bijective. The cut matching is a stable definition
over fixed carriers and rigid arithmetic relations. Completeness and
ordered-field categoricity make it necessarily bijective. Its graph is
rigid by the facts above, with necessary support made explicit.

Transport the reference tower along this isomorphism and its successive
power bijections. We obtain on the **original** carrier \(X\)

\[
\operatorname{RepPower}_1(\mathsf P^{n+1}(X),\mathsf P^n(X)).
\]

Together with (1), this is the chosen FTAN instance. Each instance uses
finitely many FTN instances. The argument neither collects an infinite
hierarchy nor chooses a sequence of fields. It needs no separate
unconditional arithmetic premise: ANA's activated witness supplied the
necessary guard at exactly the required source.

The converse toward FTN requires a possible real structure at some
specified type; without activation FTAN may be vacuous. It is not an
unconditional reverse arrow. The support, guard and original-host restrictions remain as stated throughout.
