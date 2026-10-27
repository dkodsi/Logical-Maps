# An explicit analytical Choice separator

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. The statement and the exact scope

Write


$$
B_\infty=C+\Box\mathrm{Plenitude}+\mathrm{Infinity}_e+\mathrm{Infinity}_t,
\qquad
F_\infty=C+\Box\mathrm{FunctionalChoice}+\mathrm{Infinity}_e+\mathrm{Infinity}_t
$$


Both Infinity axioms are the quantified axioms. All types and lambda
abstractions remain in the fixed relational language of C. In this note,
analytical sentences are interpreted on the common Frege numerical core;
second-order variables mean its admitted subsets, with extensional membership
and coextensional equality. They do not mean arbitrary higher-order entities
with intensional equality.

Here is a concrete mathematical distinction:

> **Constructible countable collection.** For every real A, if every finite
> constructible aleph of L[A] is countable, then their limit is countable.

More explicitly, in set-theoretic notation this is


$$
\forall A\subseteq\omega\;
\left[
 (\forall n\in\omega\;\aleph_{n+1}^{L[A]}\text{ is countable})
 \longrightarrow
 \aleph_\omega^{L[A]}\text{ is countable}
\right]                                                     \tag{CCC}
$$


The analytical formulation below says that individually available countable
codes for the levels $L_{\aleph_{n+1}^{L[A]}}[A]$ can be collected into one
sequence. It is a single parameter-universally-closed instance of countable
Choice with a $\Pi^1_2$ matrix, hence also a $\Sigma^1_3$-Choice instance.
It has an explicit $\Pi^1_5$ presentation. Its fixed-parameter, including
parameter-free, version has a $\Sigma^1_4$ presentation.

**The separation.** F∞ proves the analytical sentence. A Feferman–Lévy ZF
model gives an internally full Gallin model of B∞ falsifying even its A=∅
instance. Thus, relative to the usual consistency hypothesis for that model,
B∞ does not prove it. This is a separation at the next universal projective
level, not a proof of an exact minimal complexity for the two typed theories.
Their Π¹₄ conservation theorem is proved separately in
[the conservation argument](analytical-choice-conservation.md); it is not inferred from
this separator.

## 2. A primary source actually displays the formula

[Victoria Gitman's KGRC lecture slides, 18 May 2017,
slide 8](https://victoriagitman.github.io/files/ACNotDCtalk3.pdf#page=8)
display the countable-Choice implication for codes of
$L_{\aleph_n^L}$, state that its row predicate is Π¹₂, and describe the
Feferman–Lévy model in which every finite $\aleph_n^L$ is countable but
$\aleph_\omega^L=\omega_1$. Slide 7 places this after the positive Σ¹₂-Choice
result for Z₂. This supplies the concrete formula omitted from
[Enayat's FOM post, 25 May 2015](https://fomarchive.ugent.be/2015-May/018739.html).

The shift from n to n+1 below only avoids small initial-level conventions.
Relativization to a real A and the detailed coding and typed transfer are
spelled out here. We are not attributing those expanded arguments to a
displayed proof in the slides.

The classical source is Azriel Lévy, *Definability in Axiomatic Set Theory II*,
in *Mathematical Logic and Foundations of Set Theory*, Studies in Logic and
Foundations of Mathematics 59 (1970), pp. 129–145,
[DOI 10.1016/S0049-237X(08)71935-9](https://doi.org/10.1016/S0049-237X(08)71935-9).
Theorem 8 is the cited original location. Its full text was not accessible
during this audit; the directly checked primary presentation is Gitman's
slide 8. Simpson's *Subsystems of Second Order Arithmetic*, Remark VII.6.3,
is the reference given by Enayat, not an independently inspected proof here.

## 3. An explicit Π¹₂ row predicate

Use a fixed recursive pairing of natural numbers. A real codes a countable
structure by coding its domain, binary relations, marked elements, and any
additional countable tables in separate columns. Finite tuples of reals and
natural numbers are coded by one real. This uses given codes, not Choice.

### 3.1 Hierarchy certificates

A **hierarchy certificate** X for A contains:

1. A countable linearly ordered set of stage indices, with first and last
   stages, intended to have order type α+1.
2. A common countable domain D, membership E, and nested stage domains D_i,
   with D equal to the last domain.
3. Satisfaction tables for all first-order formulas over each D_i, using E
   and the predicate A on the finite von Neumann ordinals.
4. The empty-level, successor-Def, and limit-union clauses: D_0 is empty;
   the members of the successor domain are exactly the subsets of the
   preceding domain defined by a formula with parameters; at a limit the
   domain is the union of the earlier domains. Membership and all copies of
   earlier elements agree. E is extensional.

The truth-table recursion, the successor clauses (in both directions), and
the union and coherence clauses are **arithmetical** conditions on X,A:
formula codes, parameters, stage indices, and domain elements are numbers.
Truth-table correctness includes quantification over the numbered domain
for the quantifier clause. The tables are witnesses inside X; we do not
assert a uniform arithmetical truth predicate for uncoded structures.

Add well-foundedness of the stage order. One may also require
well-foundedness of E, redundantly. For a coded relation R, use the Π¹₁
condition that every nonempty coded subset of its domain has an R-minimal
element. Thus there are explicit arithmetical predicates a and w such that


$$
\mathrm{HC}(A,X)\;\equiv\;
a(A,X)\ \land\ \forall U\,w(X,U)                            \tag{1}
$$


Well-founded recursion and extensionality show that a valid certificate
codes precisely the hierarchy through some $L_\alpha[A]$. Conversely,
if α is countable, so is $L_\alpha[A]$: its canonical L[A] well-order
gives cardinality at most $\max(\omega,|\alpha|^{L[A]})$. After choosing
one enumeration of this one set, all the displayed tables are definable
from it. This is a ZF argument; it does not choose countably many codes.

### 3.2 Test the cardinal height in every coded later level

A real Y used as a **test certificate** packages:

- another hierarchy certificate for A, of height β;
- an indicated initial segment and an isomorphism identifying X with its
  hierarchy through α;
- a marked ordinal c of the later membership structure representing α;
- enough later stages to contain α+ω.

All the compatibility checks, including the two displayed isomorphisms of
stage orders and membership domains, are arithmetical in A,X,Y. The only
nonarithmetical condition on a test is well-foundedness of its hierarchy.
Write its validity as


$$
t(A,X,Y)\ \land\ \forall V\,w_Y(V),                          \tag{2}
$$


where t includes the raw hierarchy conditions. Let g(n,Y) be the following
arithmetical condition on the coded later structure:

> c is its (n+1)-st infinite successor cardinal: the infinite cardinals
> at most c form a finite increasing list of length n+2, starting with ω
> and ending with c.

“Cardinal” here is the ordinary first-order condition that no smaller
ordinal has a bijection with the indicated ordinal; the coded membership
structure decides that condition by its supplied satisfaction table.
The finite list is coded by natural-number indices. No new set quantifier
is hidden in g.

Define


$$
R(n,A,X):\equiv\mathrm{HC}(A,X)\ \land\
\forall Y\Bigl[(t(A,X,Y)\land\forall V\,w_Y(V))\to g(n,Y)\Bigr]       \tag{3}
$$


Equivalently, R has the literal Π¹₂ form


$$
\forall(U,Y)\,\exists V\;
\underbrace{\bigl[
 a(A,X)\land w(X,U)\land
 (\neg t(A,X,Y)\lor\neg w_Y(V)\lor g(n,Y))
\bigr]}_{\theta(n,A,X,(U,Y),V)\text{ arithmetical}}           \tag{4}
$$


This equivalence uses only classical logic and finite tuple coding. In
particular it does not move an existential set quantifier through a
universal number quantifier.

### 3.3 Why the tests express the actual L[A]-cardinal, not a local imitation

For a valid X of height α, (3) holds exactly when


$$
\alpha=\aleph_{n+1}^{L[A]}                                  \tag{5}
$$


Here is the relevant correctness argument. In L[A], the usual condensation
bound puts a constructible bijection collapsing an ordinal γ below
$(|\gamma|^+)^{L[A]}$. This follows by taking the canonical elementary
hull containing γ+1 pointwise and the bijection as a parameter in a
sufficiently high constructible level, then collapsing it; the hull has L[A]-cardinality at most
$\max(\omega,|\gamma|^{L[A]})$. For a real A the hull fixes A once it
contains ω and A, so the relative condensation argument has the same bound.

If α is an infinite L[A]-cardinal, every noncardinal γ<α therefore has its
collapse witnessed already in $L_\alpha[A]$. Later levels cannot invent
a collapse of an actual cardinal. Consequently every valid later test
computes the infinite cardinals through α correctly. Its finite-cardinal
list condition is precisely (5).

If α is not an L[A]-cardinal, a collapse of α appears below
$\kappa^+$, where $\kappa=|\alpha|^{L[A]}$. Since α is countable in
the ambient ZF universe, κ<ω₁ there. That ω₁ is also a cardinal in L[A],
so $\kappa^+\le\omega_1$. Some **countable** later constructible level
therefore contains the collapse. Enlarging its height to include α+ω
still leaves it countable. It has a valid test certificate Y for which
g(n,Y) fails. Finite or insufficient heights fail the same test directly.

Thus quantification over countable test certificates detects the relevant
global constructible-cardinal facts. It does not require a code for the
whole constructible universe or a countable transitive model of ZF.

## 4. The sentence and its exact projective presentation

The promised analytical sentence is


$$
S\;:=\;\forall A\left[
 (\forall n\,\exists X\,R(n,A,X))
 \longrightarrow
 \exists F\,\forall n\,R(n,A,F_n)
\right],                                                     \tag{6}
$$


where $F_n=\{k:\langle n,k\rangle\in F\}$.
By §3, its set-theoretic interpretation is (CCC). For the reverse direction
from countability of the limit, one code for the whole countable level
$L_{\aleph_\omega^{L[A]}}[A]$ provides all its indicated initial-level
codes by restriction and least-index enumeration. No countable choices
are required after that one code is supplied.

Absorb the pair (U,Y) of (4) into one real and write
$R(n,A,X)=\forall Y\exists Z\theta(n,A,X,Y,Z)$.
For a fixed A, (6)'s implication is equivalent to


$$
\begin{split}
\exists b\in\{0,1\}\,\exists n\,\exists F\;
\forall X\,\forall m\,\forall Y\;
\exists U\,\exists Z\;\forall V\quad
\bigl[& (b=0\land\neg\theta(n,A,X,U,V))\\
 {}\lor{}& (b=1\land\theta(m,A,F_m,Y,Z))\bigr]               \tag{7}
\end{split}
$$


The b=0 branch asserts that some row has no witness. The b=1 branch gives
the collecting F. Unused witnesses can be the empty real. This direct
equivalence avoids the invalid normalization
$\forall n\exists X\leadsto\exists F\forall n$.

Encode (b,n,F) by H, (X,m,Y) by Q, and (U,Z) by K, using fixed total
arithmetical decoders onto these tuple spaces. For example, a natural
coordinate can be decoded as the first missing element of one column,
with default 0 if the column is full; a separate column carries each
real. The flag is one bit. Every intended tuple has such a code.
Equation (7), together with the outer parameter A, is then exactly


$$
\boxed{\quad \forall A\;\exists H\;\forall Q\;\exists K\;\forall V\;
             \Theta(A,H,Q,K,V)\quad}                         \tag{8}
$$


with Θ the arithmetical matrix displayed in (7), using the decoders.
This proves the Π¹₅ upper bound **without any countable-choice
normal-form assumption**. A=∅ gives a Σ¹₄ separator. No completeness or
least-possible complexity claim for these formulas is intended.

## 5. Proof in F∞

Fix A and suppose every numerical n has a predicate X satisfying R.
Let ν be the chosen Frege number type and N its numerical-domain predicate.
The translated relation on inputs z:ν and outputs X:νt is


$$
U(z,X):=(Nz\land R(z,A,X))\lor(\neg Nz\land X=\bot_{\nu t})
$$


It is serial. Functional Choice, obtained from its boxed instance by T,
gives f of type ν(νt) choosing an output for every input. This is an
admitted relational output type; no forbidden individual-valued function
type is introduced. Set


$$
F(\langle n,k\rangle)\quad\leftrightarrow\quad (f(n))(k)
\qquad(n,k\in N),
$$


using the established internal pairing operation and lambda comprehension.
Every section is coextensional with the chosen predicate on N. The
analytical formula R is invariant under that coextensional replacement.
Therefore $\forall n\,R(n,A,F_n)$. Generalize A.

The argument applies to every internal natural number, including in
nonstandard numerical cores. It is the usual derivation of the full
second-order countable-Choice scheme from Functional Choice; this one
explicit Π¹₂ row already suffices for the separation. We do not claim
that all the premises of F∞ are needed for this forward implication.

## 6. The B∞ countermodel and the preservation obligations

Use the classical Feferman–Lévy symmetric model M over L, obtained from the
finite-support product of the collapses $\mathrm{Coll}(\omega,
\aleph_n^L)$. The imported model theorem gives


$$
M\models\mathrm{ZF},\qquad
M\models\text{each }\aleph_n^L\text{ is countable},\qquad
M\models\aleph_\omega^L=\omega_1
$$


Hence every row R(n,∅,X) has a witness in M. If one real F collected the
witnesses, their stage-order columns would give a sequence of countable
well-orders reaching all the $\aleph_{n+1}^L$. Their ordinal sum is
itself a well-order of a subset of ω×ω and has order type at least
$\aleph_\omega^L$. Thus that ordinal would be countable in M, a
contradiction. This sum uses a sequence of codes **already supplied by F**;
it does not invoke a countable union theorem or dependent Choice.

Inside M construct the full Gallin hierarchy with individuals E=ω, worlds
W=ω, propositions $D_t=\mathcal P(W)^M$, and at each admitted function
type the full internal function set. Application and lambda abstraction
have their usual set-theoretic interpretation; truth at w is membership
of w. This construction validates the fixed C, including the theoremhood
restriction on Logical Equivalence.

At a world w, a total single-valued admitted relation has its unique-value
function by ZF Replacement. The full internal function domain contains
it. This proves Plenitude at every world and hence □Plenitude. No choice
of one member of a many-valued family has occurred. E is infinite, and
$n\mapsto\{n\}$ injects ω into D_t, giving both quantified Infinity
axioms (indeed their boxed versions).

The numerical bridge identifies the Frege core with $\omega^M$.
Pulling a current admitted predicate back along this bridge gives an
element of $\mathcal P(\omega)^M$. Conversely every internal subset of
ω has its admitted rigid characteristic predicate. Thus the current
second-order structure is exactly
$(\omega^M,\mathcal P(\omega)^M)$, up to extensional identification.
Induction on each standard finite analytical formula proves preservation
of truth, in particular of (6) and of its falsity at A=∅.

This is the choice-free part of the interpretation in
[Frege arithmetic, §36.4](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md).
The extra well-ordering used there to obtain Functional Choice is
deliberately absent here. Externally the resulting typed model is a
general/Henkin model, not necessarily a full-standard or ω-standard
model. That is sufficient for nonderivability from B∞. The usual
relative-consistency version can be read internally in a model of the
set-theoretic construction; an externally countable transitive ground
model is a convenient semantic illustration, not an added claimed
consistency strength.

## 7. What has and has not been completed

Completed here: a concrete classical separator; an explicit hierarchy-code
row and its Π¹₂ form; a Choice-free five-block presentation; the typed
F∞ proof; and the internal Gallin transfer of its Feferman–Lévy
counterexample. The mathematical content of the separator is classical,
not a newly discovered failure of Choice. Its explicit integration with
the two exact modal packages is the present contribution.

Still imported: the construction and ZF verification of the classical
Feferman–Lévy symmetric model, and the standard constructibility and
relative-condensation facts used in the coding verification. No formal
recursive bit-level implementation or Lean certification was performed.
Π¹₄ conservation for arbitrary B∞ Henkin models has its own preservation
argument in [the companion note](analytical-choice-conservation.md), independently
reviewed separately from this separator.
