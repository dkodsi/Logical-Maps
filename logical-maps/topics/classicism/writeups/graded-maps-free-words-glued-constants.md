# Graded maps with free words and glued constants

For every set-sized signature $\Sigma$ there is a C action model of Logical Necessity,
necessary Strong Actuality, necessary Self-Atomicity at every relational type, and
the necessary Barcan Formula at every type, in which propositional Boolean
Completeness fails. Thus even their conjunction allows an admitted family of
propositions without a least upper bound. A single propositional constant and a
countable alphabet suffice for a nonempty example of the scheme.

## The action model

Let $\kappa=\max(\aleph_0,|\Sigma|)$ and let $A$ be the initial ordinal of
cardinality $\kappa^+$. There is one object with individual domain $A$. An arrow
is a triple $(f,n,w)$, where $w$ is a finite word on an alphabet of size
$\kappa$, $n$ is a natural number, and $f:A\to A$. At grade $n=0$ require
$f=\mathrm{id}_A$. At every positive grade allow all maps. Words are arbitrary
at every grade. Write $\epsilon$ for the empty word. Composition and identity are
\[
 (g,m,v)(f,n,w)=(g\circ f,m+n,vw),\qquad
 1=(\mathrm{id}_A,0,\epsilon).
\]
Individuals travel by $f$. Recursively, an entity $X$ of type
$\alpha_1\ldots\alpha_k t$ assigns to every arrow $h$ a subset $X_h$ of the
current product $D_{\alpha_1}\times\cdots\times D_{\alpha_k}$. For $k=0$ the
product has one member, so each row is a truth value. There must be a single
$S\subset A$ of size at most $\kappa$ such that at any fixed grade and word,
maps agreeing on $S$ give the same row. Call $S$ a pin. Define transport by
$(hX)_u=X_{uh}$. If $S$ pins $X$, then $f[S]$ pins $(f,n,w)X$.
Also, arrows with the same grade and word whose maps agree on $S$ transport
the *whole entity* $X$ equally, as may be seen by following both by any continuation.
An individual has its singleton for a pin in this latter sense.

For a lambda term with parameters, take the union of the parameters' pins.
Arrows agreeing there at a fixed grade and word give the same transported
parameters. The body is therefore evaluated at the same object with the same
parameters for each possible argument tuple. This proves admission of the
lambda profile, including for quantified and modal bodies. Application uses
the identity row, and entity equality is equality of all continuation rows on
all target tuples. This gives the action semantics of C. Order between two
relations is inclusion of every row. Every external subset of the current
tuple product occurs as an identity row, for example by putting that same
subset at every arrow. Every closed pure sentence true at the one object
holds necessarily.

## Self-atoms and a true strong atom

Given $X\ne\bot$ of any relational type, choose an arrow $(f,n,w)$ and a tuple
$b\in X_{f,n,w}$. Intersect each row with $\{b\}$ at grade $n$ and word $w$,
and put the empty row at every other grade or word. The resulting $Q$ has the
same pin as $X$, is nonzero, and satisfies $Q\le X$. Whenever an arrow $h$
instantiates $Q$, its grade is $n$ and its word is $w$. A continuation $u$
for which $uh$ still has grade $n$ and word $w$ must have grade zero and the
empty word. The sole such arrow is the identity. Consequently $hQ$ has
exactly one tuple in its identity row and is empty elsewhere. Every entity
below it is bottom or equals it, so $hQ$ is an atom. This is Self-Atomicity;
the same argument applies to the empty tuple at type $t$. It holds necessarily.

The proposition true precisely at $1$ is admitted with empty pin and is a
true atom. After every nonidentity arrow it becomes bottom, since there is
no continuation returning that arrow to $1$. At every arrow it therefore
entails each proposition or its complement. This supplies a true strong
atom at the sole object and gives necessary Strong Actuality.

## The Barcan Formula

First take $h=(s,n,w)$ with $s$ surjective. Every typed entity at its target
lifts along $h$. At $e$ this is surjectivity of $s$. At a relational type let
$T$ pin a target entity $B$. Choose a preimage of each element of $T$ and let
$T'$ consist of the chosen preimages. Prescribe a source profile $L$ by
\[
 L_{g s,m+n,vw}=B_{g,m,v}
\]
for every allowed continuation $(g,m,v)$. At each grade and word extend a
prescription to all maps agreeing with its index map on $T'$. Fill all
remaining cases with empty rows. Two prescriptions at the same grade and word
have the same $m$ and $v$, by cancellation. Agreement on $T'$ of their
composite maps implies agreement on $T$ of the postmaps, so their prescribed
rows coincide. This defines an admitted $L$ with pin $T'$ and $hL=B$.

Now suppose a property $R$ has a possible witness $b$ at $(f,n,w)$. Take a pin
$S$ for $R$. At grade zero $f$ is already the identity. At a positive grade
choose a surjection $s$ agreeing with $f$ on $S$, using the $\kappa^+$ remaining
inputs. The row of $R$ is identical at $(s,n,w)$. Lift $b$ along this arrow
to an actual witness $a$. It follows that
$\Diamond\exists x\,R(x)\to\exists x\,\Diamond R(x)$, the dual of Barcan.
Lambda abstraction permits arbitrary matrices and the proof applies at
every type. The one-object pure reduct therefore satisfies necessary Barcan.

## Logical Necessity

We adapt the [simultaneous gluing construction](symmetric-surjection-products.html).
In the fixed pure model, call a $\Sigma$-sentence realizable when it is true
under some assignment to its constants. Choose one such assignment $J_i$ and
one distinct letter $i$ for every realizable sentence. There are at most
$\kappa$ sentences. Interpret the individual constants initially by distinct
values $a_c$. For each $i$ choose a surjection $s_i:A\to A$ with
$s_i(a_c)=J_i(c)$ for every individual constant, using the remaining
$\kappa^+$ inputs for surjectivity.

For a relational constant $c$ lift $J_i(c)$ along $(s_i,1,\epsilon)$ to a
profile $L_{i,c}$ by the preceding argument. On $(f,n,vi)$ assign $c$ the
row $(L_{i,c})_{f,n,v}$, using empty rows on the empty word and on unused
last letters. The union of the at most $\kappa$ pins of these lifts still has
size at most $\kappa$. Along $(s_i,1,i)$ every constant takes its prescribed
value, as can be checked for relational constants after each further
continuation. Consequently every realizable sentence is possible under the
glued interpretation. Conversely, any assignment produced along an arrow
is already an assignment at the sole object. Applying this to a pure matrix
with its free variables replaced by distinct matching names, and taking the
classical dual, gives
$\Box P[\bar c]\leftrightarrow\forall\bar x\,P[\bar x]$, including the
empty tuple. Logical Necessity is asserted at the designated identity.

## An admitted family without a join

Fix $d,b\in A$, distinct $a_i\in A\setminus\{d\}$, and distinct $c_i\in A$,
for $i<\kappa^+$. Let $p_i$ hold precisely at grade-one, empty-word arrows
whose maps satisfy $f(d)=c_i$ and $f(a_i)=b$. It is pinned by $\{d,a_i\}$.
Use the external set $\{p_i:i<\kappa^+\}$ as an identity row of an admitted
property of propositions. Thus the native Boolean Completeness principle
requires a least upper bound of this family in the admitted proposition algebra.

Suppose $L$ were such a bound with pin $S$. Choose $j$ with $a_j\notin S$.
Take two maps $f,f'$ agreeing on $S\cup\{d\}$, with
$f(d)=f'(d)=c_j$, $f(a_j)=b$, and $f'(a_j)\ne b$. At grade one and word
$\epsilon$, the first arrow belongs to $p_j$ and must belong to $L$.
The second belongs to the admitted cylinder of maps at that grade and word
with $f(d)=c_j$ and $f(a_j)\ne b$. The cylinder is disjoint from every $p_i$,
so its complement is an upper bound. Leastness excludes the second arrow
from $L$, contradicting agreement on $S$. Propositional Boolean Completeness
therefore fails, and the closed pure failure repeats at the sole object.

The graded construction and its separation were developed by OpenAI Codex
(GPT-6), prompted by Daniel Kodsi, on 26 November 2026. Two additional
OpenAI Codex agents independently reviewed the argument.
