# Free words over disagreeing arithmetics

Possibly Witnessed Possibility holds for every set-sized free signature in
a model where Necessity of Arithmetic fails at the individual type.
Necessary Strong Atomicity, necessary BF, necessary propositional Boolean
Completeness, necessary individual Infinity and Modal Well-Ordering hold
at the same root.

## The interpreting objects

Use the two-component method of Cian Dorr's
[coalesced arithmetics](coalesced-two-extensional-arithmetics-root.html),
with a free-word root as in the
[signature gluing construction](full-free-monoid-glued-constants.html).
Here every word has its own entrances to the two components. Work in ZFC.

The first terminal $S$ has the full ordinary type hierarchy on $\mathbb N$.
For the second, choose a countable model $M$ of Zermelo set theory with
Choice and $\neg\operatorname{Con}(\mathrm{ZC})$. Such a model exists:
$V_{\omega+\omega}$ models ZC, which is effectively axiomatized and
interprets arithmetic, so Gödel's second incompleteness theorem gives
consistency of $\mathrm{ZC}+\neg\operatorname{Con}(\mathrm{ZC})$.
Completeness and downward Löwenheim–Skolem give $M$. At the terminal
$H$ use the hierarchy on $\omega^M$ formed inside $M$, using its
products and powersets for every standard finite type. External
satisfaction of each fixed typed formula agrees with satisfaction in
this internal hierarchy by induction on the formula. Separation gives
comprehension. Each terminal has only its identity arrow.

At a third object $r$ take an infinite set $I$ of individuals, of
cardinality $\kappa\ge\max(\aleph_0,|\Sigma|)$. Fix surjections
$\pi_S:I\to\mathbb N$ and $\pi_H:I\to\omega^M$. For each
surjection $I\to I$ provide $\kappa$ distinguished letters carrying
that map. The endomorphisms of $r$ are all finite words in these letters,
and their individual maps $f_w$ are the composites in word order
with the later letter prepended. The two other kinds of arrows are
$h_{i,w}:r\to i$ for $i=S,H$, one for every word $w$. Their
compositions and individual maps are
$$h_{i,w}u=h_{i,wu},\qquad h_{i,w}(a)=\pi_i(f_w(a)).$$

At a relational type $\tau=\bar\sigma t$, a root entity consists of
an arbitrary row on $D_{r,\bar\sigma}$ for each word $w$, and a whole
entity of $D_{i,\tau}$ at each $h_{i,w}$. All coordinates are
independent. The current extension is the empty word's row.
Transport along $u$ reads rows and coordinates indexed by $wu$.
Transport to a terminal reads its specified coordinate. These
operations respect composition. A difference of source values is
observable at the differing word or terminal coordinate, using
one-world extensionality in each terminal. An abstract at a root word
takes its row from its body with the transported parameters and all
root arguments. At a terminal it takes the terminal denotation on the
transported parameters. All such root rows are admitted and terminal
term closure supplies all the required coordinates. Thus the
interpretation validates C.

## Realizing the signature

Give the individual names distinct values in $I$. A source requirement
is a pure matrix, a list of distinct matching names, and the fact that
some tuple realizes it at $r$. For each such requirement choose one
realizing tuple. A terminal requirement specifies the same information
with a witnessing tuple at one of $S,H$. There are at most $\kappa$
requirements in total.

Assign a fresh letter $\alpha$ to each requirement. For a source
requirement choose its underlying surjection so it takes each named
individual in the list to its witness. For a terminal requirement at
$i$ choose a preimage of each individual witness under $\pi_i$ and
require the surjection to take the named individuals to these preimages.
A finite prescription on distinct points extends to a surjection of
the infinite set $I$. The supply of letters permits the choices to be
pairwise distinct.

For a source requirement, each relevant relational name receives the
root rows at $w\alpha$ and both terminal coordinates at $h_{i,w\alpha}$
of its matching witness at $w$ and $h_{i,w}$, for every $w$. After
$\alpha$ the constant is exactly its witness as a whole typed entity.
For a terminal requirement, put the chosen terminal value of each
such name at the single coordinate $h_{i,\alpha}$. Different final
letters keep these prescriptions disjoint. Fill unassigned coordinates
with empty values.

Any possible witness to the pure matrix occurs at one of the three
objects and hence has one of these requirements. At its chosen
entrance or word the assigned names realize the matrix. This proves
[Possibly Witnessed Possibility](../principles/possibly-witnessed-possibility-r.html),
including ordinary Witnessed Possibility.

## Arithmetic and the other principles

At each terminal the finite cardinalities of individual properties are
the cardinalities indexed by its own natural numbers. For each internal
$n$ the cardinality exists by separation and is distinguished by a
set of size $n$. The property consisting of these cardinalities is
inductive and available in that hierarchy. Conversely internal
induction shows that each lies in every inductive property. The Frege
arithmetic operations therefore compute the terminal's ordinary
arithmetic, and $I_e^*$ holds. Thus the arithmetical sentence
$\operatorname{Con}(\mathrm{ZC})$ holds at $S$ and fails at $H$.
The two terminal witnesses refute both alternatives in the root's
[Necessity of Arithmetic](../principles/necessity-of-arithmetic.html)
instance.

At the root one can take a predicate of cardinalities with actual row
consisting exactly of the externally standard Frege numerals, since all
root rows are admitted. Its row contains zero and is closed under successor,
so every root finite cardinality equals a standard numeral. By external
finite induction the $n$th numeral holds of exactly those current properties
having $n$ instances. As $I$ is infinite, none counts the universal
property. The terminals satisfy the same axiom by their internal
arithmetic, yielding necessary Axiom of Infinity at $e$.

Every outgoing arrow is surjective on each type. A root-word map lifts a
higher-type target by writing its entire family on the corresponding
word suffix. A terminal entrance lifts a value by placing it in that
coordinate. Individuals have the stipulated surjective maps. This
gives necessary BF at every type.

The root proposition algebra is the full powerset of the collection of
root words and terminal entrances, since each terminal has just two
propositions. Both terminal algebras are complete. Thus necessary
Boolean Completeness holds at $t$. At any relational type a nonzero
root entity contains the single tuple at a single occupied word or
terminal coordinate. Even $H$ has these singleton predicates by
internal comprehension with parameters. A word shift has at most one
preimage of the chosen address by right cancellation. Therefore every
transport of a singleton of this kind is bottom or another single
tuple at one address; it decides every admitted tester. In both
terminals the same singleton argument is immediate. This proves
necessary Strong Atomicity at all relational types.

For each type put a fixed external well-order of its root domain in
every word row, an ordinary well-order in every $S$ coordinate, and an
internally chosen well-order in every $H$ coordinate. The resulting
relation is necessarily a well-order in the required internal sense.
This gives [Modal Well-Ordering](../principles/modal-well-ordering-r.html).

The free-word extension and its signature and model calculations are
by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 26 November 2026.
Two further GPT-6 research agents independently checked the arguments.
