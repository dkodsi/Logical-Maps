# Symmetric integer stages of paired individuals

Necessary Boolean Completeness at every relational type is consistent with
a 5-necessary proposition that fails to be two-hat necessary. The same
example satisfies necessary Barcan at every type, necessary Atomlessness
and Logical Necessity for a purely relational signature. A second
proposition is two-hat necessary and fails distinctness-preserving necessity.

Use the stages, arrows and words of the [integer-stage model](integer-stages-paired-individuals-glued-constants.html).
The additional symmetry on admissible profiles makes the [Boolean join argument
for symmetric products](symmetric-surjection-products.html) applicable.

## The domains

The stages and coordinate labels are integers. In coordinate $i$, every stage
has $\aleph_1$ ordinary doublets; stage $n$ also has one singleton in that
coordinate if $i\le n$. Take the disjoint union of the coordinates as the
individual domain. Each arrow $(f,w):n\to m$ is a coordinate-preserving map
sending each block into a block, together with a finite word. Ordinary
doublets can collapse. Composition composes maps and prefixes words. Let
$G_m$ be the group of coordinate-preserving block automorphisms at $m$,
viewed as arrows with empty word. Its elements permute ordinary doublets,
can exchange the members of each, and fix the singletons.

At type $\alpha_1\ldots\alpha_d t$ an entity $X$ at $n$ assigns to
$(f,w):n\to m$ a subset $X_{f,w}$ of the product of the already constructed
argument domains at $m$. For $d=0$ it assigns a truth value. Require both
of the following.

- A single countable set of source individuals pins the rows: at fixed
  target and word, maps agreeing there have the same row.
- For each $\pi\in G_m$, $X_{\pi f,w}=\pi[X_{f,w}]$, with $\pi$ acting
  on the tuples by their typed transports.

Transport is precomposition. The image of a pin pins the transported
profile, and postcomposition preserves its symmetry. At the identity the
symmetry law makes each $\pi\in G_m$ an automorphism of the local typed
structure. For a lambda term, equal maps on the union of its parameter
pins at the same target and word transport the parameters equally as whole
entities. Its row is therefore pinned. The action of $G_m$ on the body
gives its equivariance, also for quantifiers and modal formulas. This
establishes term closure for C. Equality of relational entities is
agreement of their continuation rows on all target tuples.

## Why all admitted families have joins

At $n$ let $A$ be an admitted family of relations of one type and put
$E=A_{\mathrm{id},\epsilon}$. Enlarge a pin $N$ for $A$ to contain every
partner of its elements and every singleton block at $n$. There are only
countably many coordinates, so $N$ stays countable. If $\pi\in G_n$ fixes
$N$ pointwise, then $\pi[E]=E$ by pinning and equivariance.

For $(f,w):n\to m$ set
\[
 J_{f,w}=\bigcup\{X_{k,w}:X\in E,\ k:n\to m,\ k|_N=f|_N\}.
\]
This profile has pin $N$. Postcomposing by an automorphism of $m$ permutes
the eligible maps bijectively and transports their rows, giving equivariance.
The choice $k=f$ shows that $J$ is an upper bound of $E$.

Let $Z$ be any upper bound, with pin $T$, and consider a contribution
$X_{k,w}$ in the displayed union, with pin $L$ for $X$. Close $T$ and $L$
under partners. Choose $\pi\in G_n$ fixing $N$ pointwise and moving all
doublets of $L$ outside $N$ off $T$. There are $\aleph_1$ ordinary doublets
in every coordinate, and only countably many to avoid. Prescribe $r:n\to m$
on $T$ as $f$, and on $\pi[L]$ as $k\pi^{-1}$. On the overlap these
prescriptions agree, since the overlap lies in $N$ and $k|_N=f|_N$.
Their domains are unions of blocks, so extend them to a block-respecting
map on the remaining blocks. Now $\pi X\in E$ and
\[
 X_{k,w}=X_{r\pi,w}=(\pi X)_{r,w}\subseteq Z_{r,w}=Z_{f,w}.
\]
Hence $J\le Z$. This argument applies at every stage and every relational
type, including $t$, and proves necessary Boolean Completeness.

## Why Barcan and Atomlessness hold

Suppose a property has a witness at $(f,w):n\to m$. Close a pin for the
property under partners. Replace $f$ by a map $f'$ agreeing on this pin
and having a block-respecting right inverse $s:m\to n$. To do so, in each
coordinate reserve a fresh source doublet for each target block. Map it
bijectively onto a target doublet or constantly onto a target singleton.
There are enough fresh doublets even after the countably many blocks of
the pin have been assigned. Select the inverse on each target doublet and
one preimage per singleton. Fill the other source blocks arbitrarily.
Thus every typed target entity lifts along $(f',\epsilon)$ by transport
along $(s,\epsilon)$. It also lifts along an identity-map word $w$: on
words with suffix $w$ put its rows after removing $w$, and use empty rows
on the other words. This preserves the pin and symmetry. Factor $(f',w)$
into these two arrows. The property has the same row at $(f',w)$ as at
$(f,w)$, so its witness comes from a current entity, giving ordinary Barcan
at all types and stages.

For any nonzero proposition fix a nonempty row and a pin. In a doublet
outside the pin, the map can either separate the two members or identify
them while its target, word and values on the pin stay fixed. The test
that their images differ is pinned by the doublet and is equivariant under
every target automorphism. It divides the proposition into two nonzero
parts, proving necessary Atomlessness.

## The two modal separations

At stage $0$ put $P(f,w)$ iff the target $n$ is below $1$. For every true
$q$ the coordinate inclusion $u:0\to1$ witnesses $\Diamond_{\ne}q$ but
falsifies $P$, as in the [original return-map proof](integer-stages-paired-individuals-glued-constants.html).
Indeed, given a true $r$ at $1$, take a doublet in coordinate $1$ outside
its pin. Return by fixing the ordinary elements and sending the new
singleton to that doublet; then $vu=1_0$. Go forward again by collapsing
the doublet onto the singleton. The resulting loop $xv$ fixes the pin for
$r$, giving $q$ at $vu$ and $r$ at $xv$. Thus $P$ is not two-hat
necessary.

At each target stage define a property $Y$ of propositions. Its row is
all propositions if $n<1$, and otherwise those admitting a countable pin
omitting the singleton in coordinate $1$. This uses existence of an
ordinary pin, independently of any optional enlargement used in the join
proof. It is a target-only row with empty source pin; target automorphisms
fix the distinguished singleton and carry pins to pins, so it is equivariant.
At $n\ge1$, the local proposition on empty-word endomorphisms that send
this singleton to itself is equivariant and has no pin omitting it.
Changing only that one input at the identity proves the latter claim.
Consequently $(\forall z\,Yz)=P$ as proposition entities.

For each current proposition $z$, expand its pin to a countable $N$
including the partners of all its members in coordinate $1$. Use for $q$
the empty-word endomorphisms of $0$ **injective on $N$**. This is a true
pinned proposition invariant under left target automorphisms. If
$\Diamond_{\ne}q$ at $k$, then $\Diamond q$ there, so some continuation
makes the composite injective on $N$. It follows that $k$ is injective on
$N$. A coordinate-$1$ member of the pin and its distinct partner cannot
then be sent into the target's singleton block. Hence $k$ carries a pin
of $z$ to one omitting that singleton whenever it exists. This gives
$\hat{\hat\Box}(Yz)$, hence $\Box_5(Yz)$, for every current $z$. The
Barcan formula for $\Box_5$, a theorem of C, gives $\Box_5P$.

For the other separation let $D$ select targets with a singleton at
coordinate $0$ and let $a$ be that singleton at $0$. Take for $q$ the
empty-word endomorphisms of $0$ fixing $a$, an equivariant true test.
If $k:0\to m$ has $m<0$, then $k(a)$ lies in a doublet. At $m$ the
test that an endomorphism with empty word separates that doublet is true
and equivariant. Any return $v$ with $vk\in q$ collapses the doublet to
$a$; no further continuation can satisfy the separation test. Thus
$\neg\Diamond_{\ne}q$ at $k$, giving $\hat{\hat\Box}D$. For each true $r$
at $0$ take an ordinary coordinate-$0$ doublet off its pin, send $a$ into
that doublet on an arrow to $-1$, and return by collapsing the doublet to
$a$. The loop fixes the pin for $r$, so $r$ is possible after this arrow
to a target falsifying $D$. This refutes $\Box_{\ne}D$.

Translation of all stages and coordinate labels by one respects the
automorphism groups and every domain condition. The two separations hold at
every stage. For the same reason the empty-parameter case of Logical
Necessity holds. For one propositional constant, or any set-sized purely
relational signature, use the [last-letter assignment](integer-stages-paired-individuals-glued-constants.html)
at stage $0$. All assigned profiles are equivariant and this is preserved
on each final-letter sector. For each pure matrix and ordered list of
variable types use the same realizing tuple across all choices of matching
names; each constant then uses only countably many witness pins.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, constructed the symmetric
variation on 26 November 2026, adapting the two models cited above.
