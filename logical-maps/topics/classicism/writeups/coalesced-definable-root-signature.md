# Coalesced sum: exits into pointed components for Σ, definable root

Cian Dorr gave the definable root on 20 October 2026
(coalesced-definable-root). GPT-6 Astra (OpenAI), prompted by Cian Dorr,
adapted it on 1 November 2026 to a signature interpreted in the components,
with a freely chosen root extension for each constant. Claude Fable 5.2
(Anthropic), prompted by Cian Dorr, wrote this description, the verification
and the injectivity argument on 21–22 November 2026. Cian Dorr has checked
the construction against the injectivity argument. No Lean verification is
claimed.

## The construction

Let $\Sigma^{+}$ be $\Sigma$, with an individual constant $d$ added if
$\Sigma$ has none. C($\Sigma^{+}$) is conservative over C($\Sigma$).

- **Components.** A set $A$ of pointed action models for
  $\mathcal L(\Sigma^{+})$, with disjoint objects and arrows, complete for
  C($\Sigma^{+}$): every closed sentence consistent with C($\Sigma^{+}$) is
  true at the distinguished object $V_{\mathfrak A}$ of some
  $\mathfrak A\in A$.
- **Arrows.** Add an object $W_0$. Its arrows out are its identity and, for
  each $\mathfrak A$ and each arrow $k$ of $\mathfrak A$ out of
  $V_{\mathfrak A}$, an arrow $k\circ\varepsilon_{\mathfrak A}$, where
  $\varepsilon_{\mathfrak A}:W_0\to V_{\mathfrak A}$ is the exit. No arrow
  enters $W_0$ except its identity.
- **Composition.**
  $k'\circ(k\circ\varepsilon_{\mathfrak A}):=(k'k)\circ\varepsilon_{\mathfrak A}$.
- **Individuals.** The individuals at $W_0$ are the individual constants of
  $\Sigma^{+}$; $\varepsilon_{\mathfrak A}$ sends each to its denotation at
  $V_{\mathfrak A}$. (Closed terms of type $e$ are individual constants, no
  type ending in $e$ being admitted.)
- **Domains at $W_0$.** By recursion on types. An entity of type
  $\bar\tau t$ is an intension $F$ over the arrows out of $W_0$ such that,
  for some closed term $u$ of $\mathcal L(\Sigma^{+})$ of that type, the
  value of $F$ at $k\circ\varepsilon_{\mathfrak A}$ is the extension at $k$
  of the entity $u$ denotes in $\mathfrak A$, for every $\mathfrak A$ and
  $k$. Its value at the identity is any set $E$ of tuples of root entities
  of the types $\bar\tau$. Write $F=(E,u)$, and call $E$ the *root
  extension* and $u$ a *descriptor*.
- **Evaluation point.** $1_{W_0}$.
- **Interpretation of $\Sigma$.** An individual constant denotes itself. A
  relational constant $c$ denotes $(E_c,c)$ for any chosen $E_c$. Its
  transport along $\varepsilon_{\mathfrak A}$ is $\mathfrak A$'s own
  interpretation of $c$.

The differences from coalesced-definable-root: the components interpret the
signature and are complete for C($\Sigma^{+}$), not only for C; one exit
into each pointed component replaces the arrows for every interpretation of
$d$ into every object; and the constants of $\Sigma$ are not at the top but
keep their own descriptors, with root extensions left to choice.

**Descriptors.** $(E,u)$ and $(E',u')$ are the same entity iff $E=E'$ and
C($\Sigma^{+}$) proves $u=u'$. If $u=u'$ is unprovable, $u\ne u'$ is
consistent, so it holds at some $V_{\mathfrak A}$ and the component parts
differ. So each root entity has a descriptor that is well defined up to
provable identity.

**Landing.** The transport of $(E,u)$ along $\varepsilon_{\mathfrak A}$ is
the entity $u$ denotes at $V_{\mathfrak A}$, so it lies in the component
domain.

## It is a model of C

As for coalesced-definable-root. Let $s$ be a term with parameters
$(\bar E,\bar u)$ from the root domains. At an arrow into $\mathfrak A$ its
denotation is computed in $\mathfrak A$ from the transported parameters,
which are the denotations of $\bar u$; so it is the denotation of the closed
term $s[\bar u]$, uniformly in the arrow. At the identity its extension is
the set of tuples of root entities satisfying it at $W_0$, and nothing
constrains that set. So $s$ denotes the root entity $(E',s[\bar u])$ for
some $E'$. The axioms of C hold at $W_0$ because denotations are computed
extensionally on intensions, and the other worlds are worlds of the
components. Two consequences are used below.

1. A closed term $u$ denotes an entity with descriptor $u$, whatever the
   root extensions $E_c$ are. Only its root extension depends on them.
2. An application $(E,u)$ of type $\sigma t$ to a root entity $x$ with
   descriptor $v$ is the root proposition with descriptor $uv$, true at the
   identity iff $x\in E$.

## Maximalism (signature Σ) and Possibility+ (signature Σ)

A closed sentence holds at $\varepsilon_{\mathfrak A}$ iff it holds at
$V_{\mathfrak A}$. Every closed sentence consistent with C($\Sigma$) is
consistent with C($\Sigma^{+}$), so it holds at some $V_{\mathfrak A}$ and
is possible at $W_0$. A closed identity of $\mathcal L(\Sigma)$ is true at
$W_0$ iff C($\Sigma$) proves it, by the descriptor criterion and
conservativity. For Possibility+, distinct root individuals distinct from
the constants in $P$ are fresh distinct constants, and substituting them
for the free variables of a consistent $P$ gives a consistent sentence.

This holds for every choice of the root extensions $E_c$. The map
$(E,u)\mapsto[u]$ is a homomorphism from the root domains onto the closed
terms modulo provable identity.

## Constants are injective on closed terms

**Proposition.** Let $c$ be a constant of $\Sigma$ of type
$\bar\beta\,\sigma\,\bar\beta'\,t$, and let $A$, $B$ be closed terms of
$\mathcal L(\Sigma)$ of type $\sigma$, which may contain $c$. If

$$C(\Sigma)\vdash\forall\bar w\,\bar w'\,.\,c[\bar w,A,\bar w']\leftrightarrow
c[\bar w,B,\bar w'],$$

then $C(\Sigma)\vdash A=B$. In particular, for a constant $Q$ of type
$\sigma t$: $C(\Sigma)\vdash QA\leftrightarrow QB$ only if
$C(\Sigma)\vdash A=B$.

*Proof.* Suppose C($\Sigma$) does not prove $A=B$; then neither does
C($\Sigma^{+}$). Take the model above with

$$E_c:=\{(\bar w,x,\bar w'):\text{the descriptor of }x\text{ is provably
identical to }A\}.$$

This is specified before any denotation is computed, and by consequence 1
the denotation of $A$ has descriptor $A$ and that of $B$ has descriptor $B$
whatever $E_c$ is. So at $W_0$, $c[\bar w,A,\bar w']$ is true for all root
$\bar w,\bar w'$ and $c[\bar w,B,\bar w']$ for none. Every root domain is
nonempty, so the displayed sentence is false at $W_0$, which is a model of
C($\Sigma$). $\square$

When $\sigma=e$ the statement is trivial, closed terms of type $e$ being
constants.

**Corollary.** Maximalism (signature Σ) proves, for closed $A$, $B$ and a
constant $Q$ of type $\sigma\tau$ with $\tau\ne e$: $QA=QB\to A=B$. (If
$QA=QB$ is true it is provable, hence so is the displayed biconditional for
the constant $Q$, hence $A=B$.)

The same choice of root extension shows more generally that a closed term
built from $c$ by filling its other arguments is injective on closed terms.
This is the property of constants that the Russell–Myhill argument in
strong-possibility-signature-r-inconsistent needs.

## Other verdicts

- **Actuality.** $(\text{true},\bot)$ is true at the identity and nowhere
  else, and no arrow leads back to $W_0$; the group's argument applies.
- **Relational Choice** holds by the group's argument, being evaluated at
  the identity, where root extensions are unconstrained.
- **Boxed principles.** Every pure sentence consistent with C is possible
  at $W_0$, so the group's arguments from that fact apply.
- The map derives the rest from these and from Maximalism (signature Σ):
  the failure of ND (directly: $(\text{false},\bot)$ and
  $(\text{true},\bot)$ are distinct at $W_0$ and identical along every
  exit), of Atomicity, and of Strong Possibility (signature Σ); Well-Ordering
  and Transversal Choice; and the other signature principles.

## The root algebra (23 November 2026)

Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, added this section and
the argument root-algebra on 23 November 2026.

Let $L$ be the Lindenbaum algebra of C($\Sigma^{+}$). A root proposition is
$(e,[v])$ with $e$ its truth value at the identity and $v$ a closed
sentence. A closed sentence fails at some world seen from $W_0$ through an
exit iff its negation is consistent with C($\Sigma^{+}$), since by necessitation
$\vdash v$ iff $\vdash\Box v$. So at $W_0$

$$\Box(e,v)\iff e=1\text{ and }\vdash v,\qquad
(e,v)\le(f,w)\iff e\le f\text{ and }\vdash v\to w .$$

The propositions at $W_0$ form $2\times L$, and every set of them is the root
extension of a root property. None of this depends on $A$ or on the $E_c$.

**Boolean Completeness (type $t$) fails.** A greatest lower bound at $W_0$
is one in $2\times L$, so it is enough that $L$ is not complete.

- *$\Sigma^{+}$ countable.* Let $\varphi_n$ say that there are exactly $n$
  individuals ($n\ge1$). Each is consistent with C($\Sigma^{+}$), true in the
  full one-world model with $n$ individuals under any interpretation of the
  constants, and they are pairwise inconsistent. If $L$ were complete,
  $S\mapsto\bigvee\{\varphi_n:n\in S\}$ would be injective on $\mathcal
  P(\omega)$, because $\varphi_m\wedge\bigvee_{n\in S}\varphi_n=\bigvee_{n\in
  S}(\varphi_m\wedge\varphi_n)$ is $\varphi_m$ or $\bot$ as $m\in S$ or not.
  But $L$ is countable.
- *$\Sigma^{+}$ with infinitely many constants.* Suppose first there are
  infinitely many relational constants $c_0,c_1,\ldots$, of types
  $\bar\rho_i t$. Fix closed terms $\bar a_i$ of types $\bar\rho_i$ not
  containing them ($d$ at type $e$, $\lambda\bar x\, .\,\bot$ otherwise), and
  put $P_i:=c_i(\bar a_i)$ and $a_i:=P_i\land\bigwedge_{j<i}\neg P_j$. These
  are consistent and pairwise inconsistent. Let $w$ be an upper bound of the
  $a_i$ with $i$ even, and suppose $w$ mentions only $c_j$ with $j<N$. For
  even $i>N$, substituting $\lambda\bar x\, .\,\top$ for $c_i$ and $\lambda\bar
  x\, .\,\bot$ for $c_j$ ($N\le j<i$) in a proof of $a_i\to w$ gives $\vdash
  \bigwedge_{j<N}\neg P_j\to w$. So $a_M\le w$ for every odd $M>N$, and
  $w\land\neg a_M$ is a strictly smaller upper bound. With infinitely many
  individual constants instead, the same argument works with
  $a_i:=(c_i=c_0)\land\bigwedge_{1\le j<i}c_j\ne c_0$ ($i\ge1$): substitute
  $c_0$ for $c_i$ and generalize on the fresh $c_j$ to get
  $\vdash\bigwedge_{1\le j<N}c_j\ne c_0\land\exists y\, .\,y\ne c_0\to w$, which
  every $a_M$ with odd $M>N\ge2$ entails.

Every infinite signature has infinitely many constants, so the two cases
cover every $\Sigma$. Neither uses choice.

**Self-atoms need not be atoms or strong atoms (type $t$).** Let $\mathrm F$
be the Fregean Axiom $\forall p\, .\,p=\top\lor p=\bot$, and $s:=(0,\mathrm F)$.

- $s$ is possible at $W_0$, $\mathrm F$ being consistent with C($\Sigma^{+}$)
  (the full one-world model with one individual).
- C proves $\mathrm F\to\operatorname{Atom}(\mathrm F)$: under $\mathrm F$
  the true proposition $\mathrm F$ is $\top$, and the only propositions are
  $\top$ and $\bot$. So $s\to\operatorname{Atom}(s)$ holds at every exit,
  and trivially at the identity, where $s$ is false. So $s$ is a self-atom.
- $(0,\mathrm F\land\forall x\forall y\, .\,x=y)$ lies strictly between $\bot$
  and $s$: $\mathrm F$ holds in the full one-world models with one and with two
  individuals. So $s$ is not an atom.
- A strong atom $(0,v)$ at $W_0$ must have, for each closed $w$, $\vdash
  v\to w$ or $\vdash v\to\neg w$, so $v$ must be an atom of $L$. $\mathrm F$
  is not, by the previous point. So $s$ is not a strong atom.

The map derives the versions at all relational types.

## Mathematical Possibilism fails for every signature

*The Cantor regular-open obstruction for the pure definable root was recorded
by OpenAI Codex (GPT-6), prompted by Andrew Bacon, on 16 November 2026. The
arbitrary-signature argument here is by OpenAI Codex (GPT-6), prompted by
Daniel Kodsi, 26 November 2026. Work in external ZFC.*

**No infinite principal interval is complete.** Suppose $[0,b]$ is an
infinite complete principal interval in $L$. Choose countably many disjoint
nonzero elements $a_n\le b$. Such a sequence exists in any infinite Boolean
algebra in ZFC: choose countably many atoms if there are infinitely many,
or repeatedly split a nonzero element in the atomless remainder. Choose
closed representatives for $b$ and for all the $a_n$. Together these use a
countable sublanguage. For $S\subseteq\mathbb N$ let $s$ represent the join
of the $a_n$ for $n\in S$ in the interval. Replace the finitely many
constants of $s$ outside the sublanguage by fresh variables of their
respective types, and universally quantify those variables to obtain $s_0$.
For every $n\in S$, C proves $a_n\to s$ and, by generalization on the
fresh constants, $a_n\to s_0$. As $s_0\le s\le b$, its being an upper
bound implies $[s_0]=[s]$. Thus *every* such join has a representative
in the same countable language. Distinct $S$ have distinct joins: for
$m\notin S$, $b\land\neg a_m$ is an upper bound. There are only countably
many representatives and continuum many $S$, a contradiction. An
infinite principal interval of $2\times L$ has an infinite $L$-factor;
completeness of the product interval would make this factor complete.

**The small complete algebra.** At every root relation type,
an arbitrary set of current tuples is allowed as the identity row,
independently of its old descriptor (take the everywhere-bottom term).
Consequently every current subset and every graph between the fixed
current carriers used below is admitted, including at the types of the
order, subcollections and injections. The ordinal benchmark
$H=\operatorname{Ordinal}_e$ contains
$\alpha_n=\operatorname{OrdSuc}^n(\operatorname{OrdZero})$ for every
standard $n$. These are distinct root intensions. On a finite linear
order, $\alpha_n$ accepts precisely orders of length at least $n$,
by the definition of successor on restricted initial segments.
For $m<n$ the consistent pure sentence asserting such an order of length
$m$ with $\alpha_m$ true and $\alpha_n$ false is realized at a
component exit (for $m=0$ take the empty field). Equality at the root
would persist at this exit. Thus $|H|\ge\aleph_0$.

Let $\rho$ be the ordinal-carrier type. At $\rho t$ the subsets of
$\{\alpha_n:n\in\mathbb N\}$, with empty old descriptor, provide
$2^{\aleph_0}$ distinct carrier elements. On elements of this type code
the complete algebra of regular opens of Cantor space, with its order, by
a root subset and a root graph. Its size is continuum: a countable
clopen basis bounds the number of open sets above, and Boolean joins
of subfamilies of a countably infinite disjoint family of nonzero
clopens give continuum many distinct regular opens. Full current rows
make this an internal complete Boolean algebra for the actual order
and all actual subcollections.

Its carrier $B$ is small in the revised sense. If $H<Y\subseteq B$,
take a countably infinite $A\subseteq Y$. Then $|A|<|Y|$ and the
$2^{\aleph_0}$ external subsets of $A$ are all admitted current
subcollections. The distinct codes required by $\operatorname{Pow}(C,A)$
would force $|C|\ge 2^{\aleph_0}\ge |Y|$, contradicting $C<Y$.
Hence no such $Y$ is power-closed. An actual relational order isomorphism
of $B$ to an entailment interval would make that interval infinite and
complete, excluded above. This refutes the revised [[forcing-possibilism]]
at a single specified carrier type, for every set-sized signature.

## Left open

The model record lists
only verdicts that hold for every $\Sigma$ and every choice of the $E_c$, and
many of these go different ways for different $\Sigma$. The facts
below were found on 23 November 2026 by Claude Opus 5.5 (Anthropic),
prompted by Cian Dorr, and are not recorded as verdicts.

**Fresh constants.** The axioms of C($\Sigma^{+}$) are schemata, so a
constant occurring in no premise can be generalized on: if $\vdash\varphi(c)$
with $c$ not in $\varphi$, then $\vdash\forall x\, .\,\varphi(x)$. This is
what makes the verdicts turn on how many constants $\Sigma$ has.

| Principle | Fails when | Holds when |
|---|---|---|
| BF (all types, type $t$, relational types), Functionality, Tractarianism | $\Sigma^{+}$ has finitely many individual constants (BF at type $e$); or finitely many relational constants, at every relational input type | $\Sigma^{+}$ has infinitely many constants of every type |
| Infinity Schema (type $e$), Axiom of Infinity (type $e$) | finitely many individual constants | infinitely many individual constants (at least the Schema) |
| Atoms are strong atoms (type $t$; relational types) | $\Sigma=\emptyset$ | infinitely many relational constants |

- **BF, Functionality, Tractarianism.** These are equivalent on the map. For
  a root $X=(E,u)$ of type $\sigma t$, $\forall x\, .\,\Box Xx$ holds at
  $W_0$ iff every root entity is in $E$ and $\vdash uw$ for every closed $w$
  of type $\sigma$; $\Box\forall x\, .\,Xx$ holds iff, in addition,
  $\vdash\forall x\, .\,ux$. With a constant of type $\sigma$ not in $u$ the
  second follows by generalization. At type $e$ with only $c_1,\ldots,c_n$,
  $\Diamond\exists x\, .\,x\ne c_1\land\cdots\land x\ne c_n$ holds and no
  root individual is possibly such. At type $t$ with $\Sigma=\emptyset$, the
  argument barcan of coalesced-definable-root applies unchanged: a closed
  sentence of $\mathcal L(\{d\})$ is not contingent at a world with C5,
  Atomicity and one individual.
- **Infinity at type $e$.** The root individuals are the individual constants
  of $\Sigma^{+}$, and distinct constants are distinct at $W_0$.
- **Atoms are strong atoms.** With infinitely many relational constants, $L$
  is atomless: if $v$ is consistent and $c$ is a constant not in $v$, then
  $v\land c(\bar a)$ and $v\land\neg c(\bar a)$ are consistent (substitute
  $\lambda\bar x\, .\,\top$ or $\lambda\bar x\, .\,\bot$ for $c$). Then the
  atoms at a relational type $\bar\sigma t$ at $W_0$ are the entities with a
  single tuple as root extension and descriptor $\lambda\bar x\, .\,\bot$
  (the fresh-constant splitting works at every relational type). These are
  self-atoms and strong atoms, being $\bot$ along every exit. With
  $\Sigma=\emptyset$, $v:=\mathrm F\land\forall x\forall y\, .\,x=y$ is an
  atom of $L$, so $(0,v)$ is an atom at $W_0$. But C does not prove
  $\forall q\, .\,v\le q\lor v\le\neg q$. It fails at the root of the
  coalesced sum of two copies of the one-point Fregean model, where $v$ is
  the root proposition false at the root and true in both components, and
  $q$ is true in just one component.

## The number of relational constants and the two-world cell

*Added 26 November 2026 by OpenAI Codex (GPT-6), prompted by Daniel Kodsi.
The two-world cell and its pointed completeness were proved in the October
work used in [[strong-possibility-incompatible-with-barcan-t]].*

**Atoms are self-atoms at the root if and only if there are infinitely many
relational constants.** This holds for both the type-$t$ bridge and the
schema over relational types. With infinitely many such constants the
preceding fresh-constant argument shows that every root atom is strong.
Suppose instead that there are only finitely many relational constants.
The number of individual constants can be arbitrary. Let $B$ say that
$\Box\mathrm{ND}_t$ holds and there are exactly one individual and four
propositions, as in the proof cited above. Form the closed sentence

$$
\beta=B\land\bigwedge_{\text{relational }c\in\Sigma}(c=\bot_{\operatorname{type}(c)}).
$$

The full two-world S5 model with one individual and these interpretations
realizes $\beta$. C proves $B\to\Box B$ by step (1) of the cited proof,
so $\beta\to\Box\beta$ by NI. The complete finite structure in step (2)
of that proof decides every closed sentence of $\mathcal L(\Sigma^+)$ under
$\beta$. Indeed all relational names in such a sentence have their fixed
bottom values throughout the cone. All individual names denote the sole
individual there and can be replaced by a single individual variable.
The pointed finite-structure argument applies to that variable as well.
Thus $[\beta]$ is an atom of $L$, and $(0,[\beta])$ is an atom in
$2\times L$. At an exit where $\beta$ holds, that atom transports to
$\beta=\top$. It is true there, and a four-element Boolean algebra
has a proper nonzero element below $\top$. Hence this root atom is not
a self-atom, refuting the scheme already at type $t$.

**BF fails at each relational input type when there are finitely many
relational constants.** Consider an input type $\tau=\bar\sigma t$. Fix a
closed tuple $\bar d$ of argument terms in $\mathcal L(\Sigma^+)$, with
any individual name at $e$ and bottom at other types. For arity zero take
the empty tuple. Give a root property empty current extension and descriptor

$$
\lambda Y^\tau\, .\, \beta\land Y[\bar d]\ne\top\land Y[\bar d]\ne\bot .
$$

For any root $Y$ its application to $\bar d$ projects to a closed
proposition. That proposition has a fixed truth value throughout all
$\beta$-points by completeness. Since $\beta$ persists, at any
$\beta$-point it equals one of the two endpoints. Consequently no root
$Y$ can possibly satisfy the displayed property. At a $\beta$ exit
choose a proposition strictly between the endpoints; the constant relation
with this value satisfies the property there. This refutes
$\Diamond\exists Y\, .\,HY\to\exists Y\, .\,\Diamond HY$.
It covers signatures with arbitrarily many individual names.

**Strong Possibility in these signatures.** The denotation of $\beta$
itself at the root is $(0,[\beta])$. Its current bit is zero because the
root has infinitely many propositions, as witnessed by the pairwise
incompatible, consistent individual-cardinality sentences. Thus
$\operatorname{Atom}_t(\beta)$ is consistent with Maximalism in this very
signature. It is a universal Boolean combination of identities, so the
reflection lemma of [[strong-possibility-and-strong-actuality-incompatible]]
applies in the fixed language. Strong Possibility (signature $\Sigma$)
therefore gives $\operatorname{Atom}_t(\beta)$. At every $\beta$-point
$\beta$ equals top in the four-element algebra, which proves in
C($\Sigma$) that $\beta$ is not a self-atom. Hence Strong Possibility
(signature $\Sigma$) is incompatible with Atoms are self-atoms (type $t$)
under the finite-relational-constant hypothesis. The result for the pure
language is recorded at [[strong-possibility-incompatible-with-atoms-are-self-atoms-t]].

## Remaining questions for the family

- **Tame Rigidity** and **Weakly Rigid Power.** Both fail when $\Sigma^{+}$
  has infinitely many individual constants. The root property with every
  constant in its root extension and descriptor $\lambda x\, .\,\top$ is
  weakly rigid at $W_0$, by generalization on a fresh constant. It is rigid
  only if C proves BF at type $e$. Weakly Rigid Power implies Tame Rigidity.
  With finitely many constants, a weakly rigid root relation with finite
  root extension has a descriptor provably equal to a disjunction of
  haecceities of closed terms, and so is rigid. The infinite case is open.
- **Rigid Power.**
- **Contingency of Cardinal CH**, **Possible Cardinal CH** and **Possible
  failure of Cardinal CH**, added on 24 November 2026, remain undecided.
  The earlier strict-smallness argument for Forcing Possibilism is
  historical. The revised Mathematical Possibilism is refuted above.


The group's shared arguments for Tame Rigidity and Rigid Power transfer a
component's counterexample to the root. They build root entities with freely
chosen component parts, which are not available here.
