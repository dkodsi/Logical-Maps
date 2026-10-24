# Propositional ND and Inextensible Comprehension imply Weakly Rigid Power

Original derivation by Codex (OpenAI), prompted by Daniel Kodsi, 22 October
2026; written out for the database by Codex (OpenAI), prompted by Daniel
Kodsi, 23 October 2026. The direct source is
[Necessary distinctness and Inextensible Comprehension imply Weakly Rigid Power, §§1–6](../../../../submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md),
an unpaginated research note. The definitions are those of the current
database; literature novelty is not asserted.

## Statement and notation

For each relational type $\tau=\bar\sigma t$, including $\tau=t$,
the following implication holds over the fixed logic C:

$$
 \mathrm{ND}_t\ \land\ \mathrm{IC}_{\tau t}
 \quad\Longrightarrow\quad \mathrm{WRP}_{\tau}.       \tag{1}
$$

Here **IC means Inextensible Comprehension, not Intensional Choice**.
It supplies an inextensible coextension of each property of
$\tau$-relations. Both premises are unboxed and hold at the evaluation
point. The database record uses the full IC schema, from which each
required $\tau t$ instance follows.

Let $\mathrm{WP}$, $\mathrm{WI}$ and $\mathrm{WR}$ denote weak
persistence, weak inextensibility and weak rigidity. For a relation $A$,

$$
 \mathrm{WI}(A):=
 \forall Z\,.\,
 \bigl(\forall\bar x\,.\,A[\bar x]\to\Box Z[\bar x]\bigr)
       \to A\le Z.
$$

Inextensibility is $\Box\mathrm{WI}(A)$; rigidity is persistence
together with inextensibility, equivalently $\Box\mathrm{WR}(A)$.
Entailment $A\le B$ is necessary universally quantified inclusion.
The background C proves NI, T and 4, and that weak rigidity implies
persistence. For the latter, apply WI to
$\lambda\bar x\,.\,\Box A[\bar x]$, using WP and 4.

We will say that $A$ has necessary internal separation when

$$
 \operatorname{Sep}(A):=
 \Box\forall\bar a\,\bar b\,.\,
 \bigl(A[\bar a]\land A[\bar b]\land\bar a\ne\bar b\bigr)
              \to\Box(\bar a\ne\bar b).             \tag{2}
$$

Tuple equality is the conjunction of coordinate identities. All
relations, products and families below have admitted types ending in
$t$. The empty tuple uses the same conventions.

## 1. Consequences of current propositional ND

First, current $\mathrm{ND}_t$ gives necessary distinctness of any
two current entities, at any admitted type. If $a\ne b$, the proposition
$p:=(a=b)$ is false and therefore differs from $\top$. Propositional
ND gives $\Box(p\ne\top)$. Were $a=b$ at a reached world, NI there
would give $\Box(a=b)$, that is $p=\top$, a contradiction.
Coordinatewise this gives necessary distinctness of currently distinct
tuples. We have not obtained a boxed universal ND assumption.

Second, let $p$ be persistent, so $\Box(p\to\Box p)$, and suppose
$\neg p$ currently. Then $p\ne\top$, and current $\mathrm{ND}_t$
gives

$$
 \Box(p\ne\top)=\Box\neg\Box p.
$$

Together with persistence this entails $\Box\neg p$. Thus an initially
false persistent proposition cannot become true. We use this observation
at the evaluation point, not as an optional ND premise at later worlds.

## 2. Inextensible coextensions of separated persistent relations

Suppose $A$ is persistent and $\operatorname{Sep}(A)$ holds. Let $G$
be inextensible and currently coextensive with $A$. Every current
$G$-tuple necessarily satisfies $A$, so WI of $G$ gives $G\le A$.

At an arbitrary reached world, suppose
$A[\bar a]\land\neg G[\bar a]$. Every $G$-tuple $\bar b$ there
is an $A$-tuple, since $G\le A$, and differs from $\bar a$.
Equation (2) therefore gives $\Box(\bar b\ne\bar a)$ for each
such $\bar b$. WI of $G$ is available there, because $G$ is
inextensible. Apply it to the complement of the tuple haecceity of
$\bar a$ to obtain

$$
 G\le\lambda\bar b\,.\,\bar b\ne\bar a,
 \quad\text{hence}\quad \Box\neg G[\bar a].
$$

Persistence of $A$ also gives $\Box A[\bar a]$. The same tuple
therefore remains a witness to

$$
 q:=\exists\bar a\,.\,A[\bar a]\land\neg G[\bar a].
$$

The reached world and witness were arbitrary, so
$\Box(q\to\Box q)$. Current coextension gives $\neg q$.
Section 1 gives $\Box\neg q$, and hence $A\le G$.
Mutual entailment yields $A=G$. Consequently $A$ is both persistent
and inextensible: it is rigid.

This lemma used IC only to the extent of being given the one
inextensible coextension $G$. It used current $\mathrm{ND}_t$
only for the initially false persistent proposition $q$.

## 3. Products give necessary internal separation

We give the product step explicitly. If $A,B$ are weakly rigid, their
product $K[\bar a,\bar b]:=A[\bar a]\land B[\bar b]$ is weakly
persistent. To prove WI of $K$, suppose a test relation $Z$ is
necessary on every current $K$-tuple:

$$
 \forall\bar a\,\bar b\,.\,
 A[\bar a]\land B[\bar b]\to\Box Z[\bar a,\bar b].
$$

For a fixed current $A$-tuple $\bar a$, WI of $B$ gives
$\Box\forall\bar b\,.\,B[\bar b]\to Z[\bar a,\bar b]$.
Thus every current $A$-tuple necessarily satisfies
$H[\bar a]:=\forall\bar b\,.\,B[\bar b]\to Z[\bar a,\bar b]$.
WI of $A$ now gives

$$
 \Box\forall\bar a\,\bar b\,.\,
 A[\bar a]\land B[\bar b]\to Z[\bar a,\bar b],
$$

which is $K\le Z$. These are two successive WI applications; no
quantifier was moved from outside a box to inside one.

Now let $A$ be weakly rigid and apply this to $A\times A$.
Every current pair satisfies

$$
 D[\bar a,\bar b]:=
 \Box(\bar a=\bar b)\ \lor\ \Box(\bar a\ne\bar b),
$$

by NI and section 1. The predicate $D$ is persistent by 4, so
each current pair necessarily satisfies $D$. WI of $A\times A$
gives $(A\times A)\le D$. At a reached world, distinct $A$-tuples
cannot satisfy the first disjunct, by T, and therefore satisfy the
second. This is precisely $\operatorname{Sep}(A)$.

In particular, under $\mathrm{ND}_t$, a weakly rigid $A$ becomes
rigid if IC at its type supplies an inextensible coextension:
apply section 2, using its C-provable persistence. Thus

$$
 \mathrm{ND}_t+\mathrm{IC}_{\tau}
       \quad\Longrightarrow\quad\mathrm{TR}_{\tau}. \tag{3}
$$

The use of IC in (3) is essential to this argument.

## 4. Inextensible Comprehension descends one property type

For a tuple $\bar a$, let
$\delta_{\bar a}:=\lambda\bar b\,.\,\bar b=\bar a$.
These tuple haecceities are rigid in C. Indeed, NI gives persistence;
at any reached world a test necessary on their current instances is
necessary of $\bar a$, and equality substitution gives the required
entailment. This proves WI at every reached world. For the empty
tuple, the haecceity is $\top$.

Given an arbitrary $X^\tau$, form its singleton family

$$
 J_X(Y):=\exists\bar a\,.\,
           X[\bar a]\land Y=\delta_{\bar a}.
$$

IC at $\tau t$ provides an inextensible $G^{\tau t}$ currently
coextensive with $J_X$. Every current member of $G$ is rigid,
and rigidity is persistent. WI of $G$ therefore gives
$G\le\lambda Y\,.\,\operatorname{Rigid}(Y)$. Likewise it gives
necessary containment in the family of tuple haecceities: each current
witness to $Y=\delta_{\bar a}$ continues to witness singletonhood by
NI. These are necessary containments, not a necessitated coextension.

Put

$$
 U[\bar a]:=\exists Y^\tau\,.\,G(Y)\land Y[\bar a].
$$

We show $U$ is inextensible. At any reached world, $G$ is weakly
inextensible and every current $G$-member $Y$ is rigid, by the
necessary containment just proved. Let $Z$ be necessary on every
current $U$-tuple. For each current $G$-member $Y$, the same test
is necessary on all its current tuples. WI of $Y$ gives $Y\le Z$,
or
$\Box\forall\bar a\,.\,Y[\bar a]\to Z[\bar a]$.
WI of $G$, tested against
$\lambda Y\,.\,\forall\bar a\,.\,Y[\bar a]\to Z[\bar a]$,
then gives $U\le Z$. Thus WI of $U$ holds at every reached world.

At the initial world, coextension of $G$ with $J_X$ makes $U$
coextensive with $X$: an $X$-tuple contributes its own haecceity,
and every member of $G$ is the haecceity of some current $X$-tuple.
We have proved

$$
 \mathrm{IC}_{\tau t}\quad\Longrightarrow\quad
 \mathrm{IC}_{\tau}.                              \tag{4}
$$

This descent is a C derivation; it uses neither ND nor any choice
principle. Combining (3) and (4), the premises of (1) already make
every current weakly rigid $F^\tau$ rigid.

## 5. The rigid-power family is rigid

Fix such a rigid $F$. Section 3 gives $\operatorname{Sep}(F)$.
Let

$$
 R_F:=\lambda Y^\tau\,.\,
             \operatorname{Rigid}(Y)\land Y\le F.
$$

This property is persistent in C: both rigidity and entailment have
necessary forms. We show $\operatorname{Sep}(R_F)$.

At any reached world take distinct rigid $X,Y\le F$. Coextensive
weakly rigid relations are identical in C: weak persistence of each
and WI of the other give mutual entailment. Hence $X,Y$ differ on
some current tuple. Suppose $X[\bar a]\land\neg Y[\bar a]$;
the opposite case is symmetric. Every current $Y$-tuple is an
$F$-tuple distinct from the $F$-tuple $\bar a$, so separation of
$F$ makes it necessarily distinct from $\bar a$. WI of $Y$
against the complement of $\delta_{\bar a}$ gives
$\Box\neg Y[\bar a]$. Persistence of $X$ gives
$\Box X[\bar a]$. Thus $X,Y$ remain distinct.

This proves (2) for $R_F$, including members quantified at reached
worlds. IC at $\tau t$ gives a current inextensible coextension of
$R_F$. Section 2 makes it identical with $R_F$ and proves $R_F$
rigid. This establishes the typed Rigid Power conclusion under the
premises of (1).

## 6. Bounded propagation identifies the weak-power family

It remains to handle weakly rigid subrelations arising at later
worlds. We do not assume that current Tame Rigidity holds necessarily.

At any reached world $v$, let $X^\tau$ be weakly rigid there and
suppose $X\le F$. Rigidity of $F$ and $\operatorname{Sep}(F)$
are available at $v$ and all its successors. Each current
$F$-tuple $\bar a$ has its $X$-membership decided necessarily.
If $X[\bar a]$, WP of $X$ gives $\Box X[\bar a]$.
Otherwise every current $X$-tuple is an $F$-tuple distinct from
$\bar a$, so separation of $F$ and WI of $X$ give
$\Box\neg X[\bar a]$. Thus every current $F$-tuple satisfies

$$
 D_X[\bar a]:=\Box X[\bar a]\lor\Box\neg X[\bar a].
$$

By 4, this decision predicate is persistent. WI of $F$ at $v$
therefore gives $F\le D_X$. This step covers **all** $F$-tuples
at later worlds, including those not represented by a tuple chosen
at $v$.

Now take any world $u$ accessible from $v$ and any current test $Z$
there with

$$
 \forall\bar a\,.\,X[\bar a]\to\Box Z[\bar a].       \tag{5}
$$

Every current $F$-tuple at $u$ satisfies $D_X$. In its positive
case, T gives $X[\bar a]$, and (5) gives $\Box Z[\bar a]$;
in its negative case, $\Box\neg X[\bar a]$ holds. In either case
$\Box(X[\bar a]\to Z[\bar a])$. WI of $F$ **at $u$** yields

$$
 F\le\lambda\bar a\,.\,X[\bar a]\to Z[\bar a].
$$

Since $X\le F$ persists, this implies $X\le Z$. We have proved
WI of $X$ at every such $u$. Weak rigidity already gives persistence
of $X$, so $X$ is rigid at $v$.

As $v$ and its current $X$ were arbitrary, we have proved

$$
 \Box\forall X^\tau\,.\,
  \bigl(\operatorname{WeaklyRigid}(X)\land X\le F\bigr)
                      \to\operatorname{Rigid}(X).  \tag{6}
$$

The converse implication holds in C by T. Therefore the weak-power
property
$P_F:=\lambda X\,.\,\operatorname{WeaklyRigid}(X)\land X\le F$
and $R_F$ are necessarily coextensive, hence identical by the
relational order's antisymmetry. Section 5 made $R_F$ rigid, so
$P_F$ is rigid and in particular weakly rigid. Together with
sections 3–4 for the initial weakly rigid $F$, this proves (1).

## Exact scope and verification

Only current $\mathrm{ND}_t$ and IC at $\tau t$ were assumed.
Necessary separation was obtained by WI of products; necessary
rigidity of future weak subrelations was obtained by the two
successive WI uses within $F$ in section 6. There is no BF step,
no boxing of an optional premise, and no use of Atomicity, Boolean
Completeness, Rigid Comprehension or Intensional Choice.

The proof also supplies TR at $\tau$ and RP at $\tau$, but it does
not establish the unrestricted implication TR + RP implies WRP:
its bounded future tameness is explicitly derived from the stated
premises. The all-schema implication WRP implies RP elsewhere in
the database uses the higher power-property type; it is not a
same-type shortcut in this proof.

The submission's [catalog entry rigidity.09](../../../../submissions/classicism-results-2026-10-24-v2/CATALOG.md#rigidity.09)
and corresponding CATALOG.json entry separately record the successful
research check of InextensibleWeakPowerCertificates, manifest
20261023T022700791873Z. This later evidence supersedes the source
note's drafting-time statement that there was no formal verification.
It does not by itself certify the generated statement of this new
database record. No compiler was run for this registration; its
database status remains lean: none.
