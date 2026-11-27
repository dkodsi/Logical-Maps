# Strong Possibility (signature Σ) ⇒ ⊥ (conjecture)

The question of the consistency of Strong Possibility is raised at the end of *Classicism*.  This conjecture was added on 22 November 2026, as a site for the proof below, which shows that it holds for a broad range of signatures Σ. Essentially: classicism forces a Russell–Myhill collision, and different
maximalist models can place its witness differently. Claude Fable 5.2
(Anthropic), prompted by Cian Dorr, found the sentences and the models and
wrote the proofs below, 21–22 November 2026. Cian Dorr checked the argument on 25 November 2026. No Lean verification exists yet.

**Status.** Proved when $\Sigma$ has a constant of type 
$\beta_1\cdots\beta_n t$, with some $\beta_i\ne e$.  Open when $\Sigma$ is a *first-order* signature: one in which every constant is an individual
constant, a propositional constant, or a predicate of individuals.

The Appendix below proves an easier version of the theorem, which requires a constant of type $\beta_1\cdots\beta_n t$ where some $\beta_i$ itself has an argument of a type other than $e$: for instance $\beta_i=t\to t$, but not $\beta_i=et$.  

## The theorem

**Theorem.** Suppose $\Sigma$ has a constant $c$ of type
$\beta_1\cdots\beta_n t$ with some $\beta_i\ne e$. Then there are closed
sentences $E_1$, $E_2$ of $\mathcal L(\Sigma)$, each an existential closure
of a conjunction of identity and distinctness claims, such that

1. C($\Sigma$) proves $E_1\lor E_2$;
2. Maximalism (signature Σ) is consistent with $\neg E_1$, and with
   $\neg E_2$;
3. C proves $E_i\to\Box_{\ne}E_i$ for $i=1,2$.

Hence Strong Possibility (signature Σ) is inconsistent for such $\Sigma$:
by 2 it gives $\Diamond_{\ne}\neg E_1$ and $\Diamond_{\ne}\neg E_2$, by 3 it
gives $\neg E_1$ and $\neg E_2$, contradicting 1.

The models are members of coalesced-definable-root-signature, and the
notation is that of its write-up: a root entity is $(E,u)$, with root
extension $E$ and descriptor $u$, a closed term determined up to provable
identity. Write $u\equiv u'$ for provable identity in C($\Sigma^{+}$), and
$[u]$ for the class of $u$. A root proposition is a pair $(b,[v])$ of a
truth value at the identity and a class of closed sentences. A *root
operator* is a root entity $F=(E',u)$ of type $t\to t$; $E'$ is a set of
root propositions, and $Fp$ is the root proposition
$([p\in E'],[uv])$ for $p=(b,[v])$. A root proposition is *true* or *false*
according to its truth value, and a closed sentence is true or false in a
model according to the root proposition it denotes.

## A free operator on propositions

Write $\beta_i=\bar\zeta\,t$ and define the closed term

$$r:=\lambda x^t\,.\,\exists\bar w\,\bar w'\,.\,c[\bar w,\ \lambda\bar
z^{\bar\zeta}\,.\,x,\ \bar w'],$$

of type $t\to t$, where $\bar w$, $\bar w'$ have the types of the arguments
of $c$ before and after the $i$th. The map $x\mapsto\lambda\bar z\,.\,x$ is
injective on root propositions. It sends $(b,[v])$ to the root entity with
descriptor $\lambda\bar z\,.\,v$ whose root extension is everything if $b$
is true and empty if not. Different truth values give different root
extensions, the root domains being nonempty. Different classes give
different descriptors: if $\lambda\bar z\,.\,v\equiv\lambda\bar z\,.\,v'$,
applying both sides to closed terms of the types $\bar\zeta$ gives $v\equiv
v'$. So for **any**
set $R$ of root propositions there is a choice of the root extension of
$c$, namely the tuples whose $i$th member is the image of a member of $R$,
for which

$$r\,p\ \text{ is the root proposition }\ ([p\in R],\,[rv])\qquad
\text{for every root proposition }p=(b,[v]).\tag{1}$$

Call this member of the family *the model with $R$*. Each is a model of
Maximalism (signature Σ). A closed sentence $v$ denotes a root proposition
with descriptor $v$ in all of them; only its truth value depends on $R$.

To show that two closed sentences are not provably identical it suffices to
find an $R$ for which they differ in truth value. Below,
"descriptors $D$" as a choice of $R$ means: all root propositions, of
either truth value, whose descriptor is in $D$.

## Pairing, and the term $Q$

Define

$$\langle x,y\rangle:=r(rx)\land r(\neg ry),\qquad
Q:=\lambda f^{t\to t}\,.\,\forall p\,.\,r(rp)\to r\langle p,fp\rangle,\qquad
\rho:=\lambda x^t\,.\,\exists F^{t\to t}\,.\,x=QF\land\neg Fx.$$

Let $\mathcal P$, $\mathcal N$, $\Pi$ be the sets of classes of closed
sentences of the forms $rv$, $\neg rw$ and $\langle x,y\rangle$.

**Lemma 1.** (i) $rv\equiv rv'$ only if $v\equiv v'$. (ii) $\mathcal P$,
$\mathcal N$, $\Pi$ are pairwise disjoint. (iii) $\langle
x,y\rangle\equiv\langle x',y'\rangle$ only if $x\equiv x'$ and $y\equiv y'$.

*Proof.* (i) $R$ := descriptors $\{[v]\}$: $rv$ is true, and $rv'$ is true
only if $v'\equiv v$. (ii) $R$ := everything: $rv$ and $\langle
x,y\rangle$ are true and $\neg rw$ is false. $R$ := descriptors $\{[v]\}$:
$rv$ is true, while $\langle x,y\rangle$ would need both $rx\equiv v$ and
$\neg ry\equiv v$. That is impossible: $rx\equiv\neg ry$ would put a class
in both $\mathcal P$ and $\mathcal N$, which the first choice of $R$ ruled
out. (iii) $R$ := descriptors
$\{[rx]\}\cup\mathcal N$: $\langle x,y\rangle$ is true, and $\langle
x',y'\rangle$ is true only if $rx'\equiv rx$, so $x'\equiv x$ by (i). $R$ :=
descriptors $\mathcal P\cup\{[\neg ry]\}$: likewise $\neg ry'\equiv\neg ry$,
so $y'\equiv y$. $\square$

**Lemma 2.** For closed $u$ of type $t\to t$: $[Qu]$ is not in
$\mathcal P\cup\mathcal N\cup\Pi$ and is not $[\top]$. $[\top]$ is not in
$\mathcal P\cup\mathcal N\cup\Pi$.

*Proof.* Three choices of $R$.

- $R$ := nothing. $Qu$ and $\top$ are true, $rv$ and $\langle x,y\rangle$
  false. So $[Qu]$ and $[\top]$ are outside $\mathcal P\cup\Pi$.
- $R$ := everything. $Qu$ and $\top$ are true, $\neg rw$ false. So they are
  outside $\mathcal N$.
- $R$ := descriptors $\mathcal P$. Every $r(rp)$ is true and every
  $r\langle p,up\rangle$ false, its argument having a descriptor in $\Pi$;
  so $Qu$ is false, while $\top$ is true. So $[Qu]\ne[\top]$. $\square$

**Lemma 3.** $\rho\top$ is false in every model with $R$.
$[\rho\top]$ is not in $\mathcal P\cup\mathcal N\cup\Pi$, is not $[\top]$,
and is not $[Qu]$ for any closed $u$. And $\rho(Q\rho)\equiv\top$.

*Proof.* $\rho\top$ says that some $F$ has $\top=QF$ and $\neg F\top$. No
root operator $(E',u)$ has $QF=\top$, the descriptors $[Qu]$ and $[\top]$
being different by Lemma 2. So $\rho\top$ is false in
every model with $R$.

For the separations: suppose a closed sentence $s$ is true
in some model with $R$. If $s\equiv\rho\top$, then C($\Sigma$) proves
$s=\rho\top$, so $s$ and $\rho\top$ denote the same root proposition in
that model and have the same truth value there; but $\rho\top$ is false
there. So $s\not\equiv\rho\top$. It is therefore enough to show that every
member of each class to be excluded is true in some model with $R$:

- $R$ := everything. Every $rv$ and every $\langle x,y\rangle$ is true. So
  $[\rho\top]$ is outside $\mathcal P\cup\Pi$.
- $R$ := nothing. Every $\neg rw$ and every $Qu$ is true (Lemma 2). So
  $[\rho\top]$ is outside $\mathcal N$ and is no $[Qu]$.
- $\top$ is true in every model. So $[\rho\top]\ne[\top]$.

The last claim is the Russell–Myhill argument: if $\neg\rho(Q\rho)$,
instantiating $F:=\rho$ gives $\rho(Q\rho)$; so C proves $\rho(Q\rho)$.
$\square$

**Lemma 4 (agreement).** If $Qu\equiv Qu'$ then $uv\equiv u'v$ for every
closed sentence $v$.

*Proof.* $R$ := descriptors $\mathcal P\cup\{[\langle w,uw\rangle]:w$
closed$\}$. Every $r(rp)$ is true, and for $p=(b,[w])$ the argument of
$r\langle p,up\rangle$ has descriptor $\langle w,uw\rangle$; so $Qu$ is
true. Then $Qu'$ is true, so for the $p$ denoted by $v$ the descriptor
$\langle v,u'v\rangle$ is in $R$. It is not in $\mathcal P$, so it is
$[\langle w,uw\rangle]$ for some $w$, and Lemma 1 gives $w\equiv v$ and
$u'v\equiv uw\equiv uv$. $\square$

## The sentences

$$E_1:=\exists F\,.\,QF=Q\rho\land F(Q\rho)\ne\rho(Q\rho)\land F\top=\rho\top,$$

$$E_2:=\exists F\,.\,QF=Q\rho\land F(Q\rho)\ne\rho(Q\rho)\land F\top\ne\rho\top.$$

**C($\Sigma$) proves $E_1\lor E_2$.** By Lemma 3, $\rho(Q\rho)$: there is
$F$ with $Q\rho=QF$ and $\neg F(Q\rho)$. So $F(Q\rho)$ and $\rho(Q\rho)$
differ in truth value and are distinct. And $F\top=\rho\top$ or not.

**C proves $E_i\to\Box_{\ne}E_i$.** Each $E_i$ is an existential closure
of a conjunction of identity and distinctness claims, and C proves that
identity and distinctness are $\Box_{\ne}$-necessary (Background,
*Varieties of necessity*).

So it remains to show $\neg E_1$ and $\neg E_2$ are both consistent with Maximalism (signature Σ).  We will do this by finding models.  Both will be models with $R$ for appropriate choices of $R$.  

## The two models

By Lemmas 2 and 3, $[\top]$, $[Q\rho]$ and $[\rho\top]$ are three
different classes outside $\mathcal P\cup\mathcal N\cup\Pi$.

For a set $\mathcal V$ of classes and a set $R_0$ of root propositions
whose descriptors are not in $\mathcal P\cup\mathcal N\cup\Pi$, let
$R(\mathcal V,R_0)$ consist of

- $(\text{true},d)$ for every $d\in\mathcal P\cup\mathcal N\cup\Pi$;
- $(\text{false},[\langle x,y\rangle])$ whenever $[x]\notin\mathcal V$;
- the members of $R_0$.

This is well defined by Lemma 1.

**Observation.** A root proposition with descriptor in $\mathcal
P\cup\mathcal N$ is in $R(\mathcal V,R_0)$ iff its value is true. One with
descriptor $[\langle x,y\rangle]\in\Pi$ is in it iff its value is true or
$[x]\notin\mathcal V$. A root
proposition whose descriptor is not in $\mathcal P\cup\mathcal N\cup\Pi$
is in $R(\mathcal V,R_0)$ iff it is in $R_0$. The first two clauses only
add root propositions with descriptors in $\mathcal P\cup\mathcal
N\cup\Pi$, and $R_0$ only adds ones with descriptors outside it. So, for instance,
$(\text{false},[\top])$, $(\text{false},[\rho\top])$ and
$(\text{true},[Q\rho])$ are in $R$ only if they are in $R_0$.

**Lemma 5.** In the model with $R=R(\mathcal V,R_0)$, for every root
operator $F$:

$$QF\text{ is true}\iff Fp\notin R\text{ for every }p\in
R\text{ whose descriptor is in }\mathcal V.$$

*Proof.* Let $p=(b,[v])$ and $F=(E',u)$. By (1), $rp=([p\in R],[rv])$,
which is in $R$ iff $p\in R$, a class in $\mathcal P$ being in $R$ only
with the value true. So $r(rp)$ is true iff $p\in R$. Suppose $p\in R$ and
let $z:=Fp$. Then $\neg rz=([z\notin R],[\neg r(uv)])$, in $R$ iff
$z\notin R$. So $\langle p,z\rangle$ is the root proposition with
descriptor $\langle v,uv\rangle$ that is true iff $z\notin R$, and it is in
$R$ iff $z\notin R$ or $[v]\notin\mathcal V$. $\square$

Let $c_\top:=(\text{true},[\top])$ and $e:=(\text{true},[\rho\top])$.

- **Model A:** $\mathcal V:=\{[\top]\}$, $R_0:=\{c_\top,\ e\}$.
- **Model B:** $\mathcal V:=\{[\top],[Q\rho]\}$,
  $R_0:=\{c_\top,\ e,\ a\}$ with $a:=(\text{false},[Q\rho])$.

Let $P$ be the root extension of $\rho$. A root proposition is in $P$ iff
it is $QF$ for some root operator $F=(E',u)$ whose $E'$ omits it; its
descriptor is then $[Qu]$. So $c_\top\notin P$, and $\rho\top$ denotes
$(\text{false},[\rho\top])$.

Call a root operator $F = (E',u)$ *$\rho$-like* if $Qu\equiv Q\rho$. A $\rho$-like $F$ has
$F c_\top=([c_\top\in E'],[\rho\top])$, by Lemma 4 with $v:=\top$. It has
$Fp=([p\in E'],[\top])$ for any $p$ with descriptor $Q\rho$, by Lemma 4 with
$v:=Q\rho$, which gives $u(Q\rho)\equiv\rho(Q\rho)$, together with
$\rho(Q\rho)\equiv\top$ from Lemma 3. And $QF=Q\rho$
iff $F$ is $\rho$-like and $QF$, $Q\rho$ have the same truth value.

**Model A.** The only member of $R$ with descriptor in $\mathcal V$ is
$c_\top$. For $\rho$-like $F$, $Fc_\top\in R$ iff $c_\top\in E'$, since $e$
is in $R$ and, by the Observation, $(\text{false},[\rho\top])$ is not. So by Lemma 5

$$QF\text{ is true}\iff c_\top\notin E'\qquad(F\ \rho\text{-like}).$$

- $Q\rho$ is true, since $c_\top\notin P$; it denotes
  $a':=(\text{true},[Q\rho])$.
- $a'\in P$: take $F:=(\emptyset,\rho)$.
- If $QF=Q\rho$, then $F$ is $\rho$-like and $c_\top\notin E'$, so
  $F\top=(\text{false},[\rho\top])=\rho\top$.

So no $F$ witnesses $E_2$: **$E_2$ fails and $E_1$ holds.**

**Model B.** The members of $R$ with descriptor in $\mathcal V$ are
$c_\top$ and $a$. For $\rho$-like $F$, $Fc_\top\in R$ iff $c_\top\in E'$ as
before, and $Fa=([a\in E'],[\top])$ is in $R$ iff $a\in E'$, since $c_\top$
is in $R$ and, by the Observation, $(\text{false},[\top])$ is not. So

$$QF\text{ is true}\iff c_\top\notin E'\text{ and }a\notin E'\qquad(F\
\rho\text{-like}).$$

- $a\in P$: take $F:=(\{c_\top\},\rho)$. Then $QF$ is false, so it is the
  proposition $a$, and $a\notin\{c_\top\}$.
- Hence $Q\rho$ is false and denotes $a$. Nothing is circular: $a$ was
  defined as a pair before $R$ was chosen.
- $\rho a=(\text{true},[\top])$, since $a\in P$.
- Let $QF=Q\rho$ and $F(Q\rho)\ne\rho(Q\rho)$. Then $F$ is $\rho$-like and
  $QF$ is false, so $c_\top\in E'$ or $a\in E'$. And
  $Fa=([a\in E'],[\top])$ differs from $\rho a$, so $a\notin E'$. Hence
  $c_\top\in E'$, and $F\top=(\text{true},[\rho\top])\ne\rho\top$.

So no $F$ witnesses $E_1$: **$E_1$ fails and $E_2$ holds.**

This proves the Theorem.

## Remarks

- In a model of Maximalism (signature Σ) where $E_i$ holds with witness
  $F$, the conjunction $q$ of the distinctness conjuncts of $E_i$ is a true
  proposition that no closed sentence denotes. Suppose a closed sentence $s$
  denoted it. Then $\Box(\Diamond s\to E_i)$ holds in the model. If
  $\Diamond s\land\neg E_i$ were consistent with C($\Sigma$), Maximalism
  would make it possible there, and at a world where it holds, $\Diamond s$
  would give $E_i$. So C($\Sigma$) proves $\Diamond s\to E_i$. But $s$ is
  consistent, being true in this model, so Maximalism proves $\Diamond s$,
  and hence $E_i$. That contradicts the model of Maximalism in which $E_i$
  fails. If a closed term $u$ denoted $F$, the distinctness conjuncts of $E_i$ at
  $u$ would name $q$. So for these signatures every model of Maximalism has
  a proposition, and an entity of type $t\to t$, that no closed term
  denotes.
- No model of C($\Sigma$) embeds, by an injective homomorphism for all term
  operations, into elementary extensions of both Model A and Model B: such
  an embedding preserves $E_1$ and $E_2$, and one of them holds in the
  source.
- When the constant has an argument whose type itself takes a relational
  argument, the root extension of the constant controls $Q$ on whole
  operators and not only one argument at a time, and a shorter argument
  with a unique twin is available. It is in the Appendix.

## What is open

The signatures all of whose constants are individual constants,
propositional constants or predicates of individuals. No closed term then
has a freely choosable root extension on relational arguments, and nothing
is known. The question includes Strong Possibility (pure), left open in
*Classicism*.

## Appendix: constants with a higher-order argument

This was the first case proved. It uses a different term $Q$, with $\rho$,
$E_1$ and $E_2$ defined from it as in the main text.

### A closed term of type $(t\to t)\to t$

Suppose the constant $c$ has type $\beta_1\cdots\beta_n t$ and one argument
type $\beta_i$ is $\alpha_1\cdots\alpha_m t$ with some $\alpha_j\ne e$. Write
$\alpha_j=\gamma_1\cdots\gamma_l t$ and define closed terms of
$\mathcal L(\Sigma)$:

$$h:=\lambda y^{\alpha_j}\,.\,\exists\bar z^{\bar\gamma}\,.\,y[\bar z],\qquad
G:=\lambda F^{t\to t}\,.\,\lambda\bar x^{\bar\alpha}\,.\,F(h\,x_j),\qquad
Q:=\lambda F^{t\to t}\,.\,\exists\bar w\,\bar w'\,.\,c[\bar w,\,GF,\,\bar w'],$$

where $\bar w$ and $\bar w'$ have the types of the arguments of $c$ before
and after the $i$th. (If $l=0$, $h$ is $\lambda y\,.\,y$.) So $G$ has type
$(t\to t)\to\beta_i$ and $Q$ has type $(t\to t)\to t$. When $c$ itself has
type $(t\to t)\to t$, $Q$ is provably $c$.

Work in coalesced-definable-root-signature, with the notation of its
write-up: a root entity is $(E,u)$, with root extension $E$ and descriptor
$u$. Let the root extension of $c$ be

$$E_c:=\{(\bar w,x,\bar w'):x\in\mathfrak E\}$$

for a set $\mathfrak E$ of root entities of type $\beta_i$ still to be
chosen, the other constants being arbitrary. A *root operator* is a root
entity $F=(E',u)$ of type $t\to t$; $E'$ is a set of root propositions.

**(a) $h$ is onto the root propositions.** For a root proposition $(b,v)$
take the root entity $x:=(E,\lambda\bar z\,.\,v)$ with $E$ everything if
$b$ is true and empty if not. Then $h\,x$ has descriptor
$\exists\bar z\,.\,v$, provably identical to $v$, and is true iff $E$ is nonempty.

**(b) $G$ is injective on root operators.** $GF$ is the root entity with
descriptor $Gu$ and root extension $\{\bar x:h\,x_j\in E'\}$. If
$E'\ne E''$, some root proposition lies in one and not the other, it is
$h\,x_j$ for some $x_j$ by (a), and the root extensions differ. If the
descriptors $u,u'$ are not provably identical, neither are $Gu,Gu'$: from
$Gu=Gu'$, applying both to a tuple with $x_j:=\lambda\bar z\,.\,p$ gives
$up=u'p$ for a variable $p$, and then $u=u'$.

**(c)** For a root operator $F=(E',u)$, the root proposition $QF$ has
descriptor $Qu$ and is true iff $GF\in\mathfrak E$, the
root domains being nonempty. By (b), for **any** set $\mathcal S$ of root
operators there is a choice of $\mathfrak E$, namely
$\{GF:F\in\mathcal S\}$, for which $QF$ is true exactly for
$F\in\mathcal S$.

**(d) $Q$ is injective on closed terms.** If C($\Sigma$) does not prove
$u=u'$ for closed $u,u'$ of type $t\to t$, it does not prove $Qu=Qu'$:
choose $\mathcal S$ to be the root operators with descriptor $u$. Nor does
it prove $Qu=\top$: choose $\mathcal S$ empty.

### Two models

Fix, before any root extension is chosen:

- $P$, the set of root propositions whose descriptor is provably identical
  to $Qu$ for some closed $u$;
- $a:=(\text{false},Q\rho)$ and $c_\top:=(\text{true},\top)$. So $a\in P$,
  and $c_\top\notin P$ by (d).

For a set $S$ of root propositions let $\mathcal S_S$ be the set of root
operators

$$\{(E',u):u\text{ is not provably identical to }\rho,\ c_\top\in E'\}\ \cup\
\{(E',\rho):E'\ne P,\ E'\ne S\},$$

and choose $\mathfrak E$ by (c) so that $QF$ is true
exactly for $F\in\mathcal S_S$.

- **Model A:** $S_A:=P\setminus\{a\}$.
- **Model B:** $S_B:=(P\setminus\{a\})\cup\{c_\top\}$.

Both satisfy Maximalism (signature Σ), as every member of the family does.

**The root extension of $\rho$ is $P$, in both.** A root proposition $x$ is
in it iff some root operator $F=(E',u)$ has $x=QF$ and $x\notin E'$. $QF$
is the proposition with descriptor $Qu$ that is true iff
$F\in\mathcal S_S$. So $x$ has a descriptor $Qu$, and by (d) $u$ is
determined up to provable identity. Conversely let
$x=(b,Qu)$.

- $u$ not provably $\rho$: membership of $(E',u)$ in $\mathcal S_S$ depends
  only on whether $c_\top\in E'$, and $x\ne c_\top$. So some $E'$ omits $x$
  and gives $QF$ the truth value $b$.
- $u$ provably $\rho$ and $b$ true: take $E':=\emptyset$, which is neither
  $P$ nor $S$.
- $u$ provably $\rho$ and $b$ false, so $x=a$: take $E':=S$, which omits
  $a$.

Nothing here is circular: $P$, $a$, $c_\top$ and $S$ were fixed before
$\mathfrak E$.

**The twins.** So $\rho$ denotes $(P,\rho)$, which is not in
$\mathcal S_S$; hence $Q\rho$ is false and denotes $a$. A
root operator $F=(E',u)$ has $QF=Q\rho$ iff $Qu$ is provably $Q\rho$ and
$F\notin\mathcal S_S$, that is, by (d), iff $u$ is provably $\rho$ and
$E'\in\{P,S\}$. The only such $F$ other than $\rho$ is $F^*:=(S,\rho)$.

**The verdicts.** $F^*$ differs from $\rho$ at $Q\rho$: $a\in P$ and
$a\notin S$. $\rho\top$ is the proposition with descriptor $\rho\top$ that
is false, since $c_\top\notin P$. $F^*\top$ has the same
descriptor and is true iff $c_\top\in S$.

- Model A: $c_\top\notin S_A$, so $F^*\top=\rho\top$. $E_1$ holds and $E_2$
  fails.
- Model B: $c_\top\in S_B$, so $F^*\top\ne\rho\top$. $E_2$ holds and $E_1$
  fails.

This proves the Theorem for these signatures, with a unique twin in each
model.


## Further restrictions for first-order signatures

OpenAI GPT-6, prompted by Daniel Kodsi, 27 November 2026. Two independent researchers checked the Barcan arguments below.

With $m$ public individual names, where $m$ is externally finite, signature Strong Possibility forces exactly $\max(1,m)$ individuals at the evaluation point. The [descriptor model](coalesced-definable-root-signature.html) has signature Maximalism and exactly that many individuals. The upper bound reflects through ND-possibility: a tuple violating it supplies as guard the conjunction of its pairwise disequalities, which by necessity of identity prevents the tuple from collapsing wherever that guard remains possible. Distinct public names denote different individuals at a Maximalist point, since the possibility of their disequality excludes identity. The case without individual names is Dorr’s October monism argument. Consequently unboxed Barcan at individual type fails: the finite union of these actual individual haecceities necessarily covers every current individual and some accessible point has more. With infinitely many public individual names the distinctness argument yields all standard finite lower bounds. [October reflection and descriptor constructions](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/sp-structural-proof-package/profile-root-construction-20261022.md)

### Which signatures admit a closed Barcan counterexample?

Consider a fixed $\Sigma$ and a formula $\Phi(p)$ at type $t$ with no free variable other than the displayed proposition. It may contain arbitrary closed $\Sigma$-terms, modalities, and typed quantifiers. Its Barcan instance at a point is
$$
 (\forall p\,\Box\Phi(p))\to\Box\forall p\,\Phi(p).
$$

**Infinitely many nonindividual constants.** Every such instance holds at every ordinary $\Sigma$-Maximalist point. Suppose $\Diamond\exists p\,\neg\Phi(p)$ there, and take a pointed $\Sigma$-model with a witness $b$ to the existential. Choose a nonindividual name $c$ absent from the finite formula, including its displayed closed terms. Its type can be any relational $\tau=\bar\alpha t$. At the witness interpret $c$ by $\lambda\bar x.b$; when $\bar\alpha$ is empty use $b$. Its scalar projection $c^\circ=\exists\bar x\,c(\bar x)$ then equals $b$ as an entire proposition. At each accessible point the constant lift gives the transported $b$ on all inputs and each argument domain is inhabited. The reinterpretation preserves $\neg\Phi(b)$. Consequently $\neg\Phi(c^\circ)$ is a C-consistent closed $\Sigma$-sentence. Ordinary signature Maximalism entails $\Diamond\neg\Phi(c^\circ)$, which contradicts the antecedent of the Barcan instance.

In this case any actual failure of the internal statement $\mathrm{BF}_t$ at a $\Sigma$-Maximalist point must be witnessed by a property of propositions that no closed $\Sigma$-term denotes there. A point at which all such properties have closed names consequently satisfies the full internal $\mathrm{BF}_t$. The argument applies to infinitely many names at unbounded finite types, even when no propositional name occurs.

**Finitely many nonindividual constants.** Signature Strong Possibility implies the failure of one explicit closed Barcan instance, with no bound on the number of individual names. Conjoin the pure cell $B$ asserting necessary propositional distinctness, one individual and four propositions with the finitely many identities assigning bottom to the nonindividual names. Call the result $\Delta$. At the ordinary signature-definable Maximalist root, every proposition descriptor evaluated anywhere in $\Delta$ is invariant under exchanging the two atoms of the four-element proposition algebra. All individual names, including any extra individual marker, already denote the sole individual there; every named relation has its stipulated bottom value. The full finite hierarchy is invariant under this exchange. Thus $\Delta$ is a nonzero root atom, and the universal identity statement that it is an atom transfers by signature Strong Possibility. The usual stable-cell calculation shows that $\Phi(p)=(\Delta\to(p=\top\lor p=\bot))$ is necessary for each current $p$. At a possible $\Delta$-point two of the four propositions are neither endpoint, so $\Box\forall p\,\Phi(p)$ fails. [Original finite-signature proof](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/signature-sp-barcan-20261022.md)

There is also a reduct consequence. Let $\Sigma$ have finitely many nonindividual names and any set of individual names, and extend it to $\Theta$ by at least one new nonindividual name $c$. No pointed $\Theta$-interpretation can satisfy ordinary $\Theta$-Maximalism and satisfy $\mathrm{SP}_\Sigma$ in its reduct. Indeed the $\Sigma$ formula $\Phi$ above passes necessarily at every current input. But a two-world model of $\Delta$ can interpret $c$ as the constant lift of a nonendpoint proposition; hence $\Theta$-Maximalism makes $\Delta\land(c^\circ\ne\top)\land(c^\circ\ne\bot)$ possible. This contradicts the test with current input $c^\circ$. The case where $\Sigma$ is pure is Dorr's established signature-versus-pure obstruction.

These conclusions concern syntactically closed tests or explicit changes of signature. They do not decide the internal local $\mathrm{BF}_t$ in an infinite relational signature. Two independent GPT-6 research agents checked the two directions on 27 November 2026.

### The four-proposition cell under signature Strong Possibility and local Barcan

Let $\Sigma$ be any set of free typed constants. Write $B$ for the closed pure assertion that $\Box\mathrm{ND}_t$ holds, that there is exactly one individual, and that there are four propositions. At a point with $\mathrm{SP}_\Sigma$ and local $\mathrm{BF}_t$, the following holds for every true proposition $a$. There is a current nonzero proposition $u\le B$ and an accessible point where $a$ holds and the transported $u$ is bottom. Thus even the possible propositions in this single specified region cannot all remain possible on every realization of any current truth.

#### The model for the consistency side condition

Use the ordinary signature-definable coalesced root. Add an auxiliary scalar $d$ and, if needed, one individual marker to the descriptor language. As the bulk take a set of pointed models witnessing each C-consistent closed $\Sigma$-sentence. Expand them by $d=\bot$ throughout and choose the marker freely. Add one further component, the full classical intensional hierarchy over the indiscrete two-world S5 frame with one individual, where $d=\top$. Every public relation is bottom throughout this component and every individual symbol is its sole individual. Use an independent entrance into each pointed component and keep all old postcomposites. The root individuals are the public individual names and the optional marker. Each root relation has an unrestricted current row and one closed descriptor evaluated throughout all old components. Quotient descriptors by equality of their actual old traces. Constants receive their own descriptor. Give $d$ the false current bit.

Term closure uses the current lambda table at the root and the descriptor obtained by substituting the finitely many parameter descriptors at all old arrows. No completeness requirement in the expanded language is needed for this equality-of-traces version. Each bulk $\Sigma$-sentence witness remains unchanged, so the root is $\Sigma$-Maximalist. In the special component exchange the two worlds and transport the full typed hierarchy by the induced automorphism. It fixes every name, including $d$ and the marker, so every closed descriptor at type $t$ there is either top or bottom. The scalar algebra itself has four elements, and $\Box\mathrm{ND}_t$ holds. Thus $d$ is nonzero, it is below $B$, and the root satisfies
$$
 \Psi(d)\;:=\;d\ne\bot\ \land\ d\le B\ \land\
 \forall p^t\,\Box\bigl(d\to(p=\bot\lor p=\top)\bigr).
$$
The sentence $\exists d\,\Psi(d)$ lies in the pure language and is consistent with ordinary Maximalism in the actual signature $\Sigma$. The root uses one auxiliary value to witness the existential. The argument allows infinitely many public relation symbols.

#### Two applications of local Barcan

At the putative $\mathrm{SP}_\Sigma+\mathrm{BF}_t$ point $r$, fix any true $a$. Strong possibility of the closed existential gives
$$
 \Diamond\exists d\,(\Psi(d)\land\Diamond a).
$$
Apply dual $\mathrm{BF}_t$ at $r$ to the displayed predicate. It gives a current $d_0$ and arrows $r\to w\to z$ such that $\Psi(d_0)$ holds at $w$ and $a$ holds at $z$, with every parameter transported along its path. Since $d_0$ is nonzero and below $B$ at $w$, a further point from $w$ satisfies $d_0\land B$. The further point has a proposition unequal to both endpoints. In particular the source satisfies $\Diamond\exists p\,(d_0\land B\land p\ne\top\land p\ne\bot)$. A second application of dual $\mathrm{BF}_t$ at $r$ yields an old $p_0$ witnessing this possibility. Hence
$$
 u=d_0\land B\land(p_0\ne\top)\land(p_0\ne\bot)
$$
is nonzero at $r$. It is below $B$ by construction. The universal clause of $\Psi$ at $w$ applies to the transported $p_0$, so $u$ there is bottom. Identity persists to $z$, which realizes $a$.

Vicinity would supply a true $a$ such that $a\le\Diamond q$ for every current true $q$. Apply it to $q=\Diamond u$. By $\Diamond\Diamond u=\Diamond u$, this $u$ would still be possible at $z$. Actuality gives Vicinity. The incompatibility with either of these full native hypotheses already follows from the recorded implications from Vicinity plus local Barcan to two-hat-implies-ND and its incompatibility with signature Strong Possibility. The restriction to $u\le B$ is the extra conclusion here.

The argument does not force $d_0$ or $u$ to remain nonzero on a return chosen using an arbitrary initial $a$. A boxed Barcan assumption has an independent, shorter refutation: even ordinary signature Maximalism sees a possible failure of local Barcan, since a C-countermodel can be given any interpretations for its free constants. No box on Barcan is used in either of the two applications above.

#### A single return through all the finite-size cells

Let $N$ be the Frege numbers at individual type. Set
$$
 B_n=\Box\mathrm{ND}_t\ \land\ \text{there are four propositions}\
     \land\ (\operatorname{Suc}_e n)(\lambda x^e.\top).
$$
Use a separate special two-world component of every standard positive individual size $j$. In each such component use identity transport on the $j$ individuals, assign all individual names to the same chosen individual, assign bottom to every public relation, and give the auxiliary $d$ the value top. The two-world interchange fixes the individuals pointwise. It again forces every present proposition descriptor to have an endpoint value on every $d$-component. The root's full current rows admit its standard numeral cut. The finite components separate the standard numerals, so these are exactly the actual, pairwise distinct members of $N$ there. Consequently the same root witnesses the single sentence
$$
 \exists d\left[
   \forall n\in N\;\Diamond(d\land B_n)
   \ \land\
   \forall p^t\,\Box\bigl(d\to(p=\bot\lor p=\top)\bigr)
 \right].
$$
At this root, $\forall n\in N\,(B_n\ne\bot)$ holds, and $B_n\land B_m=\bot$ for distinct current $n,m\in N$. For the disjointness, the two distinct standard counts cannot count the same instantiated individual universe. These assertions transfer to a signature SP point by universal identity reflection: numberhood is persistent, so its application may be replaced by its identity to top in the universal formula.

At $r$ fix any true $a$ and request a return to $a\land\forall n\in N\,(B_n\ne\bot)$ through the displayed existential. The first application of local Barcan gives the same source $d_0$ for this whole path. Every old $n$ is still a number at $w$. Since $d_0\land B_n$ is possible there, it is possible at $r$. At a realization there are four propositions. Apply source $\mathrm{BF}_t$ to obtain an old $p$ for which
$$
 d_0\land B_n\land(p\ne\bot)\land(p\ne\top)
$$
is possible. This nonzero source element below $B_n$ has become bottom at $w$ and remains bottom at $z$. At both $w$ and $z$ the image of the entire cell $B_n$ remains nonzero. The arrows $r\to w\to z$ were chosen before the arbitrary index $n$. Thus the same Boolean homomorphism from $r$ to $z$ kills a nonzero part of **each** disjoint $B_n$, including when the starting arithmetic is nonstandard, and preserves the nonzeroness of every entire cell. No simultaneous choice of the $p$'s as an internally represented function is needed.

The model and the two Barcan steps were checked by independent GPT-6 research agents on 27 November 2026.
