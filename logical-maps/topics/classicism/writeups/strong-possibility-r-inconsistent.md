# Strong Possibility (pure) ⇒ ⊥ (conjecture)

The consistency of pure Strong Possibility (SP) remains open. An SP root
with Actuality would require elementary returns through every individually
Max-consistent pure sentence. Many such returns can be modeled together,
even when the returning atom splits along the way. These are ordinary
arguments by OpenAI GPT-6, prompted by Daniel Kodsi and independently
reviewed by a second GPT-6 research agent on 26 November 2026.

## A restriction on the Russell–Myhill argument

The [signature argument](strong-possibility-signature-r-inconsistent.html#the-sentences) uses a closed operator $Q:(t\to t)\to t$. Put $\rho(p)=\exists F\,(QF=p\land\neg Fp)$ and $d=Q\rho$. Classicism proves there is a collision witness $F$ with $QF=d$ and $Fd\ne\rho d$. The two existential sentences $E_1,E_2$ ask whether such a witness can respectively agree or disagree with $\rho$ at $\top$. To use them against pure SP, each sentence must fail in some pure Max model.

Suppose there are finitely many fixed closed pure propositions $r_i$ and C proves $QF=QG\leftrightarrow\bigwedge_i Fr_i=Gr_i$ for all $F,G$. This includes evaluation at any single closed proposition. **No such $Q$ gives the required split.** Indeed C proves $d\ne r_i$ for each $i$, since a collision witness must agree with $\rho$ at $r_i$ and disagree at $d$. At a Max point, two closed pure terms are identical exactly when C proves their identity. Otherwise Max realizes their possible distinctness, whereas identity would persist. Thus the equalities of $d$ and of each $r_i$ with $\top$ are settled uniformly across all Max points. If $d=\top$, $E_1$ fails everywhere and $E_2$ holds everywhere. If any $r_i=\top$, the reverse holds.

In the remaining case both sentences hold at every Max point. Write $A(p)=\bigwedge_i p\ne r_i$. Obtain $F_1(p)$ from $\rho(p)$ by exclusive disjunction with $(p=d\land p\ne\top\land A(p))$, and $F_2(p)$ by exclusive disjunction with $((p=d\lor p=\top)\land A(p))$. Both guards are identically false on each probe, so $QF_1=QF_2=d$. Both flip the truth value at $d$. The first preserves the whole proposition $\rho(\top)$, and the second flips its truth value at the current point. These witnesses also explain why finite observations at fixed probes leave the unrestricted Russell–Myhill question open.

## Elementary returns

Let $a$ witness Actuality at $x$. For any current proposition $p$,
$\Diamond_{\ne}p$ holds at $x$ iff there are arrows
$f:x\to y$, $h:y\to z$ with $fp$ true at $y$ and $hf(a)$ true at $z$.
Indeed the definition tests each true $q$ for
$\Diamond(p\land\Diamond q)$. Use $q=a$ in one direction; in the other
direction $a$ entails every such $q$. On any such return $hf$ preserves
and reflects every native formula with parameters of every type at $x$.
Apply the truth observation to the formula and its negation, and use
transport of term values. Conversely an elementary composite through a
$p$-point returns the truth of $a$. At $z$ its transported value again
witnesses Actuality, including for newly available propositions.
An SP point therefore returns to another SP point in this situation.
One can iterate through any prescribed countable sequence of individually
Max-consistent closed sentences, in the same model.

Without Actuality, fix a finite menu $P_1,\ldots,P_k$ of such sentences.
The closed $Q=\bigwedge_i\Diamond_{\ne}P_i$ holds at an SP point.
Wherever $Q\land q$ holds, test $\Diamond_{\ne}P_i$ against $Q\land q$.
Some path through $P_i$ returns to $Q$ with the transported $q$ true.
This realizes arbitrary infinite words over the menu while preserving
any specified finite diagram of current parameter truths at the returns.
Further true parameters can be added after each return.

## Uniform numerical consequences of SP

Write $F$ for the Fregean Axiom, $E_j$ for exactly $j$ individuals and
$E^t_j$ for exactly $j$ propositions. For positive integers $d,m$, put
$B_{d,m}=\Box\mathrm{ND}_t\land\Box E_d\land\Box E^t_{2^m}$.
Let $N=\mathbb N_e$, let $U=\lambda x^e.\top$, and write
$J(n)=(\operatorname{Suc}_e n)(U)$. At the standard numeral $k$,
$J(k)$ says there are exactly $k+1$ individuals. If $r\ne\bot$
and $r=\Diamond r$, SP entails that the single term
$n\mapsto r\land J(n)$ gives pairwise disjoint nonzero propositions
for **all** $n\in N$. The single term $n\mapsto F\land J(n)$
also gives pairwise disjoint weak atoms for all $n\in N$. These
quantifiers include nonstandard numbers. The October calculation
gave each externally indexed finite Fregean cell separately.
[Finite Fregean cells, §§3–4](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/sp-structural-proof-package/profile-root-construction-20261022.md#L21)

The transfer uses universal Boolean combinations of typed identities.
If one of these sentences fails, its countertuple witnesses a finite
identity diagram. True identities persist. Let $q$ be the conjunction
of its true disequalities. Wherever transported $q$ remains possible
those disequalities still hold, by necessity of identity. Thus a
countertuple prevents the sentence from holding under $\Diamond_{\ne}$.
Consequently SP entails every individually Max-consistent sentence
of this form. In C, $N(n)$ is persistent and hence equivalent to
$N(n)=\top$. Nonzeroness, disjointness and the definition of a weak
atom all have the required identity form, universally quantifying
over a possible subproposition in the atom condition.
[Universal reflection, §§2–4](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/sp-structural-proof-package/reflection-universal-core-20261022.md#L11)

For the first claim choose one individual set $X_j$ of each positive finite
size $j$, with all functions between these sets as arrows and exits into a C-complete family of
old components. From $X_j$ to an old object use all $j$-tuples of
individuals there, postcomposing by transport. At each new relational
type give an entity unrestricted rows on all its internal arrows and a
single old descriptor with $j$ free individual markers, evaluated at
the tuple of the exit. Internal transport precomposes the rows and
substitutes the markers according to the individual map. Take old
components complete also for formulas with finitely many markers.
Equality of the old traces is then provable descriptor equality.
The lambda and quantifier check uses the transported parameters at
each internal target and substitutes their descriptors at old targets.
Every new point satisfies Max. At the singleton $X_1$, $N$ is exactly
the standard numeral values by the unrestricted current row argument.
A nonzero possibility-fixed $r$ is true there. Each section
$X_1\to X_j$ has a return, so transported $r$ is possible at $X_j$,
hence true there. This realizes $r\land J(j-1)$. Different standard
sizes are disjoint at every world, giving the universal sentence at
$X_1$.

For the second claim use the ordinary singleton definable root. Its
current numbers are again standard. In a Fregean world of fixed
positive finite individual size the extensional hierarchy is full by
finite comprehension. Permutations of its individuals act transitively
on interpretations of the single marker. Each proposition descriptor
therefore has constant value on the entire cell $F\land E_j$; the cell
is false at the root and possible on an old exit. It is consequently
an atom. All these standard-index assertions hold at the same Max
point, so universal reflection gives the claim on its full internal
index set at every SP point.

A third represented injection concerns any current operator
$H:\sigma\to\rho$ with relational output. There are $N$-many distinct
operators agreeing with $H$ in their output *entities* at every current
input. Put $b(n)=\Box\mathrm{ND}_t\land\Box((\operatorname{Suc}_e^2
n)(U))\land\Box E^t_4$. At standard $k$ this is $B_{k+2,2}$.
For relational $\sigma$, let $S_\sigma$ be the October term lifting
the swap of the two atoms of the four-element proposition algebra,
and put $T_n(X)=K_\rho(b(n)\land S_\sigma(X)\ne X)$, where $K_\rho$
lifts a proposition constantly. On a $b(k)$-cell the swap acts
trivially on individuals and lifts by conjugation through each type,
fixing every descriptor with its individual marker. A moved
proposition, lifted constantly to $\sigma$, witnesses nonzeroness
there. Thus at the singleton definable root $T_k$ is nonzero but
$T_k(X)=\bot_\rho$ for every current $X$. For $\sigma=e$ take instead
$T_n(x)=K_\rho(b(n)\land x\ne a)$ with its sole current individual
$a$; the use of $k+2$ supplies distinct individuals in the finite
cell. Different $k$ give disjoint operators. The uniform statement
about nonzeroness, disjointness and current vanishing again consists
of universal Boolean combinations of identities; universally close
$a$ in the individual case. Reflection transfers it to all $n\in N$.
The required injection is $n\mapsto H\mathbin{\triangle}T_n$, by
Boolean cancellation. The archive proved each external finite
multiplicity bound; the displayed term indexes the entire internal
family. [Finite-cell operators, §§19 and 25](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/sp-existential-products-20261022.md#L948)

## Purely definable atoms for finite fragments

The October research proves that pure SP forces
each $\mathrm{Atom}(B_{d,m})$ and that the singleton profile model
satisfies these sentences together with pure Max.
[Finite homogeneous cells, §§17.1–17.5](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/sp-existential-products-20261022.md#L532)

Let $\Gamma$ be a finite conjunction of ordinary possibility axioms
of pure Max. There is a model of $\Gamma$ and *all* these cell-atom
sentences with a singleton individual domain and a true atom named by
a closed pure term. It can have literal returns through every positive
finite individual cardinality and an arbitrarily wide split of that atom
on one return path.

To find two separated old components, take the consistent recursively
enumerable theory
$$
 T=C+\Gamma+\Diamond\neg F+
              \{\mathrm{Atom}(B_{d,m}): d,m\ge1\}.
$$
Some consistent $\eta=F\land I_e^*\land\theta$ has
$T+\neg\Diamond\eta$ consistent. Here $I_e^*$ is the arithmetic
Peano condition on the Frege numbers at $e$. Otherwise, for each
sentence $A$, dovetail proofs of $A$ in $C+F+I_e^*$ and proofs of
$\Diamond(F\land I_e^*\land\neg A)$ in $T$. Exactly one search
would succeed, deciding the former theory. Its undecidability already
follows from first-order validity with a binary relation. Relativize
to a nonempty unary predicate, universally bind both predicates,
and expand any counterstructure to a full classical one-world
hierarchy over an infinite domain containing the counterstructure.
Completeness of first-order logic gives the positive direction.

Choose an old point $w\models T+\neg\Diamond\eta$ and an old
point $u\models\eta$, in disjoint components. All successors of $w$
miss $\eta$. All successors of $u$ are Fregean and satisfy $I_e^*$:
at a Fregean point each true proposition equals top. In particular
their individual domains are externally infinite, since no standard
finite domain in a Fregean cone with $I_e^*$ satisfies the Peano
condition.

For any $l\ge2$ use two objects $r,s$ with a map $f:r\to s$ and
distinct $g_i:s\to r$ ($1\le i\le l$), with $g_i f=1_r$.
The other maps are identities and $e_i=fg_i:s\to s$; composition
reduces by these equations. Take the product of this category with
the category of nonempty finite sets and functions, using one
representative $X_j$ of each size $j$. The individuals at $(X_j,t)$
are $X_j\times D_t$, where $D_r$ is a singleton and $D_s$ a doubleton;
$f$ picks a point and the $g_i$ collapse $D_s$ to the singleton.
Use all these product maps as internal arrows. Add one entrance
from each new object to each of $w,u$ and all its old postcomposites,
indexed by their old arrows. Internal precomposition changes only the
source of an entrance. Send every individual to a fixed chosen
individual of the appropriate old point. These constant maps respect
the composition rule.

At a new object a relational entity has an unrestricted extension row
for every outgoing internal arrow, together with one whole old value
of its type at each of $w,u$. The empty tuple gives proposition rows.
Internal transport precomposes the row table and keeps the old values;
entrance transport takes the appropriate old value. At an old
postcomposite apply its original transport. The domains are defined
inductively in the argument types. A lambda has on each internal arrow
the row given by evaluating its body on transported parameters and
all arguments then available. Its two old values are the original
lambda values on the respective transported parameters. Induction on
terms gives the required transport equation, including quantifiers
over the full target domains. Old domains and arrows out of old points
stay as in the two original components. This is the old finite-set
retraction construction with a second, explicitly split, factor.
[October retraction construction, §§1–3](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/sp-structural-proof-package/reflection-retract-fragments-20261022.md#L11)

Put $R=(X_1,r)$ and
$c=\Diamond\eta\land\Diamond\neg F\land E_1$.
The first two conjuncts hold at each new object and jointly at no
old successor. The individual condition selects just $R$. Consequently
the row of $c$ out of $R$ is true only at its identity: $c$ is its
actual atom. At $(X_1,s)$ the rows where $c$ is true are exactly the
$l$ arrows $g_i$ to $R$. The interval below its transported value has
$2^l$ elements, since each mask on those rows is admitted. Each
$g_i f$ returns by the identity. For every $j\ge1$, choosing any
point of $X_j$ gives a section $R\to(X_j,r)$ with a literal return
to $R$. At $R$ the Frege numbers $\mathbb N_e$ are exactly the
standard numeral values: arbitrary current rows admit the set of those
values as an inductive predicate, and the finite objects distinguish
every pair of standard numerals. Thus even the internal universal
quantification over finite cardinalities in the next paragraph holds
there. The $\Gamma$-diamonds follow from the entrance to $w$.
Each $B_{d,m}$ is false at all internal objects, all of which see $u$,
and impossible at $u$. Its only nonbottom coordinate at $R$ is its
old atom at $w$, so it is an atom at $R$.

## A single source proposition spanning the full Max theory

Every pointed pure Max model has an elementary extension of its
action-and-evaluation structure in which the original point admits
a nonzero self-atom $b$ with all the following properties throughout
its truth set.

* Every $b$-point satisfies pure Max, $E_1$, $\neg F$ and every
  $\mathrm{Atom}(B_{d,m})$. There $b$ witnesses Actuality.
* For every $n\in\mathbb N_e$ at a $b$-point there is a path through
  $(\operatorname{Suc}_e n)(\lambda x^e.\top)$ and back to a
  $b$-point. At the intermediate point the number parameter is
  transported. For each standard $l$ there is also a path through
  a point where $b$ has at least $l$ pairwise disjoint nonzero parts,
  and back to $b$. All these returns are elementary on the parameters
  at the starting $b$-point by the first section.

For the finite satisfiability check, let $G(z)$ conjoin finitely
many requested local conditions, including the desired diamonds with
$z$ marking the return. In the construction above choose $l$ large
enough. At $R$, $c$ is the actual atom and $G(c)$ holds. Set
$d=c\land\mathrm{Atom}(c)\land G(c)$. As a matter of C alone,
at any $d$-point the nonzero $d\le c$ must equal the atom $c$
as a proposition, giving both $\mathrm{Atom}(d)$ and $G(d)$ there.
This equality also justifies occurrences of $d$ *inside* the return
diamonds. Since $d$ is a C-consistent closed pure proposition, every
Max point has $\Diamond d$. Its local $d$ is therefore a self-atom
satisfying the finite list of entailments $d\le G(d)$. Compactness
with the elementary diagram of the given model supplies one new
$b$ for the entire list. This uses many-sorted first-order
presentations of Henkin action models, with the usual evaluation
translation for each standard typed formula.

No fixed closed pure term can name a true atom at a Max point.
If $c$ did so, it would entail each pure Max axiom $K$ there.
This entailment is a closed pure identity, so it is already provable
in C: failure of the identity is C-consistent and Max would otherwise
require its possibility, contrary to necessity of identity. Then the
consistent recursively enumerable theory $C+c$ would entail pure Max.
The October argument excludes this by dovetailing C identity proofs
and proofs of their Max disequalities.
[Non-effective axiomatizability, §§9–10](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/sp-essential-extension-20261022.md#L95)

The extension thus supplies a source proposition whose realizations
meet the entire Max theory and return conditions above. SP also
requires returns through arbitrary Max-consistent higher-order
sentences. Their simultaneous realization remains open.
