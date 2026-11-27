# Strong Possibility (pure) ⇒ ⊥ (conjecture)

The consistency of pure Strong Possibility (SP) remains open. An SP root
with Actuality would require elementary returns through every individually
Max-consistent pure sentence. Many such returns can be modeled together,
even when the returning atom splits along the way. These are ordinary
arguments by OpenAI GPT-6, prompted by Daniel Kodsi and independently
reviewed by a second GPT-6 research agent on 26 November 2026.

## A restriction on the Russell–Myhill argument

The [signature argument](strong-possibility-signature-r-inconsistent.html#the-sentences) uses a closed operator $Q:(t\to t)\to t$. Put $\rho(p)=\exists F\,(QF=p\land\neg Fp)$ and $d=Q\rho$. Classicism proves there is a collision witness $F$ with $QF=d$ and $Fd\ne\rho d$. The two existential sentences $E_1,E_2$ ask whether such a witness can respectively agree or disagree with $\rho$ at $\top$. To use them against pure SP, each sentence must fail in some pure Max model.

Suppose $R$ is a closed pure property of propositions and C proves, for all $F,G$,
$$
 QF=QG\quad\longleftrightarrow\quad
 \forall p\,(Rp\to Fp=Gp).
$$
Then these observations cannot produce the split. The probes may form an internally infinite family, and membership in $R$ may change along an arrow.

To see this, note that $d=\top$ has the same verdict at every pure Max point. If C proves the identity it holds everywhere. Otherwise its negation is C-consistent, so Max requires its possibility, which is incompatible with a current identity. If $d=\top$, the unavoidable collision witnesses $E_2$ at every Max point. Suppose instead that $d\ne\top$. Choose $F$ with $QF=d$ and with $Fd$ opposite in current truth value to $\rho d$. Such an $F$ exists since the diagonal first gives $\rho d$, and its definition then supplies the witness. With $\mathbin{\triangle}$ for exclusive disjunction, set
$$
 G(p)=\rho(p)\mathbin{\triangle}
       \bigl((F(p)\mathbin{\triangle}\rho(p))\land p\ne\top\bigr).
$$
At every current probe $p$, $Fp=\rho p$ as propositions, so their exclusive disjunction is the bottom proposition. Thus $Gp=\rho p$ as propositions at every probe and $QG=d$. Also $G\top=\rho\top$ identically. At $d$ the guard is currently true, hence $Gd$ differs in truth value from $\rho d$. This witnesses $E_1$ at every Max point. In either case one of the two sentences holds throughout the class, whereas Dorr's argument requires each to fail somewhere.

For finitely many named closed probes $r_i$, use $R(p)=\bigvee_i p=r_i$. This includes an operator that evaluates its argument at a single fixed proposition. In this finite case there is a further classification. A collision forces $d\ne r_i$ for each $i$. If a probe equals $\top$, any collision witness agrees with $\rho$ at $\top$, so only $E_1$ holds. If $d$ differs from $\top$ and every probe differs from $\top$, both sentences hold. To witness $E_2$, flip $\rho(p)$ by exclusive disjunction with $((p=d\lor p=\top)\land\bigwedge_i p\ne r_i)$. This leaves every probed output unchanged as an entity and changes the current truth values at both $d$ and $\top$.

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

## Returning individual cardinalities and scalar coding at an actual atom

Let $N=\mathbb N_e$, $I=I^*_e$ and $U=\lambda x^e.\top$. Write $J(n)=(\operatorname{Suc}_e n)(U)$. At the standard numeral $j$, this says that exactly $j+1$ individuals exist. All statements below quantify over the full current $N$.

### Pure Strong Possibility realizes every positive finite size on a return

There is a pure Maximalist point satisfying the single sentence
$$
 \Theta=I\land\forall n\,(Nn\to\Diamond_{\ne}J(n)).
$$
For the existence claim, use the [construction of a single proposition spanning the full Max theory](strong-possibility-r-inconsistent.html). In an elementary extension of a pure Max model it gives a possible self-atom $b$. At every point where $b$ is true, pure Max and the Peano guard hold, and each local $n\in N$ admits a path through $J(n)$ back to $b$. Since $b$ is the actual atom there, these are precisely the required distinctness-preserving possibilities. Choose one such point.

Suppose $r$ satisfies pure Strong Possibility. The preceding consistency certificate gives $\Diamond_{\ne}\Theta$. Take any $n\in N$ and any true $q$ at $r$. Reach a $\Theta$-point where $\Diamond q$; numberhood persists along the entrance. At that point apply the $n$-instance of $\Theta$ using the current truth $\Diamond q$ as its test. This reaches $J(n)$ with $\Diamond\Diamond q$, hence with $\Diamond q$ by transitivity. This proves $\Diamond_{\ne}J(n)$ at $r$. Pure Max already gives $I$ there.

### An actual atom encodes number predicates in propositions

Let $a$ be a true atom at $r$. For each $n\in N$ define $C_n=J(n)\land\Diamond a$. These propositions are nonzero by testing the preceding result with $a$. Every $a$-point has the same parameter truths as $r$: a true atom entails each current truth, including any formula in any current tuple and the negation of each false formula. In particular $a\le I$. At every $C_n$-point $I$ is therefore possible and hence holds, by the Peano guard's equivalence to its ordinary possibility at type $e$.

For a current predicate $X$ on the number type, set
$$
 s_X=\exists k\,\bigl(Nk\land J(k)\land\Diamond a\land(a\le Xk)\bigr).
$$
This is a single native term in $a,X$. At every $C_n$-point the transported $n$ satisfies $Nn$ and $J(n)$. If any number there, including one new to that point, satisfies $J(k)$, its successor and the successor of the transported $n$ both count $U$. [Numbers with a common instance are identical](../index.html#background/arithmetic). The Peano guard gives successor injectivity there, so $k$ equals the transported $n$. In particular the existential cannot introduce a spurious sign. At $r$ either $a\le Xn$ or $a\le\neg Xn$ according to the current truth of $Xn$. The order identity persists, and $a$ is nonzero at every $C_n$-point. Thus throughout $C_n$ the bit of $s_X$ is exactly the current bit of $Xn$.

If $X$ and $Y$ agree currently on every number, the identity
$$
 a\le\forall k\,(Nk\to(Xk\leftrightarrow Yk))
$$
holds at $r$. At any later point and any $k$ satisfying $Nk$ there, numberhood persists throughout its future. The identity therefore gives $a\land Xk=a\land Yk$ at that point. It follows directly from the definition that $s_X=s_Y$. Conversely, a current disagreement at $n$ gives opposite bits on the nonzero $C_n$, so $s_X\ne s_Y$. The closed abstraction in the parameter $a$ thus embeds the extensional equivalence classes of current predicates on $N$ into the scalar domain.

Consequently there is no current relation which functionally enumerates all scalar entities by $N$. Indeed, suppose $E(n,p)$ were such an enumeration, and form the admitted predicate
$$
 X(n)=\neg\exists p\,(E(n,p)\land C_n\le p).
$$
Choose a current $j\in N$ with $E(j,s_X)$. Functionality gives $Xj$ exactly when $C_j\nleq s_X$, whereas the proven bit rule and $C_j\ne\bot$ give $Xj$ exactly when $C_j\le s_X$. An injection of all scalars into $N$ would give a functional enumeration by reversing its graph and assigning bottom to unused numbers, also impossible. This is internal uncountability at the actual point, with counts measured at individual type. A countable Henkin presentation externally is compatible with this conclusion. Ordinary pure Max admits the opposite internal verdict at its countable-scalar definable root, whose unrestricted current graph enumerates its scalars with the standard individual Frege numerals.

### A real number structure on propositions

Take the pairwise distinct nonzero $b_n=\mathrm{Fr}\land J(n)$ of the [pure SP finite-cell argument](strong-possibility-and-boolean-completeness-t-incompatible.html) as number labels, and the $s_X$ as real labels. These two classes of labels are disjoint. Every $s_X$ entails $\Diamond a$. At an $a$-point the Fregean Axiom is false, since it is already false at the source by Maximalism and $a$ entails each actual truth. At a Fregean point the axiom persists, excluding $\Diamond a$. Thus even the zero real label differs from each nonzero $b_n$.

Define the two carriers by their displayed images, equip the first with the zero and successor coming from $N$, and put $b_n\in s_X$ exactly when $Xn$. All these are current relations supplied by abstraction. The classification of the $s_X$ makes membership well defined and gives real extensionality. For every current property $P$ of number labels the predicate $n\mapsto P(b_n)$ supplies the real coding its extension. A current inductive subproperty of the number labels pulls back to an inductive subproperty of $N$, so the number part satisfies Peano induction. This is an actual membership-presentation real structure at type $t$. In the ordinary pure descriptor Max root, $D_t$ is externally countable and the current rows include every subset of every number part, so no real structure at $t$ is possible *as an actual structure at that root*.

The returning sizes, the treatment of newly available numbers, the enumeration obstruction and this real-structure corollary received a separate GPT-6 mathematical review on 27 November 2026.

## Internal proof reflection and true arithmetic at the second level

Write \(N=\mathbb N_e\) and \(I=I_e^*\). Fix a pure formula \(A(v)\)
whose only free parameter is a Frege number variable. Let \(L_A(n,k)\)
be the primitive recursive proof check that \(k\) is a C-refutation of
\(A(\bar n)\). Use the effective pure C calculus, annotating axiom
instances by their enumeration certificates if necessary. The
function producing the syntax of the Frege numeral is primitive
recursive. This is one fixed PA graph, including at nonstandard
arguments.

At every pure SP point,
\[
 \forall n\in N\quad
 \big(\neg\Diamond A(n)\ \longleftrightarrow\
                   \exists k\in N\, L_A(n,k)\big).
\]
The modal formula has \(n\) as an actual parameter. The proof check
on the right operates inside the source arithmetic; for nonstandard
\(n,k\) it is not a claim about an external finite derivation.

The displayed sentence, together with \(I\), holds at the standard
singleton descriptor Max point \(V\). All its numbers are standard,
and for each standard numeral a closed sentence is possible there
exactly when it is C-consistent. Pure SP therefore supplies
distinctness-preserving possibility of that one uniform sentence.
Every SP point also satisfies \(I\).

Suppose \(A(n)\) is impossible at the source without an internal
refutation. Request a return to \(I\land\neg\exists k\in N\,L_A(n,k)\)
through the displayed sentence with its Peano guard. The source
identity \(A(n)=\bot\) persists to the intermediate point, and the
sentence supplies a refutation code there. Its numberhood and its
primitive recursive proof check persist to the Peano return, contrary
to its guard.

If \(A(n)\) is possible and \(L_A(n,k)\) holds at the source, request
a return to \(\Diamond A(n)\) through the same Peano sentence. The
primitive recursive proof check is preserved from source to
intermediate, so \(A(n)=\bot\) there. This persists to the return,
contrary to possibility of \(A(n)\). This proves the equivalence
for all internal indices. Multiple numerical parameters can be
treated together. Taking \(A(v)\) to assert a failure of identity
also gives a uniform numerical test for identity of two fixed
parameterized pure terms in the source.

The same method proves that the source arithmetic satisfies every
true first-order \(\Pi^0_2\) sentence. Write the sentence in the
form \(\forall n\exists m\,R(n,m)\) with a primitive recursive
matrix. It holds at \(V\). If an actual \(n\) of the source had no
witness, request a return to \(I\land\neg\exists m\in N\,R(n,m)\).
At the intermediate Peano point choose \(m\) and carry it to the
return. Its PA graph and numberhood are preserved, a contradiction.
In particular any standard program which really halts on every
standard input is internally total on the source natural numbers.
No assertion about correctness of every arithmetical sentence, or
about arithmetic in all accessible worlds, is needed.

The arithmetic transport fact used here is proved in the
[finite-cell Boolean Completeness argument](strong-possibility-and-boolean-completeness-t-incompatible.html).

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026.

## Returns with an unbounded increase at both steps

There is a single true arithmetic \(\Pi^0_2\) sentence
\(\Phi=\forall n\exists m\,R(n,m)\), with primitive recursive
\(R\), with the following property. In every model of pure Strong
Possibility, and in every model of signature Strong Possibility for
any signature, each current truth \(q\) has a round trip through
\(I\land\neg\Phi\) to a point satisfying \(q\land I\land\Phi\).
Each of the two arithmetic embeddings along this round trip has
noncofinal image. One may continue making such trips from the return
point while keeping the original \(q\) true at successive returns.

Choose a computably presented countably infinite signature
\(\Omega\) with infinitely many symbols of each type. The axioms of
\(T=\operatorname{Max}_\Omega(C)+I\) can be enumerated using the
halting problem as an oracle, since the ordinary C calculus is
effective and its consistency tests concern single formulas. The
signature-definable Maximalist root has exactly the standard
\(e\)-numerals as its numbers. Its unrestricted current predicates
include a test for exactly these numerals. This test is inductive
at the root, and the possible finite Fregean sizes distinguish the
different standard numerals. Thus all arithmetic consequences of
\(T\) hold in the standard natural numbers. The true \(\Pi^0_2\)
sentences are not computably enumerable with the halting oracle,
so some true \(\Phi\) of the stated form is unprovable in \(T\).

For any signature \(\Sigma\), the sentence \(P=I\land\neg\Phi\)
is consistent with \(\operatorname{Max}_\Sigma(C)\). Otherwise a
proof of \(\Phi\) from \(\operatorname{Max}_\Sigma(C)+I\) uses only
finitely many symbols. A type-preserving injection of those
symbols into \(\Omega\) carries each used Max axiom to a Max axiom.
Indeed satisfiability of a formula in a finite vocabulary is
preserved when further unconstrained names are introduced. The
renamed proof would contradict the choice of \(\Phi\). The same
argument covers the pure vocabulary. Conversely the standard
numeral root for any \(\Sigma\) satisfies \(I\land\Phi\), so the
earlier two-step proof of true \(\Pi^0_2\) reflection also works
for signature Strong Possibility, using its own reference theory.

At the Strong Possibility source, request a return through \(P\) to
the truth \(q\land I\land\Phi\land\Diamond_{\ne}P\). At the
intermediate point choose a number \(k\) with no witness to
\(R(k,m)\). For each original number \(a\), PA and \(\Phi\) give
an original number \(c\) with
\(\forall i\le a\,\exists j\le c\,R(i,j)\). This last assertion
is a bounded primitive recursive test on \(a,c\). Its value is
preserved between the two Peano points, even if new numbers occur
below the image of an old number. Consequently \(k\) is greater
than the image of every source number. At the returning Peano
point choose \(y\) witnessing \(R(k,y)\). For each number \(b\)
at the intermediate point the bounded test
\(\forall j\le b\,\neg R(k,j)\) is true and remains true at the
return. Thus \(y\) exceeds every image from the intermediate point.
The specified return truth again includes \(\Diamond_{\ne}P\),
which permits iteration of the same test without assuming the
entire Strong Possibility schema at each successive return.

In particular a model with standard arithmetic at all its Peano
points cannot realize either form of Strong Possibility. This
obstruction applies even in the absence of a true atom. The bounded-computation transport used above is the one established in the [finite-cell argument](strong-possibility-and-boolean-completeness-t-incompatible.html). An independent researcher checked both embeddings and the finite renaming argument for the common choice of \(\Phi\).
