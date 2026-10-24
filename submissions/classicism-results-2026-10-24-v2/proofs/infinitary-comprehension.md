# Infinitary Comprehension and full standard models

23 October 2026. Original mathematical development by OpenAI Codex, prompted
by Daniel Kodsi. Direct source for the new arguments: `misc`, the numbered
sections below, unpaginated. The inherited finite reconstruction and observer
theorems are identified at their points of use.

Infinitary Comprehension is ordinary boxed Comprehension with classical
infinitary formulas admitted as matrices. Together with C5, it characterizes
the full standard relational hierarchies. Atomicity is a consequence of the
infinitary logical resources, so it need not be separately assumed. The
principle keeps the shape of ordinary Comprehension while allowing genuinely
infinitary specifications of a relation's entire intension.

The results concern ordinary set-sized models in ZFC. Structural arguments
are distinguished from consequences that use an external choice function.
The assertion that a fixed syntactic scheme has a certain class of models
is separate from completeness of a proof calculus for that class.

## 1. Language and principle

Keep the original relational types: base types e and t, and sigma to rho
only when rho is relational. Every relational type has the form
$\sigma_1\cdots\sigma_n t$, for a finite, possibly empty tuple.
Application $R[\bar x]$ is explicitly left-nested. There are no
individual-output operation types and no infinitary-arity relation types.

Start with the established lambda-free base $B_0$: classical typed
applicative logic, equality, primitive formula constructors and object
quantifier binders, top, a first-class $b:tt$, K, theorem-only
necessitation, and Intensionality at every relational type:

$$
 \Box\mathrm{coext}_\rho(X,Y)\longrightarrow X=Y,
 \qquad \Box A:=b(A).
$$

Here $\mathrm{coext}_t(p,q)$ is $p\leftrightarrow q$, and
coextension at an arrow type universally quantifies its argument and then
uses coextension at the output type. The exact finite base is specified in
[Lambda-free reconstruction, sections 1–2](lambda-free-reconstruction.md).
Comprehension is removed from that base before the new scheme is added.

Extend the term grammar by arbitrary set-sized conjunctions and disjunctions
of terms of type t. Syntax trees are well founded and set sized. Object
quantifier binders in matrices remain finitary; arbitrary Boolean nesting
is permitted. Allow arbitrary set-sized families of free typed parameters.
Each expression has only a set of parameters, but there is no fixed bound
on their number. This parameter convention is part of the proposal; one
must not replace it by a convention allowing only finitely many free
variables in an infinitary formula.

Use ordinary classical infinitary logic, including its local conjunction
introduction and disjunction elimination rules, with the ordinary modal
interpretation of necessity. Two logical laws used explicitly below are

$$
 \bigvee_{\epsilon\in 2^I}\bigwedge_{i\in I}p_i^{\epsilon(i)},
 \qquad p_i^1=p_i,\quad p_i^0=\neg p_i,
 \tag{1.1}
$$

$$
 \Box\bigwedge_{i\in I}A_i
 \ \leftrightarrow\ \bigwedge_{i\in I}\Box A_i.
 \tag{1.2}
$$

The first says that one complete truth pattern obtains. These are logical
theorems, eligible for necessitation. Ordinary infinitary truth clauses
are retained: a conjunction is true at an evaluation point exactly when
every conjunct is true there. Merely equipping a Boolean-valued structure
with arbitrary joins is a different proposal. Equations (1.1)–(1.2) are
highlighted consequences of the chosen logic, not an asserted complete
axiomatization of that logic.

**Infinitary Comprehension** is the schema

$$
 \boxed{\quad
 \exists R^{\sigma_1\cdots\sigma_n t}\;
 \Box\forall x_1\cdots x_n
       \bigl(R[\bar x]\leftrightarrow A\bigr).
 \quad}
 \tag{Comp-infinity}
$$

The matrix A is any formula of this language; R is not free in A. All its
other free variables are parameters, and the instance is required for
every simultaneous assignment of them. Equivalently, universally close
that entire family before the existential witness, allowing the matching
set-sized block for this closure. Open instances avoid adding such blocks
inside the matrix grammar.

The schema is fixed syntactically, independently of any model. It mentions
neither a domain nor a truth set nor standardness. Its dependence on a
metasyntactic matrix is the same kind of dependence as ordinary
Comprehension. Because A is a proposition term, its box is the existing
b(A), not a newly introduced assertion-level operator.

Write $\mathcal T_\infty$ for $B_0$, this infinitary logic, and
Comp-infinity. The old finite Comprehension instances reconstruct C by the
finite reconstruction theorem. This does not change C's original
H-theoremhood gate or authorize necessitation of optional local premises.
When comparing with C alone below, its Comprehension instances are
restricted to the original finitary language.

## 2. What comes from the infinitary language

Two propositional consequences precede the nonempty-arity Comprehension
instances. The empty-tuple instance itself is immediate: choose R=A and
necessitate the logical theorem $A\leftrightarrow A$.

**Theorem 2.1.** The infinitary propositional language with the stated
logical laws and Intensionality forces arbitrary propositional joins and
meets, propositional Atomicity, and Actuality.

**Proof.** Work in the current identity quotient of the proposition domain,
whose finite Boolean identities follow by necessitating classical logical
equivalences and applying Intensionality. For a
family $(p_i)$, its disjunction is an upper bound in algebraic entailment.
If every $p_i\le q$, then every $\Box(p_i\to q)$ holds. By (1.2)
and disjunction elimination, $\Box((\bigvee_i p_i)\to q)$ holds.
Thus the disjunction is the least upper bound. Complements give meets.

For Atomicity, in a particular set-sized model index the current proposition
entities by I and assign parameters $p_i$ to them. For each
$\epsilon\in2^I$, form the admitted proposition

$$
 a_\epsilon=\bigwedge_{i\in I}p_i^{\epsilon(i)}.
 \tag{2.1}
$$

It lies below either p or its complement for every current p. If
$0<q\le a_\epsilon$, the negative sign at q would imply q=0;
the positive sign gives $a_\epsilon\le q$. Hence every nonzero
$a_\epsilon$ is an atom. Necessitating (1.1) and using Intensionality
shows that their join is top. If a nonzero p contained no atom, every
$a_\epsilon$ would lie below $\neg p$, contradicting that join.

Finally let T index all current true propositions. Their conjunction c
is true by the ordinary infinitary truth clause, and $c\le p$ for
every current true p. Thus c witnesses Actuality. In fact c is an atom:
it decides every proposition by current classical bivalence, and its
truth makes it nonzero. This establishes the theorem. QED.

The proof selects instances of a previously fixed schema when inspecting
a model. It does not place that model's domain in the formulation of the
axiom. It establishes semantic entailment for all set-sized models, not a
single fixed set-sized derivation covering all possible domain cardinalities.

## 3. Comprehension at relational types

**Theorem 3.1.** $\mathcal T_\infty$ gives arbitrary joins and meets
and Atomicity at every relational type. In particular it gives Arbitrary
Atomic Joins and the original internal Boolean Completeness schema.

**Proof.** For $\tau=\bar\sigma t$ and any family $(F_i^\tau)$,
Comprehension represents $\bigvee_iF_i[\bar x]$. The boxed defining
equivalence makes its witness an upper bound. If Y bounds every F_i,
combine the formulas $\Box\forall\bar x(F_i[\bar x]\to Y[\bar x])$
using (1.2), and apply disjunction elimination inside the box. This makes
the witness the least upper bound. The dual gives meets.

For Atomicity, index the current entities of type tau by I. Represent
each complete signed pattern
$\bigwedge_iF_i[\bar x]^{\epsilon(i)}$ by a relation
$a_\epsilon$. The boxed defining equations imply that each
$a_\epsilon$ decides every F_i in algebraic order. Thus each nonzero
one is an atom, by the argument of Theorem 2.1. Combine their boxed
defining equations using (1.2). Necessitated truth-pattern exhaustiveness,
universally quantified over the finite argument tuple, says their join
is top. The same Boolean argument now gives Atomicity at tau. The
witnesses can be collected in the stated ZFC metatheory; Intensionality
makes their current identity classes unique.

Given an admitted property X of tau-entities, apply the arbitrary-meet
result to its current extension. Its greatest lower bound witnesses the
ordinary internal Boolean Completeness formula. QED.

**Theorem 3.2.** $\mathcal T_\infty$ gives Rigid Comprehension.

**Proof.** For an arbitrary parameter family $(\bar s_i)_{i\in I}$,
let R represent

$$
 D(\bar x)=\bigvee_{i\in I}(\bar x=\bar s_i).
 \tag{3.1}
$$

Necessity of Identity and the boxed defining equation make R persistent.
For inextensibility, suppose at any accessible point that every R-instance
necessarily satisfies Y. Each $\bar s_i$ is an R-instance there, so
each $\Box Y[\bar s_i]$ holds. By (1.2), their conjunction is
necessary. Inside the box, an R-instance equals some $\bar s_i$;
substitution gives Y of that instance. Hence $R\le Y$. The defining
equation is stable by 4, so this argument applies at every accessible
point and proves the full inextensibility condition, with its leading box.

For a given current relation F, assign the family $(\bar s_i)$ to
its current extension. The resulting rigid R is currently coextensive
with F. This also covers the empty tuple: the range formula is top or
bottom according as the given proposition is true or false. QED.

These are current conclusions from the current scheme. Boxed conclusions
require the corresponding argument at every relevant point, or a separate
persistence proof; optional premises have not been necessitated.

## 4. Full standard models from C5

A **full standard hierarchy** has nonempty sets E and W and domains

$$
 D_e=E,\qquad D_t=\mathcal P(W),\qquad
 D_{\sigma\rho}=D_\rho^{D_\sigma}\quad(\rho\ne e).
 \tag{4.1}
$$

Identity is literal, application is function application, truth is
membership at a designated world, and quantifiers range over the fixed
typed domains. Necessity quantifies over all of W. This describes the
target models; it is not a clause added to Comprehension.

**Theorem 4.1.** The set-sized models of
$\mathcal T_\infty+C5$ are exactly the full standard hierarchies,
up to the canonical typed representation. No separate Atomicity premise
is required.

**Proof.** Finite Comprehension reconstructs C, and Theorem 2.1 gives
propositional Atomicity. C5 means boxed ND at every type. The existing
finite consequences give BF, all-type Atomicity and boxed Plenitude.
Their canonical representation uses the current identity quotients as
constant domains and

$$
 W=\mathrm{At}(D_t),\qquad
 \beta_\tau(R)=\{(w,\bar a):w\le R[\bar a]\}.
 \tag{4.2}
$$

Here are the ingredients of that representation. Atom tests respect
Boolean operations and jointly separate propositions. BF gives
$w\le\forall x Fx$ exactly when $w\le Fx$ for every current x.
NI and ND make typed identity constant at those worlds. Intensionality
and BF make (4.2) faithful at every relation type. Actuality supplies
the designated true atom. Necessity is universal over the atom set.
The finite truth lemma then gives the original C representation; the
expanded argument is in [Positive results, section 5](infinitary-canonical-representation.md).

Arbitrary joins at t imply that an atom belongs to the support of an
infinitary disjunction exactly when it belongs to the support of one
disjunct. Indeed meet with a fixed atom preserves any existing join, and
each meet is either that atom or zero. Thus (4.2) also respects the new
infinitary connectives, by induction on their well-founded syntax.

Let $U\subseteq W\times\prod_kD_{\sigma_k}$ be arbitrary. Use
parameters p_w for the proposition atoms and parameters for the entries
of each tuple in U. Apply Comprehension to

$$
 A_U(\bar x)=
 \bigvee_{(w,\bar a)\in U}
   \left(p_w\land\bigwedge_k x_k=a_k\right).
 \tag{4.3}
$$

At a canonical world v this is true of $\bar x$ exactly when
$(v,\bar x)\in U$. Its Comprehension witness therefore has support
exactly U. Every relational support is available.

For an arbitrary function $f:D_\sigma\to D_\rho$, flatten rho as
$\bar\tau t$ and take the support
$\{(w,x,\bar y):w\le f(x)[\bar y]\}$. The preceding construction
supplies an admitted relation of type sigma-rho with that support.
Faithfulness identifies its value at each x with f(x). This gives every
allowed full function domain and proves (4.1).

Conversely, in a full standard hierarchy, well-founded recursion interprets
every infinitary formula with any simultaneous parameter assignment. Its
set of world–argument points is a set and is represented by (4.1).
That representative satisfies the required boxed equivalence. The base,
classical infinitary logical laws, and C5 also hold. QED.

Only disjunctions of finitary matrices are needed for (4.3). Consequently,
over the same infinitary logical base and C5, restricting Comprehension
to arbitrary disjunctions of ordinary finite matrices already gives the
full characterization. The unrestricted schema is the cleaner statement:
ordinary Comprehension applies to every admitted formula.


fails when $a_n$ is assigned n. This proves strictness in the same
expanded language. QED.

**Theorem 5.2.** No fixed cardinal bound on Comprehension matrices and
their parameter families forces unrestricted fullness, even when the
surrounding infinitary propositional language is unrestricted.

**Proof.** It suffices to treat an arbitrary infinite regular bound kappa.
Choose $\lambda^{<\kappa}=\lambda$, for example
$\lambda=2^\kappa$. Let H be the full one-world hierarchy on
$E=\lambda$. In a sufficiently large regular $H_\theta$, take
$M\prec H_\theta$ of size lambda, containing the coded hierarchy
and its operations, with $\lambda\subseteq M$ and
$M^{<\kappa}\subseteq M$. The usual elementary-hull chain of length
kappa gives this closure because $\lambda^{<\kappa}=\lambda$.

Retain $D_\tau^H\cap M$ at each type and transport application as
in Theorem 5.1. A matrix of total syntax size less than kappa, with fewer
than kappa retained parameters, can be relabelled and coded inside M by
closure. Satisfaction recursion for that set-sized formula in H is
available in $H_\theta$. For an existential subformula true in H,
elementarity supplies a witness in M; the universal case follows by
negation. Infinitary Boolean steps follow by induction over the small
syntax tree. Thus truth for these matrices agrees between H and the
reduced hierarchy. The full representative of such a matrix is definable
from its code and parameters and hence belongs to M. Every bounded
Comprehension instance holds.

There are at most lambda retained individual properties but
$2^\lambda$ subsets of the unchanged individual domain. Therefore
fullness fails. As the proposition domain is still two-valued, the
unrestricted infinitary logical language remains interpretable throughout.
For an arbitrary prescribed bound, choose a regular kappa above it. QED.

The bound in this theorem applies to the whole syntax tree and the whole
parameter family. A truth-pattern formula with $2^{|I|}$ branches need
not fit a bound merely because $|I|$ does.

## 5. A countermodel for every fixed parameter bound

**Theorem 5.3.** For every infinite regular cardinal kappa there is a
one-world model of C5 and all-type Atomicity which admits the unrestricted
infinitary logical language and satisfies every Comprehension instance
with fewer than kappa parameters, but fails unrestricted Infinitary
Comprehension. There is no bound on the size of the formulas in the
restricted scheme.

**Construction and proof.** Put $E=\kappa\times\{0,1\}$ and let
G be the full permutation group of E. A support of a G-object a is a set
S of individuals such that every permutation fixing S pointwise fixes a.
Use $D_e=E$ with its natural action and $D_t=\{0,1\}$ with
the trivial action. Recursively, let $D_{\sigma\rho}$ consist of
all functions from $D_\sigma$ to $D_\rho$ with a support of
cardinality less than kappa, under the conjugation action

$$
 (g\cdot f)(x)=g\cdot f(g^{-1}\cdot x).
$$

These domains are invariant under G. Every individual has its singleton
support, every proposition has empty support, and every admitted function
has a small support by definition. Application is ordinary function
application: a support for f together with a support for x supports f(x).
Identity is literal identity. There is one world, so necessity is the
identity on propositions. Quantifiers range over the displayed invariant
domains. Arbitrary infinitary Boolean operations have their ordinary
two-valued interpretation, whether or not a corresponding higher-type
property is available.

Take an arbitrary well-founded infinitary matrix with fewer than kappa
parameters at arbitrary types. Choose a small support for each assigned
parameter. Regularity makes their union S small. Structural induction on
the actual formula shows that its truth is equivariant when both the


This last currying claim includes a typing check. After fixing some
arguments, the remaining function is supported by S together with the
supports of those arguments, a finite union of small sets. Induction
backwards along the finite argument list therefore places every intermediate
function in its required domain, and the outer function has support S.
It supplies the Comprehension witness. Thus all finite instances hold,
giving the ordinary theory C, and the same proof covers every size of
infinitary matrix with fewer than kappa parameters. Literal one-world
identity gives C5.

All-type Atomicity also holds. A nonzero relation is true of some finite
tuple. The characteristic function of that singleton tuple has a support
contained in the finite union of the tuple entries' supports. It is

## Sources

Original mathematical development by OpenAI Codex at Daniel Kodsi’s request, 23 October 2026, source `misc`; source sections 1–4, 5.3 and 6. The finite reconstruction is in [Lambda-free reconstruction](lambda-free-reconstruction.md), §§1–3 and 10. The canonical representation argument is expanded in [Canonical representation and fullness](infinitary-canonical-representation.md). These are semantic consequences for the stated set-sized models, not a completeness theorem for an effective calculus.

## Certified representation

The [Lean certificate](../evidence/certificates/infinitary-full-representation/certificate.json) proves the forward representation for universe-0 categorical premodels under three explicit hypotheses: closure under actual infinitary term denotations, unrestricted Infinitary Comprehension for original closed-type matrices, and ☐ND at type $t$. The premodel has coherent injective inclusions into intensions.

The representation retains the original closed root-domain carriers, identifies observationally equivalent reachable worlds, and preserves infinitary truth through grounding. Every proposition profile and every external function at an admitted relational-output type is represented. Separate standard-model validity reports supply the converse semantic direction. These are semantic results; they do not assert recursive proof-calculus completeness or equivalence with finitary Choice Classicism.
