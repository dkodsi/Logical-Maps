# Real structures and CH in the full modalized cloud

Original mathematical argument, direct source misc; unpaginated.

## 1. Conclusion and exact scope

For the full modalized-domain model on the forcing frame of a complete Boolean
algebra B, with constant individuals omega, the fragment consisting of

- individuals of type e;
- real codes of type sigma = et;
- predicates and finite-arity relations on those two sorts;

has the same Boolean truth values as the corresponding relational structure in
Boolean-valued set theory. After taking a generic quotient, these domains give
omega, all subsets of omega, and all such finite-arity relations **as computed
inside the forcing extension**. Functions are represented by their graphs.

Using the standard nonempty-subset completeness clause explained in section 2,
there is a canonical real-number structure R_B at the one fixed type sigma = et
for which

$$
\|\mathrm{Real}_{et}(\mathfrak R_B)\|=1_B,
\qquad
\|\mathrm{CH}(\mathfrak R_B)\|
 =\|\mathrm{CH}\|_{M^B}.
\tag{1}
$$

There is also an explicit restriction and lifting comparison between this
fragment in a component and the same fragment in the full rooted cloud. The
lottery family therefore gives, at its root,

$$
\Diamond\exists\mathfrak R\,
 (\mathrm{Real}_{et}(\mathfrak R)\land\mathrm{CH}(\mathfrak R))
\;\land\;
\Diamond\exists\mathfrak R\,
 (\mathrm{Real}_{et}(\mathfrak R)\land\neg\mathrm{CH}(\mathfrak R)).
\tag{2}
$$

This is a result about the specified full lottery model. It does not prove the
general implication from C + necessary Rigid Comprehension + Intensional Choice
+ Forcing Possibilism. Nor does it identify the older lottery hierarchy with
the modalized-domain hierarchy, or cover unrestricted additional higher-type
quantification.

## 2. Sources, framework, and metatheory

The controlling semantic source is Andrew Bacon and Claude Opus 5.5
(Anthropic), *Modalized Domains on Possibility Frames*, draft 20 October 2026:
Definitions 2.1–2.2, p. 8; Definitions 2.4 and 2.7, p. 9; interpretation,
p. 10; Proposition 2.11, p. 11; Example 2.15, p. 12; the fundamental lemma,
Lemma 3.2, p. 13; Definition 4.1 and Lemma 4.3, pp. 20–21; and Definition 6.4,
Theorem 6.8, and Corollary 6.9, pp. 28–29. The inspected copy is
`.reproduction/classicism-modalized-domains-20261023.pdf`; the source URL is
<https://andrew-bacon.github.io/techdoc/modalized-domains.pdf>.

Example 2.15 describes the connection with Boolean-valued higher-order models.
The explicit powerset and relational-graph comparison below supplies the narrow
transfer needed here. The source's lottery theorem establishes its modal axioms
and strict-smallness MP; this note evaluates structural CH in that model.

The Real and CH vocabulary comes from the 23 October upstream
`topics/classicism/background.md`, section Analysis, and
`principles/non-contingency-of-ch.yaml`, inspected in the read-only checkout
`logical-maps/`. These definitions use
relations for operations, injections, and bijections. Their ambient type system
allows an arrow only when its output is relational. No object-language
function type with output e is introduced here.

**Source wording caveat.** The upstream explanation calls X a complete ordered
field, but its subsequent description of the least-upper-bound clause omits
the word *nonempty*. Here completeness has its standard meaning: every
**nonempty** subproperty of X bounded above in X has a least upper bound in X.
If the subsequent prose were instead imposed literally on the empty
subproperty too, no ordered field would satisfy Real: the empty subset has
every element as an upper bound, and an ordered field has no least element.
The transfer theorem remains valid on that literal reading, but the real
structure and structural-contingency conclusions would not. Equations (1)
and (2) use the conventional complete-ordered-field reading. The upstream
wording has not been edited.

For the standard set-forcing inputs, see Assaf Shani,
[*145B Set Theory II: An Introduction to Forcing*](https://people.math.harvard.edu/~shani/Teaching/145/145B-Notes.pdf),
section 3.7, pp. 21–23 (forcing theorem), Theorems 4.9 and 4.13 and section 4.2,
pp. 27–28 (cardinal preservation and Cohen forcing), and section 7,
pp. 35–36 (collapse forcing and preservation of reals and omega_1).

Work over a transitive ground model M of ZFC, with B a nontrivial complete
Boolean algebra **in M**. All function sets, powersets, joins, completions, and
cardinalities in the construction are computed in M. The Boolean calculations
can equivalently be read internally in a ground universe of ZFC. A generic G
is needed only for the optional two-valued interpretation in section 6; no
generic belonging to M is assumed. This distinguishes internal fullness from
fullness in a larger ambient universe.

The component frame has points B minus zero and both refinement and
accessibility given by the Boolean order. Its regular-open algebra is B.
Writing p for a nonzero condition, propositional identity at p is
`p <= (b iff c)`. The box is idle on this component. Individuals are omega with
literal identity at every point. Full function spaces have all ground-model
raw functions as underlying elements, with the source's partial identity:

$$
 f\sim_p g\quad\Longleftrightarrow\quad
 \forall q\le p\ \forall a,b\,
 (a\sim_q b\Rightarrow f(a)\sim_q g(b)).
\tag{3}
$$

The condition q is nonzero where it denotes a frame point. A raw function
exists at p exactly when it is related to itself there. Underlying fullness
does not assert that every raw function exists everywhere.

## 3. Real codes, local relations, and totalization

Let U_e = omega and U_sigma = (B^omega)^M, where sigma = et. Every member of
both carriers exists everywhere. At sigma this follows directly from (3),
since individual identity is literal and every proposition exists everywhere.
Their identity values are

$$
 \delta_e(n,m)=\begin{cases}1&n=m,\\0&n\ne m,\end{cases}
 \qquad
 \delta_\sigma(s,t)=\bigwedge_{n\in\omega}(s(n)\leftrightarrow t(n)).
\tag{4}
$$

Fix a finite list of argument sorts, each e or sigma, and let A be the product
of their raw carriers. Put delta_A(a,c) equal to the meet of coordinate
identities. Curried raw relations can be treated as ground-model functions
F:A -> B. Iterating (3) gives

$$
 F\text{ exists at }p
 \quad\Longleftrightarrow\quad
 p\wedge\delta_A(a,c)\le F(a)\leftrightarrow F(c)
 \quad\text{for all }a,c\in A.
\tag{5}
$$

For the forward direction use each nonzero
`q = p meet delta_A(a,c)`: the arguments are identical there, so the output
propositions agree below q. Conversely, local identity at any q <= p says
`q <= delta_A(a,c)`, and (5) supplies the required output identity. The same
argument for curried relations works because all base arguments exist
everywhere and accessibility is transitive.

Define the existence value

$$
 \epsilon(F)=\bigwedge_{a,c\in A}
  \bigl(\delta_A(a,c)\Rightarrow(F(a)\leftrightarrow F(c))\bigr).
\tag{6}
$$

Here Boolean implication is `not b join c`. Write Ext(A) for those F with
epsilon(F)=1. On arbitrary raw relations the partial identity value is

$$
 \delta(F,H)=\epsilon(F)\wedge\epsilon(H)
              \wedge\bigwedge_{a\in A}(F(a)\leftrightarrow H(a)).
\tag{7}
$$

Indeed, cross-argument identity entails existence of both functions and
pointwise agreement, by the PER laws and reflexivity of each argument.
Conversely those three conditions imply cross-argument agreement using (5).
Only on globally existing relations can the existence factors be omitted.

**Local totalization.** If p <= epsilon(F), put

$$
 F^p(a)=p\wedge F(a).
\tag{8}
$$

Then F^p is in Ext(A) and is identical to F at p. To verify extensionality,
split delta_A(a,c) into its parts below p and below its complement. The first
part uses (5); on the second, both output values in (8) are zero. Agreement
at p and (7) give identity there.

This step preserves existence-sensitive quantification. The semantic clause
for `forall F phi(F)` at p tests every q <= p and every F existing at q.
For a globally existing assignment of the other parameters, it is equivalent
to

$$
 p\le\bigwedge_{H\in\mathrm{Ext}(A)}\llbracket\phi(H)\rrbracket.
\tag{9}
$$

One direction tests globally existing H at p. For the other, replace a raw F
existing at q by F^q. They are identical at q, so the fundamental lemma
preserves the formula's truth below q. This proves precisely the original
all-refinements condition. Negation gives the corresponding existential join.
Assignments whose relation parameters exist only below p can first be
totalized at p; their values below p are preserved. No universal assertion
about a raw relation outside its existence region is needed.

## 4. Boolean-valued names and fullness of the represented relations

For s in U_sigma use the name

$$
 \dot s=\{(\check n,s(n)):n\in\omega\}.
\tag{10}
$$

The recursive membership and equality clauses give

$$
 \|\check n\in\dot s\|=s(n),\qquad
 \|\dot s=\dot t\|=\delta_\sigma(s,t).
\tag{11}
$$

Every name forced to be a subset of check-omega has a representative (10)
equal to it with value one: take `s(n) = ||check n belongs to that name||`.
Equality follows from extensionality and the membership clause for
check-omega. Below a condition p forcing subsethood the same construction
gives equality below p. Thus the carrier represented by these names is the
internal powerset of check-omega, not the check-name of the ground powerset.

For a in A let dot-a be the finite tuple of its coordinate names, using
check-n for individual coordinates. Define

$$
 \dot K_A=\{(\dot a,1):a\in A\}.
\tag{12}
$$

This is forced to be the corresponding product of check-omega and the
internal powerset of check-omega. Its members satisfy Boolean coverage:

$$
 \|u\in\dot K_A\|=\bigvee_{a\in A}\|u=\dot a\|.
\tag{13}
$$

For individual coordinates, coverage follows from the name check-omega.
For real-code coordinates it follows from (10), locally if necessary.
Finite products combine these covers by finite distributivity over joins.
Also `||dot-a = dot-c|| = delta_A(a,c)`.

Coverage is the required statement. A name for a natural number mixed over
an antichain need not equal one fixed numeral with value one.

For F in Ext(A) define a subset name

$$
 \dot F=\{(\dot a,F(a)):a\in A\}.
\tag{14}
$$

Then dot-F is forced to be a subset of dot-K_A, and

$$
 \|\dot c\in\dot F\|
 =\bigvee_{a\in A}\bigl(F(a)\wedge\delta_A(a,c)\bigr)
 =F(c).
\tag{15}
$$

Extensionality bounds every summand by F(c); the summand a=c supplies the
reverse inequality.

Conversely, suppose dot-X is forced to be a subset of dot-K_A. Define
`F(a) = ||dot-a in dot-X||`. Equality substitution in Boolean-valued set
theory makes F extensional. Equation (15) gives agreement of membership for
each represented tuple. To get equality of the whole sets, for an arbitrary
u use (13): its membership value is covered by the values on which u equals
some dot-a. On each part, substitution gives agreement. Both names are
subsets of dot-K_A, so they have equal membership values everywhere and
`||dot-F = dot-X|| = 1`.

If subsethood is known only below p, instead take
`F(a) = p meet ||dot-a in dot-X||`. This is globally extensional and its
name agrees with dot-X below p. This covers relation parameters that arise
only locally in a forcing extension.

Consequently **all** internal subsets of these finite products are
represented, including all graphs on the stated carriers. This does not
claim that all raw A -> B functions are extensional. Furthermore, for
globally extensional F and H,

$$
 \|\dot F=\dot H\|
 =\bigwedge_{a\in A}(F(a)\leftrightarrow H(a)),
\tag{16}
$$

by the same coverage argument. This matches (7) on existing parameters.

## 5. Formula transfer and the canonical real structure

Consider the two-sorted nonmodal relational language with variables for e
and sigma and relation variables of all finite arities on these sorts.
Allow equality of these objects and of relation variables, membership of a
natural number in a sigma code, Boolean connectives, and quantifiers over
the stated carriers and relation sorts. Application of a relation to its
arguments is allowed; unrestricted functionals taking relation variables
as arguments are outside this fragment. Definitional lambda abbreviations
can be expanded into the displayed relational formulas.

Under globally existing assignments, every formula has the same Boolean
value in the cloud component as its translation into Boolean-valued set
theory, with relation quantifiers interpreted as powerset quantifiers.
Proof is by induction. Equations (11), (15), and (16) handle atoms; Boolean
connectives use the same algebra. For carrier quantifiers, (13) and equality
substitution show that bounded quantification over dot-K_A is the meet or
join over represented tuples. Explicitly, if c is below every value
`||phi(dot-a)||`, then

$$
 c\wedge\|u\in\dot K_A\|
 =\bigvee_a(c\wedge\|u=\dot a\|)
 \le\|\phi(u)\|.
$$

The converse uses each dot-a as an instance. For relation quantifiers,
section 4 represents every internal subset, and (9) identifies quantification
over Ext(A) with the modalized domain's original local quantification.
Local assignments are handled by totalization. This completes the induction.

Now fix in M a coding of the rationals by natural numbers. A real is a
Dedekind cut, hence a subset of omega and so an entity of type sigma=et.
Define X(s) as the Boolean value that dot-s is a cut. Define order and the
ternary addition and multiplication graphs by the usual set-theoretic cut
definitions, with value false outside X. Let 0 and 1 be the codes of the
two rational cuts, and let N(s) say that dot-s is a nonnegative integer cut.
Each relation is extensional by equality substitution and therefore exists
globally by (5).

The corresponding tuple has exactly the types required by the map:

$$
 \mathfrak R_B=(X^{\sigma t},\le^{\sigma\sigma t},
 +^{\sigma\sigma\sigma t},\times^{\sigma\sigma\sigma t},
 0^\sigma,1^\sigma,N^{\sigma t}).
$$

The ZFC construction of the Dedekind reals gives a complete ordered field,
and its natural numbers are the least subset containing zero and closed
under adding one. Every property quantified over in that assertion, and
every nonempty bounded-above subproperty quantified over in completeness,
is included in section 4. Formula transfer therefore gives the first equality
in (1), with the source-wording qualification in section 2. It is not
merely completeness with respect to ground-model subsets of the reals.

The exact CH formula is

$$
 \forall Y^{\sigma t}\,
 \bigl((\forall x\,(Yx\to Xx))\to
       (Y\precsim N\lor Y\approx X)\bigr),
\tag{17}
$$

where the two comparisons are witnessed by binary relational graphs.
All its quantified subsets and graphs are covered by the transfer theorem.
In ZFC, (17) for the reals is equivalent to CH: if the continuum has size
aleph_1, each subset is countable or has the continuum's size; if it is
larger, a subset of size aleph_1 witnesses failure. This proves the second
equality in (1).

## 6. What the generic quotient means

Let G be M-generic for B. The sigma quotient sends s to
`{n : s(n) belongs to G}`. Equations (10)–(11) and the forcing theorem show
that this identifies the quotient exactly with the subsets of omega in
M[G]. Relations are interpreted by membership of their Boolean values in
G; section 4 supplies all the corresponding relations in M[G]. Formula
transfer and the forcing theorem identify their satisfaction relations.

This uses genericity. An arbitrary ultrafilter need not turn arbitrary
Boolean meets or joins into universal or existential quantification.
In particular, do not infer equality of the sigma quotients by assuming
that an ultrafilter contains a countable meet whenever it contains each
factor. The forcing theorem supplies the required equivalence. Nor is
P(omega) in M[G] asserted to be the powerset in an ambient universe
containing M[G].

The source's no-new-entities lemma is compatible with forcing-new reals:
existing ground representatives can have new generic evaluations.

## 7. Restriction from the full rooted cloud

For a family (B_i), the full cloud has propositional algebra

$$
 C=2\times\prod_iB_i.
$$

Let pi_i:C -> B_i be projection and j_i:B_i -> C insert an element in
coordinate i, with zero in every other coordinate including the root bit.
The insertion preserves the Boolean structure relative to the component
unit j_i(1); it is not asserted to preserve the global unit or complement.
Use these maps coordinatewise on real codes, and use the identity on
individuals.

The full cloud's sigma carrier is (C^omega)^M. Its projection onto
(B_i^omega)^M is surjective, with section j_i. At a point p in component i,
identity of sigma objects is precisely the value (4) of their projections,
restricted below p. Thus a and j_i pi_i(a) are identical everywhere in
component i; individual coordinates are unchanged.

If F is a globally extensional component relation, lift it by

$$
 \widehat F(\vec a)=j_i\bigl(F(\pi_i\vec a)\bigr).
\tag{18}
$$

This raw relation exists at the root and throughout the cloud. On component
i it respects identity by extensionality of F. On other components all
its values are locally zero. At the root, identity on e and et is literal,
so identical argument tuples have literally identical outputs. These are
exactly the tests in the iterated form of (3).

Conversely, if H is a cloud relation existing at p in component i, put

$$
 f(\vec s)=\pi_i H(j_i\vec s).
\tag{19}
$$

It exists below p in the component. For arbitrary cloud arguments a,
local extensionality and the identity of a with j_i pi_i(a) show that
`pi_i H(a)` and `f(pi_i(a))` agree below p. If a global component
representative is needed, use f^p from (8). This proves local surjectivity
for quantified relations as well as agreement of their applications and
identities. Together with the carrier projections, it gives formula
transfer between the full cloud restricted to i and its standalone
component, by the induction in section 5. All refinements of a component
point remain in that component, as required for the quantifier step.

In particular the canonical real structures in section 5 lift to tuples
existing at the root and all component points. Their Real and CH values
in component i are those in (1). No claim about their being real structures
at the isolated root is needed. A full rooted cloud with a single B
component has algebra 2 x B; it must not be confused with the standalone
component, whose algebra is B.

## 8. Two factors in the lottery family

Let mu > omega be the source's strong limit cardinal of countable
cofinality, with all quantities computed in M. Set kappa = 2^aleph_0.
The lottery includes representatives of every nontrivial complete Boolean
algebra of size less than mu.

For CH, use P_+ = Col(omega_1,kappa): countable partial functions from
omega_1 to kappa, ordered by extension. The standard collapse theorem says
that it preserves omega_1 and adds no reals, while its generic union
surjects onto kappa. Hence it forces CH. For failure of CH use
P_- = Add(omega,omega_2): finite binary functions on omega_2 x omega.
It is ccc, preserves cardinals, and adds omega_2 distinct reals, so forces
not-CH. These are the forcing inputs cited in section 2; adding one Cohen
real would not supply the required change in CH.

Here are the size checks needed for this particular lottery. Since
omega_1 <= kappa and kappa^aleph_0 = kappa, the set of countable partial
functions in P_+ has size kappa: encode their graphs as countable subsets
of omega_1 x kappa for the upper bound, and use singleton graphs for the
lower bound. The Boolean completion B_+ has at most 2^kappa elements,
since regular-open sets are subsets of the forcing poset. Strong
limitness gives kappa < mu and then 2^kappa < mu.

Similarly |P_-| = omega_2, so its completion B_- has at most 2^omega_2
elements. We have omega_2 <= 2^omega_1 < mu, since omega_1 < mu, and
therefore 2^omega_2 < mu. Both completions are nontrivial. Thus both
occur up to isomorphism in the lottery family. The arguments and their
names transport along those complete Boolean algebra isomorphisms.

By (1) and section 7, the top point of the B_+ component satisfies
`exists R (Real_et(R) and CH(R))`, and the top of the B_- component
satisfies its not-CH counterpart. The isolated root sees both points.
If either corresponding diamond failed at the root, its boxed negation
would hold at every accessible point, contradicting the relevant
component witness. This proves (2), and therefore refutes both disjuncts
of the non-contingency-of-CH sentence at sigma=et in this concrete model.

Countable cofinality of mu is used in the source's proof of MP, through
the complete-Boolean-algebra cardinal gap. The CH argument here uses
only inclusion of the two appropriately sized forcing factors.

## 9. The remaining general implication

The lottery already has the full hierarchy and the explicitly supplied
forcing components. The transfer proof repeatedly uses that external
construction: all B^omega codes, all raw relation functions, local
totalization, Boolean-name normal forms, and the projection/lifting maps.

For an arbitrary hierarchy satisfying the proposed three axioms, the
following implications have not been proved here:

1. Its internally complete Boolean algebras have the externally complete
   representation needed for this forcing construction, or an adequate
   entirely internal substitute.
2. An isomorphism from an internal Boolean algebra to the propositions
   below p extends to the needed real-code and relational domains, with
   the required local fullness and preservation of quantifiers.
3. The relevant CH and not-CH forcings can be represented with the exact
   internal size bound and their real structures placed at a common
   admitted type.

The size condition in Forcing Possibilism is
`Fin(X) or X is strictly smaller than the propositions`, with comparisons
by relational injections, and the witnessing proposition must differ
from top. The quantifiers are unboxed. Neither a non-strict size bound
nor necessary MP has been substituted. In the lottery source MP itself
can fail inside a component (Remark 6.11, p. 30).

The upstream result
`necessary-rigid-comprehension-intensional-choice-and-forcing-possibilism-incompatible-with-non-contingency-of-ch`
was inspected with status `conjectured`, empty proof, and `lean: none`.
Its source attributes the theorem to Bacon's *Could the truths of
mathematics have been different?*, draft 9 October 2025, Theorem 6.1,
p. 27, with proof deferred. Nothing in this note promotes that record.

The bounded checkpoint is the proved concrete transfer and lottery
consequence, with the representation problem above isolated as the next
mathematical obligation. No Lean work, frozen submission edit, publication,
or deployment is part of this checkpoint.
