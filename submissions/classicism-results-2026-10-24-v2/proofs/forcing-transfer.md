# Forcing transfer at finite relational types

Original mathematical argument, direct source misc; unpaginated.

## 1. Result and boundary

The component comparison in the preceding note extends to every finite type
of the fixed relational type system: e and t, and sigma -> rho only when rho
is relational. There are two results.

1. The full modalized-domain model on B minus zero, with constant individuals
   omega, has recursive normal forms. Its globally existing representatives
   give the full finite relational type hierarchy in Boolean-valued set
   theory. The comparison preserves application, abstraction, equality and
   quantification, with the modal operators idle in the component. Generic
   quotients are full relative to M[G], not to a larger ambient universe.
2. A component of the source's full rooted cloud has the same local typed
   semantics as its standalone full B-valued model, at all these types.
   Component entities existing globally can be lifted to entities existing
   at the isolated root.

The new issue beyond the real-code fragment is that arguments can themselves
exist only partially. The normal forms below include their partial identity
values. They never replace partial identity by an unguarded pointwise test.

These results concern the explicitly full constructions. They do not prove
that C + necessary RC + IC + strict-smallness MP supplies the same normal
forms in an arbitrary hierarchy. They do not take over the separate task of
axiomatizing a full standard hierarchy.

The controlling construction is Bacon and Claude Opus 5.5 (Anthropic),
*Modalized Domains on Possibility Frames*, draft 20 October 2026:
Definitions 2.1--2.2, p. 8; Definitions 2.4 and 2.7, p. 9; interpretation,
p. 10; Proposition 2.11, p. 11; Example 2.15, p. 12; Lemma 3.2, p. 13;
Definition 4.1 and Lemma 4.3, pp. 20--21. The recursive comparisons in this
note are new arguments, not claims that the paper states these theorems.

## 2. Boolean partial identities and totalization

Work in a transitive ground model M of ZFC. B is a nontrivial complete
Boolean algebra in M. All raw sets, functions, joins, meets and names below
are computed in M. Equivalently the argument can be read internally in a
ground universe of ZFC. The source frame is B minus zero, ordered by
refinement, with each condition seeing its refinements.

Let U_e = omega, U_t = B and U_(sigma -> rho) = U_rho ^ U_sigma. The latter
are raw function sets: their elements need not exist. Define Boolean
identity values recursively by

$$
 \delta_e(n,m)=[n=m],\qquad \delta_t(b,c)=(b\leftrightarrow c),
$$

$$
 \delta_{\sigma\to\rho}(f,g)
 =\bigwedge_{a,c\in U_\sigma}
     \bigl(\delta_\sigma(a,c)\Rightarrow\delta_\rho(fa,gc)\bigr).
 \tag{1}
$$

Unfolding Definition 2.2 shows that a is identical to c at a nonzero
condition p iff p <= delta_sigma(a,c). In particular

$$
 E_\sigma(a):=\delta_\sigma(a,a),\qquad
 G_\sigma:=\{a\in U_\sigma:E_\sigma(a)=1\}
 \tag{2}
$$

are the existence value and the globally existing representatives. The
delta values are Boolean partial equivalence relations: they are symmetric
and transitive in the Boolean sense, and delta(a,c) <= E(a) meet E(c).
These follow either by induction in (1), or from the source PER laws by
testing every nonzero condition. They need not be reflexive with value one.

Write a relational type rho uniquely as sigma_1 ... sigma_n t, allowing
n=0. Flatten its raw elements to functions F:A -> B, where
A = product_i U_sigma_i; for n=0 this identifies B with functions on a
singleton. Write delta_A for the meet of the coordinate identities.
Repeated use of (1) gives

$$
 E_\rho(F)=\bigwedge_{a,c\in A}
       \bigl(\delta_A(a,c)\Rightarrow(F(a)\leftrightarrow F(c))\bigr).
 \tag{3}
$$

The fact that argument existence may be partial is already in delta_A.
For example its diagonal is E_A(a), not necessarily one.

**Totalization lemma.** If p is any element of B with p <= E_rho(F), the flattened function

$$
 F^p(a)=p\wedge F(a)
 \tag{4}
$$

belongs to G_rho and p <= delta_rho(F,F^p). For nonzero p this says it is
identical to F at p; p=0 simply gives the zero relation. For extensionality, below p
use (3); outside p both values in (4) vanish. For identity at p, test any
arguments identical at q <= p and apply the same condition (3). This also
works at t. Individuals already exist globally and require no change.

Taking p=E_sigma(a), and leaving individuals unchanged, gives a global
representative T_sigma(a) with

$$
 \delta_\sigma(a,T_\sigma(a))=E_\sigma(a).
 \tag{5}
$$

The inequality from right to left follows from totalization; the reverse
inequality is a PER law. Thus every local entity has a global representative
on its entire existence region. For finite tuples the coordinatewise T
gives the same assertion with E_A. In particular

$$
 E_A(a)=\bigvee_{g\in G_A}\delta_A(a,g),
 \qquad G_A:=\prod_iG_{\sigma_i}.
 \tag{6}
$$

There is even a single summand attaining E_A(a), namely T applied to the
tuple. Equation (6) concerns existing parts of raw arguments, not the
existence of every raw argument.

## 3. Saturated normal forms

For an arbitrary raw F:A -> B define

$$
 N(F)(a)=\bigvee_{g\in G_A} F(g)\wedge\delta_A(g,a).
 \tag{7}
$$

This is a raw function available by fullness. It exists globally even if F
does not: Boolean transitivity gives

$$
 \delta_A(a,c)\wedge N(F)(a)\le N(F)(c),
$$

and the reverse inequality follows symmetrically. Also N(F)(a) <= E_A(a),
so the normal form vanishes outside the existence region of its arguments.

If p <= E_rho(F), then
`p meet E_A(a) meet N(F)(a) = p meet E_A(a) meet F(a)`.
Indeed, every summand is bounded by F(a) below p by (3).
For the converse, use (6); below delta_A(a,g), extensionality identifies
F(a) and F(g). Consequently

$$
 \delta_\rho(F,N(F))=E_\rho(F).
 \tag{8}
$$

This is equality on the whole possible existence region, not literal
equality of raw functions. In particular a globally existing F is identical
everywhere to N(F), but may differ on never-existing arguments.

The same argument proves the useful equality test

$$
 \delta_\rho(F,H)=E_\rho(F)\wedge E_\rho(H)
       \wedge\bigwedge_{g\in G_A}(F(g)\leftrightarrow H(g)).
 \tag{9}
$$

For the nontrivial direction, work below the right-hand side and a
condition where a and c are identical. Replace each coordinate by its
global representative there using (5). Extensionality of F and H reduces
cross-argument agreement to the displayed tests on G_A. The other direction
uses global tuples directly and the PER laws.

This is where the unguarded pointwise test on all raw tuples would be wrong.
The test on G_A is valid only together with the two existence factors.

## 4. Recursive comparison with Boolean-valued sets

Define the intended internal carriers recursively in Boolean-valued set
theory. H_e is check-omega. For rho = sigma_1 ... sigma_n t, let

$$
 H_\rho=\mathcal P\!\left(\prod_i H_{\sigma_i}\right).
 \tag{10}
$$

Products and powersets here are internal to M^B. The empty product is a
singleton, so H_t is its powerset, canonically the two truth values. This
presentation of a relational type is canonically equivalent to the curried
function-space presentation: application is taking a section of a relation,
and abstraction assembles those sections into a relation. All argument
types in (10) are proper subexpressions, so the recursion is well founded.

We construct names a-hat for every a in G_sigma with the following three
properties:

1. ||a-hat belongs to H_sigma|| = 1.
2. ||a-hat = c-hat|| = delta_sigma(a,c) for global a,c.
3. For every name u, ||u belongs to H_sigma|| is the join, over global a,
   of ||u = a-hat||.

At e use check-n; these assertions are the membership and equality clauses
for check-omega. The third assertion is coverage, not a claim that a mixed
natural-number name equals one fixed numeral with value one.

Suppose the assertions hold at all argument types of rho. Let K be the
internal product in (10), represented by the name containing each tuple
g-hat, for g in G_A, with weight one. The inductive coverage properties and
finite distributivity show that this is the whole product, with

$$
 \|u\in K\|=\bigvee_{g\in G_A}\|u=\widehat g\|,
 \qquad \|\widehat g=\widehat h\|=\delta_A(g,h).
 \tag{11}
$$

For F in G_rho put

$$
 \widehat F=\{(\widehat g,F(g)):g\in G_A\}.
 \tag{12}
$$

This name is a subset of K with value one. Extensionality of F and the
self-identity of global g give

$$
 \|\widehat g\in\widehat F\|
    =\bigvee_{h\in G_A}F(h)\wedge\delta_A(h,g)=F(g).
 \tag{13}
$$

Coverage in (11) then gives

$$
 \|\widehat F=\widehat H\|
    =\bigwedge_{g\in G_A}(F(g)\leftrightarrow H(g))
    =\delta_\rho(F,H),
 \tag{14}
$$

where the last equality uses (9) for global F,H.

It remains to prove powerset fullness, not merely that our names are
subsets. Given a name X, let b=||X is a subset of K|| and put

$$
 u(g)=b\wedge\|\widehat g\in X\|,
 \qquad
 F_X(a)=\bigvee_{g\in G_A}u(g)\wedge\delta_A(g,a).
 \tag{15}
$$

The saturation proof for (7) shows F_X is global. Equality substitution for
names makes u extensional on global tuples; hence F_X(g)=u(g) there.
Equations (11)--(13) show

$$
 b\le\|X=\widehat{F_X}\|.
 \tag{16}
$$

In detail, below b both sets are subsets of K and have the same membership
values on every g-hat. Cover an arbitrary name's membership in K using
(11), and substitute on each equality part. Their membership values agree
below b everywhere, giving (16). Conversely, equality to any F-hat implies
membership in H_rho. This proves the third property at rho and completes
the recursion.

For every relational type a name locally in H_rho therefore has one global
representative agreeing on that entire membership value. At e only Boolean
coverage is needed and asserted.

## 5. Typed terms, quantification, and generic quotients

For a formula phi with globally existing other parameters, the source's
universal quantifier at type sigma has Boolean value

$$
 \llbracket\forall x^\sigma\,\phi(x)\rrbracket
       =\bigwedge_{g\in G_\sigma}\llbracket\phi(g)\rrbracket.
 \tag{17}
$$

To verify the nontrivial direction, at any refinement q and any raw a
existing there replace a by a^q, or by T_sigma(a). It is global and identical
to a at q. The source's fundamental lemma makes phi agree below q. This
is exactly its all-refinements quantifier clause. Existential quantifiers
follow by negation. Local parameter assignments can first be totalized on
the condition under consideration.

The name coverage established in section 4 similarly identifies bounded
Boolean-valued quantification over H_sigma with the meet or join over these
representatives. If c is below every ||phi(g-hat)||, then for any name u,

$$
 c\wedge\|u\in H_\sigma\|
   =\bigvee_g c\wedge\|u=\widehat g\|
   \le\|\phi(u)\|.
 \tag{18}
$$

For application, if F and a exist globally, so does F(a). On every global
tuple of remaining arguments, (13) identifies the name of F(a) with the
section of F-hat at a-hat. Coverage gives equality of those section names.
For abstraction, its source value exists globally by Lemma 3.2. Its values
on global arguments are the values of its body under the corresponding
assignments. Induction on the body, followed by (14), identifies its name
with the internally assembled relation. This covers higher-type arguments
and results, not only first-order relation graphs.

These observations yield a simultaneous induction on terms and formulas:
equality uses (14), application and abstraction use the preceding paragraph,
Boolean operations use B, and quantifiers use (17)--(18). Thus the complete
finite typed relational language has the same Boolean semantics as the
internal full hierarchy (10). Truth of a proposition is membership of the
unique empty tuple in its name. The cloud's box and diamond are idle, so
modal formulas translate by deleting these operators. Globally existing
nonlogical constants can be translated by their names; local parameter
versions hold after restriction to their existence condition.

If G is M-generic, evaluate the names and identify global representatives
whose delta value belongs to G. The forcing theorem and section 4 identify
the quotient at e with omega and at each relational rho with the full
powerset in (10), computed in M[G]. Induction gives the entire finite
relational hierarchy of M[G]. This assertion uses genericity: an arbitrary
ultrafilter need not respect the meets and joins needed for quantification.
It asserts no powerset fullness in an ambient universe larger than M[G].

## 6. Recursive restriction and lifting for a rooted cloud

Now take the source's full rooted cloud for a family (B_i), with constant
individuals omega. Its proposition algebra is C = 2 times product_i B_i.
Its root is isolated for refinement and sees all components. It is not
the forcing frame on C minus zero: in particular the box is not idle at
the root.

Fix i. Write pi:C -> B_i for projection and j:B_i -> C for insertion in
coordinate i, zero in the other components and the root bit. Use a
superscript C or B for the raw domains in the full rooted cloud and the
standalone component respectively. Define raw maps R_sigma:U^C_sigma ->
U^B_sigma and L_sigma:U^B_sigma -> U^C_sigma recursively:

$$
 R_e=L_e=\mathrm{id},\qquad R_t=\pi,\quad L_t=j,
$$

$$
 (R_{\sigma\to\rho}F)(x)=R_\rho\bigl(F(L_\sigma x)\bigr),
 \qquad
 (L_{\sigma\to\rho}f)(a)=L_\rho\bigl(f(R_\sigma a)\bigr).
 \tag{19}
$$

All these functions belong to the raw full domains. Induction gives
R_sigma L_sigma = id exactly on raw elements. Three further properties,
simultaneously proved by induction, hold at every component condition p:

- a ~^B_p b implies L(a) ~^C_p L(b);
- a ~^C_p b implies R(a) ~^B_p R(b);
- if a exists at p in the rooted cloud, then a ~^C_p L(R(a)).

At e these are immediate; at t they say restriction and insertion agree on
component i. For arrows the first two follow directly from Definition 2.2,
using the induction hypotheses on arguments and values.

For clarity, the arrow case of the third is as follows. Suppose F exists
at p. If a ~^C_q b with q <= p, the induction hypothesis gives
b ~^C_q L(R(b)); hence a ~^C_q L(R(b)). Apply F, which respects identity
there. The resulting value F(L(R(b))) exists at q, so the induction
hypothesis on the codomain identifies it with
L(R(F(L(R(b))))). By (19) this is the value of L(R(F)) at b. This proves
the required cross-argument identity.

It follows that R reflects identity between entities that exist at p:
use the first property and the third on both sides. Local existence and
local quantifier coverage are therefore preserved in both directions.
No reflection statement is made about arbitrary non-existing raw inputs.

**Root lifting.** If f ~^B_1 g, then L(f) ~^C_r L(g), where r is the
isolated root. In particular every globally existing component entity
lifts to a root-existing entity. Here is the additional induction needed
for this stronger assertion.

At e it is literal equality and at t it is equality of j-inserted Boolean
values. For a relational type rho, every raw L_rho(f) has terminal
propositional values supported only in component i. Thus any two such
lifts are identical at every point of a different component, regardless
of whether f or g exists in B. In the arrow case, test Definition 2.2 at
each point seen by the root. In component i the already proved local
properties apply; in another component the two codomain lifts are locally
zero. At the root itself, if a ~^C_r b, persistence gives identity at the
top of component i, hence R(a) ~^B_1 R(b). Since f ~^B_1 g, their values
on those arguments are identical at 1; the induction hypothesis for the
codomain makes their lifts identical at r. These are all points seen by r.
The codomain is relational, as required for the locally-zero argument.

Application is preserved locally: for F,a existing at p,
R(F(a)) and R(F)(R(a)) are identical there, because
a ~^C_p L(R(a)) and F respects identity. Abstraction and logical constants
are preserved by their semantic clauses. In particular identity uses the
local equivalence just proved, and quantifiers use the local surjectivity
R L = id on existing component entities; all refinements stay in the same
component. More precisely, induction on terms gives, for an assignment g
existing at p and a term t of type sigma,

$$
 R_\sigma(\llbracket t\rrbracket_{C,g})
       \sim^B_p \llbracket t\rrbracket_{B,Rg}.
 \tag{20}
$$

For abstraction, test the functional identity at q <= p on component
arguments x and y identical there. Lift these arguments by L, apply the
induction hypothesis to the body, and use its substitution of identical
arguments; this proves (20) at the arrow type. For quantifiers, each local
component witness lifts by L and each local cloud witness projects by R,
so the same all-refinements tests are obtained. At type t, (20) means
agreement of formula truth values below p. It gives agreement throughout
component i for assignments existing at its top, including closed formulas
and constants translated by R. It does not extend a merely local parameter
assignment outside its existence region.

Thus this comparison concerns the actual higher-type domains of the full
rooted cloud. It is not an inference from an isomorphism of proposition
algebras alone. A component entity existing only below p can first be
totalized there by section 2 and then lifted to the root. This also gives
an explicit version of the source's no-new-entities conclusion at these
types.

## 7. What this removes, and what it does not

The restriction to the real-code fragment in the preceding note is no
longer a semantic obstacle for the specified full constructions. All finite
relational types, their partial identities, and their full internal powers
can be compared recursively. The preceding CH-contingency proof needs only
the smaller fragment and is unchanged.

The proof exposes a sufficient additional representation condition for
another B-valued hierarchy: local entities must have global representatives,
and for every internal subset name of a finite product of represented lower
carriers, the saturation function in (15) must be admitted. With those
conditions, the recursion in sections 4--5 applies. It is enough to have
such admitted representatives up to local identity; literal equality of
raw domains is unnecessary.

In the full construction (15) is available because every raw function of
the appropriate type is in the underlying domain. In an arbitrary
axiomatic hierarchy it is not licensed merely by propositional completeness:
its definition uses all global lower-type representatives and their entire
membership-value array. Ordinary term closure and rigidification of an
already admitted relation do not by themselves establish that this array,
or its saturation, is admitted. Intensional Choice also cannot simply be
read as a metatheoretic license to add every such raw function. A derivation
of the representation condition from the proposed axioms would be a further
theorem, not a consequence proved here.

Accordingly the general C + necessary RC + IC + strict-smallness MP
implication still requires an argument that its internally complete
Boolean algebra and realized proposition interval support the required
higher-domain representation, or a sufficient entirely internal substitute.
The internal smallness of the relevant forcings and a common type for their
real structures must also be justified there. Neither the non-strict size
reading nor necessary MP is introduced. No countermodel to the general
implication is claimed, and its source-reported status is unchanged.

This is the first substantial checkpoint: the full finite-type extension
for the constructed clouds, together with the exact normal-form admission
obligation left for arbitrary hierarchies. No Lean work or record edit is
part of it.
