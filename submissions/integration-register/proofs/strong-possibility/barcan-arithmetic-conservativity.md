# Arithmetic countermodels with Strong Actuality and Barcan

26 October 2026. Ordinary mathematical deductions by OpenAI Codex.
Direct source: `misc`, this note, §§1–7. Self-checked, not independently
audited or Lean-verified. The interpretation inputs are identified below.
Neither unrestricted Strong Possibility question is settled.

## 1. Exact theories and statement

Treat independently L equal to the pure language and L equal to exactly
Σ={c:e→t}, with no original individual names. Put M_L=Max(C_L). Let Q_L
be M_L together with StrongActuality, ordinary Barcan at every admitted
type, and the current Relational Choice and Transversal Choice schemata.
No boxed version of an added principle is included. Let T be the ordinary
first-order arithmetic consequence theory of C+I_e in the fixed Frege
interpretation, and TrueΠ₁ the externally standard-true Π⁰₁ sentences.

**Theorem.** In both languages,

    Th_arith(Q_L) = Th_arith(M_L) = Cn(T + TrueΠ₁).             (1)

In particular, every arithmetic sentence consistent with M_L remains
consistent after adding the entire displayed structural package. Applied
to the fixed true Π⁰₂ sentence Γ_L independent of M_L, both

    Q_L + Γ_L,          Q_L + not Γ_L                         (2)

are consistent. These are separate models, not an embedding between them.

The lower inclusion in (1) uses the existing pure-Max arithmetic theorem.
The new part is the upper inclusion with Barcan and StrongActuality,
including the original unary constant. The key construction is an internal,
bounded-type version of the interpretation-arrow root, represented by
coherent profiles over a category of coded C_L-models.

## 2. Inputs and their scope

The earlier [arithmetic study](../../../classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md),
§§35–37, provides these inputs:

1. A current extensional quotient of any C+I_e model supplies every fixed
   finite order of arithmetic while preserving its first-order numbers.
2. For any externally fixed finite rank bound, a number-preserving
   interpretation gives a model of ZFG[n+] plus V=L with sufficiently
   many iterated powersets of its own ω. Its ω need not be externally
   standard or well-founded in the surrounding presentation.
3. Pure Max has arithmetic theory Cn(T+TrueΠ₁), and a complete standard-
   arithmetic model. Adjoining the fresh relational constant to C does
   not change T: substitution of the closed bottom relation eliminates c
   from a proof of a pure arithmetic sentence.

Input 2 uses Colin McLarty, *Interpreting set theory in higher order
arithmetic*, arXiv:1207.6357v5, 15 February 2013, §§3–5, especially
Theorems 4.3 and 5.3, pp.5–6. The canonical ω-tree and the retained
natural-number parameters give the number preservation, as checked in
the linked study §36.1. [Primary text](https://arxiv.org/pdf/1207.6357).

We also use the small intensional category of C_L BBK-models whose typed
carriers are subsets of ω, with all logical homomorphisms. In particular,
if p≠bottom in one of these models, some homomorphism to another makes
p actually true. Bacon–Dorr, *Classicism*, draft 1 July 2022, Theorem 3.12
and its small-category refinement, pp.51–52, supply this fact; the
countable Henkin construction is Theorem 3.2 and footnote 64, pp.44–45.
[Primary text](https://andrew-bacon.github.io/papers/Classicism.pdf).
These locators deliberately use the inspected 2022 draft rather than the
map's 2023 pagination.

The interpretation-arrow idea and its fresh-name Barcan argument are
Cian Dorr's construction of 19 October 2026, as recorded in
[the existing write-up](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/coalesced-pinned-interpretations-root.md).
The coherent-profile implementation and arithmetic-conservativity
argument below are deductions here, not claims attributed to those sources.

## 3. A coded interpretation-arrow root

Work inside a sufficiently large finite-rank set model S from input 2.
Let Ccal be the category of internally coded countable C_L BBK-models
and their logical homomorphisms. These models preserve the original
signature, so every homomorphism preserves c in the unary case. Their
typed carriers, term interpretations and truth predicates are coded on
ω^S. Objects, homomorphisms and the assignments used next can all be
coded by subsets of ω^S, with a fixed finite coding overhead.

Fix countably many fresh auxiliary generator symbols of every type.
They are used only to describe the construction, not added to the
reference M_L. For each M in Ccal let I range over all typed assignments
of these generators to M. An admissible profile at type σ is a family

    α_(M,I) ∈ M_σ

with both properties:

* There is one finite set of generators on which α depends: at a fixed
  M, assignments agreeing there give the same α-value.
* α_(N,hI)=h(α_(M,I)) for every homomorphism h:M→N in Ccal.

Call the set of these profiles P_σ. Constant logical profiles and the
generator profiles α_(M,I)=I(d) are admitted. Profiles are not assumed
to be original-language term profiles. The naturality condition is
essential in the Barcan proof below.

The root individual domain consists of the auxiliary individual labels.
Its profile at label d is I↦I(d). For each required relational type
σ=τ₁…τ_k t define the root carrier recursively as

    P(D_τ₁ × … × D_τ_k) × P_σ.                               (3)

At t the first factor is {0,1}. It supplies actual truth; the second
factor supplies the coherent old-model values. All powersets here are
internal powersets in S. Application slices the current extension and
applies the profile values pointwise. Quantifiers have the ordinary
current truth clause and the corresponding quantifier value in each M.
Identity has current truth exactly when the root entities are literally
equal, and profile Eq_M of their respective profiles.

A lambda abstraction has the current extension of its body and, at
(M,I), the abstraction evaluated in M on the parameter profiles. A finite
union of supports suffices for its profile, and preservation of all term
operations by h gives naturality. This verifies closure, including
quantified and identity-containing bodies. Beta and eta hold at the
current coordinate and in every profile. The classical local truth and
quantifier clauses verify H. An H-equivalence makes the current lambda
extensions agree and makes their profiles identical in every C_L-model;
it therefore verifies Logical Equivalence with its original restriction.

In the unary signature, interpret c by empty current extension and the
coherent profile c_M. Each auxiliary relational generator d has empty
current extension and profile I(d). All original closed L-terms have
their original interpretation in every profile M, independently of I.

This algebraic construction avoids building a full set-theoretic action
representation at every internal type. The old carriers remain the coded
BBK carriers. Profile equality and the actual coordinate determine root
entity equality; the category's separation property is used explicitly
when ordinary possibility needs a true old witness.

## 4. The added principles and the arithmetic

**Barcan.** Use diamond exists x F(x) -> exists x diamond F(x). If the
existential is currently true, its actual witness suffices. Otherwise its
nonzero value has a profile (exists F)_(M,I)≠bottom. By the small-category
separation property, choose h:M→N making h((exists F)_(M,I)) true.
Naturality identifies this with exists F_(N,hI). Choose its actual
N-witness y.

Choose a fresh generator d of the quantified type outside a finite support
of F. Replace only (hI)(d) by y, obtaining I'. Finite support gives
F_(N,I')=F_(N,hI). The root entity d-hat with profile I(d) therefore has
(F d-hat)_(N,I') actually true, hence nonzero. Thus F d-hat is nonzero
at the root, proving its possibility and the required Barcan conclusion.
For the individual type d-hat is the actual individual label d. This
argument covers every type required by the finite proof fragment.

The intermediate h is necessary: a profile's being nonzero in M does
not imply it is actually true there, and Barcan is not assumed at M.
This is why arbitrarily choosing finitely many component algebras would
not be an adequate replacement for Ccal.

**StrongActuality.** Let q have current truth 1 and bottom profile.
For every root proposition p, q∧p equals q or bottom according to p's
current truth. Thus Settle(q) is currently true. Its profile is
Settle(bottom)=top at every M. Consequently Settle(q) itself is the
root top proposition, establishing Box Settle(q). The true q is the
required strong world.

**Current choices.** Every internal S-subset of a current argument
product occurs in (3), with bottom profile if desired. Global
well-ordering in S therefore supplies an admitted selecting graph for
each serial relation and an admitted transversal for each equivalence
relation. These are current Relational and Transversal Choice; they do
not assert intensional Functional Choice.

**Arithmetic.** The current individual carrier is internally countably
infinite. Replacement forms the internally iterated zero/successor
orbit. Its range is the actual extension of an admitted predicate, so
the impredicative number domain is contained in that orbit; induction
inside S gives the reverse containment. The full current individual
property extensions distinguish the n-element initial segments for
distinct n∈ω^S. Hence the orbit is in bijection with ω^S. The current
addition and multiplication graphs are admitted, and their recursive
characterization gives the same operations, as in the earlier study
§37.6. Root first-order Frege arithmetic is therefore exactly S's
first-order arithmetic, including when S has nonstandard numbers.

## 5. Finite-proof argument for (1)

Suppose an arithmetic A is not a consequence of T+TrueΠ₁. By ordinary
compactness and the definition of T there is a model of

    C + I_e + all translated TrueΠ₁ + not A.

For any sufficiently large fixed rank bound, inputs 1–2 produce a set
model S with the same arithmetic, satisfying TrueΠ₁ and not A. Suppose,
for contradiction, a finite Q_L-proof π proves A. Expand abbreviations
and the H-certificates for its Logical-Equivalence steps. Include the
fixed Frege-number and arithmetic-correctness derivations. Only finitely
many root types and added-principle instances are now required.

Use the possibility presentation of Max for the finitely many used
instances diamond P_i. Each Con(C_L+P_i) is an externally true Π₁
sentence, and therefore holds in S. Internal Henkin completeness gives
a coded model M_i in Ccal satisfying P_i. The root value of P_i has
a true, hence nonzero, profile there, so the root satisfies diamond P_i.
Thus all the Max instances in π hold, as do its required structural
axioms by §4.

Here is the finite-rank bound. Codes for the whole old category and its
generator assignments are sets of natural numbers. The index set J of
pairs (M,I) is a set of such codes. Every typed profile is represented by
a graph contained in J×ω; finite pinning and naturality select a subset
of that fixed function space by separation. This requires only a fixed
finite powerset allowance, independent of the type. The current factors
in (3) require finitely many additional powersets, bounded by the maximum
type complexity of the expanded π and its listed auxiliary derivations.
Replacement handles the numerical orbit. Choose the rank n at the start
large enough for these bounds. No uniform full root hierarchy over all
internal types is assumed.

The old category's Henkin completeness and separation proofs are carried
out on coded models and countable diagrams inside S. Their objects and
homomorphisms remain in the same fixed coding bound; they do not require
the root's higher full powersets. The source proofs in §2 give exactly
these countable-model constructions.

The root interpretation now makes every step of π sound but makes A
false, a contradiction. Hence Q_L proves no arithmetic consequence
beyond Cn(T+TrueΠ₁). Conversely M_L contains the pure Max axioms: adding
the fresh relational constant is conservative for C-provability of pure
identities. The earlier pure-Max theorem supplies the lower inclusion.
Since M_L⊆Q_L, all three theories in (1) have the same arithmetic
consequences. This proves (1), and the deduction theorem proves (2).

## 6. Consequences for the consistency research

The two assigned Max theories have the same ordinary arithmetic
consequences, although they have different higher-type consequences.
Thus the pure Γ may, if desired, be used as a common arithmetic test
in both languages. Keeping the separately defined Γ_L is also harmless.

The [arithmetic-lifting theorem](arithmetic-lifting.md), §3, now applies
with the added structural schemata as its computably axiomatized P.
Every countable recursively saturated model of Cn(T+TrueΠ₁) can be the
actual arithmetic of a genuine Q_L-model. In particular a suitable
nonstandard model of not Γ_L can have StrongActuality, every ordinary
Barcan instance, and both current choice schemata simultaneously.

This removes those structural requirements as an independent obstacle to
choosing the arithmetic target. It supplies no full-term embedding from
a Γ_L-model into a not-Γ_L-model. The required arithmetic disagreement
cannot be obtained from the literal return maps used in the earlier
grafts, which force the two numerical structures to be isomorphic.
The one-way embedding and unrestricted SP targets remain unproved.

## 7. The combined structural SP fragment is also arithmetically conservative

There is a stronger comparison using the combined model of
[triangulation-ladder.md, §8](triangulation-ladder.md#8-strong-actuality-and-barcan-can-hold-at-the-same-retract-target).
Write B_L for the following theory, with the same reference M_L throughout:

* M_L, the singleton-individual sentence E₁, and the finite conjunction
  A_L of singleton-cell atomhood assertions defined in that note §3;
* DP for every finite conjunction P of ordinary Barcan instances,
  relational atomlessness instances, not E₁, and current Relational or
  Transversal Choice instances;
* DQ for every finite conjunction Q of StrongActuality, ordinary Barcan
  instances, not E₁, and those same current choice instances.

The constructor fragment K is **not** included in this definition. Both
displayed D-families have the original M_L-consistency side condition:
the §8 targets verify it. In particular full SP entails B_L.

**Theorem.** Separately for the pure and exact unary languages,

    Th_arith(B_L) = Th_arith(M_L) = Cn(T + TrueΠ₁).             (3)

Thus the entire combined structural fragment adds no ordinary arithmetic
consequences. This is stronger than consistency of B_L alone. It also
distinguishes its contribution from K, which proves the true Π₂ sentence
Γ_L independent of M_L.

### Internal form of the three-object construction

Suppose a finite B_L-proof proves an arithmetic sentence A not in
Cn(T+TrueΠ₁). Choose the finite-rank set model S as in §5, with arithmetic
not A. We implement the §8 construction internally in S, retaining its
objects R, W and S₀; S₀ denotes the special target, not the ambient set
model. All supplies of auxiliary generators and all finite supports are
now internal to S. In particular an internally finite support may be
externally infinite; freshness in the proofs is internal freshness.

Use the small coded C_L category from §3 as the old category. At a new
object X, an old profile is the interpretation of one internally coded
L-term in finitely many X-generators. At S₀ the special z is replaced by
bottom in old profiles. Assignments at old targets are unrestricted on
the other auxiliary generators and preserve the original c, if present.
Profiles are identified when all their old interpretations agree.

At each required relational type, pair such an old profile with its
extensions at all new arrows out of X, requiring one finite generator
support for those extensions and the profile. Application and lambda
abstraction use the same coordinate clauses as before. New transport is
precomposition on the new coordinates and substitution in the old
profile. Old transport evaluates the profile in the indicated coded
model. Naturality of old term interpretations makes these transports
compatible. This is the algebraic implementation of the §8 action
construction; it avoids building the old action representation's entire
type hierarchy.

The support, substitution and masked-lift proofs of §8 are internal
finite arguments. Their witness-renaming operations require finitely
many fresh generators of specified types, which exist internally. For
an old-target Barcan witness, first use the coded category's separation
property to make the nonzero existential true, as in §4, and then
change a fresh generator's assignment. The special generator z still
gives StrongActuality at S₀. Fresh unrestricted proposition generators
still split every nonzero relation at W. The root inclusions still have
literal left inverses, giving both D-families at R. None of these proofs
uses external standardness of ω.

The singleton-cell atom proof is unchanged. Its propositions are false
at the new objects. At R every old profile uses only the one individual
marker, together with the original signature. At each specified
singleton cell its interpretation is constant over the complete marked
cell diagram. This remains an internal syntactic induction for the
internally coded profile terms. Therefore each nonzero cell has only
zero and itself as root subparts. In the unary case the two cells fix
c to bottom or top, and every new substitution continues to fix c.

Every internal subset of a new object's actual argument product remains
an available current extension: prescribe one fixed extension for each
new target and the bottom old profile. At R one may instead prescribe
its extensions independently at its three unique new-target arrows.
These assignments have finite support. Internal global well-ordering
therefore gives the two choice schemata at both targets, as required.

### Arithmetic at the singleton root

The fact that R has one individual causes no arithmetic collapse.
Its number entities have old profiles as well as current extensions.
Internal Replacement forms the orbit b₀=0_e, bₙ₊₁=Suc_e(bₙ). An admitted
current predicate with exactly that orbit as extension proves that the
impredicative number domain is contained in the orbit. Internal induction
gives the reverse containment.

Distinct internal indices still give distinct entities bₘ and bₙ.
For any internally finite k≥max(m,n), the old category contains the full
extensional model with k individuals, where the two finite-cardinality
terms differ (take k≥1 as well). These models need no unbounded powerset
allowance: each individual typed carrier is finite, and the entire
hierarchy is coded on ω by finite function tables, recursively in the
internal type codes. Its term-evaluation tables and truth clauses are
coded in the same way. The uniform finite-model construction and its C
soundness verification are available inside S. The two root numeral
profiles consequently differ. The interpretation of c may be chosen
bottom in these models.

Include the fixed proof that Max implies I_e and the fixed PA and
arithmetic-correctness derivations in the finite fragment. The required
Max instances hold by the argument below. The recursive characterization
of addition and multiplication, together with the admitted internal
current graphs, identifies the arithmetic on the orbit with ω^S.
Thus R's arithmetic falsifies A even though its individual domain is
a singleton. This argument uses internally finite numerals, not just
the external standard numeral sequence.

### Bounds and the finite-proof conclusion

New arrows are coded substitutions, hence subsets of ω. Old models,
assignments, and term profiles also have a fixed finite coding bound.
At a new relational type, the varying coordinate data are subsets of
the product of a fixed arrow-code set with the already constructed
argument domains. A powerset and Separation supply the required carrier;
finite support and the old-profile condition are definable restrictions.
Only finitely many new types occur in the expanded proof and auxiliary
derivations, so a sufficiently large fixed finite-rank S suffices. The
whole old category stays coded on ω. In particular the construction
does not assume full current domains at all internal types at once.

For every used Max axiom diamond P_i, the true Π₁ sentence
Con(C_L+P_i) holds in S. Its internal Henkin model belongs to the old
category and supplies a nonzero old profile of P_i at each new object.
Thus the required Max instances hold. The coordinate and support
arguments verify all other used axioms of B_L, and the root falsifies A.
This contradicts the alleged finite proof and establishes the upper
inclusion in (3). The lower inclusion follows from M_L⊆B_L. QED.

In particular B_L+Γ_L and B_L+not Γ_L are both consistent. By contrast,
K+B_L is consistent and proves Γ_L; the previously constructed model
witnesses its consistency with standard arithmetic. None of these
statements supplies Γ_L+D(not Γ_L): every literal
retraction in the construction still identifies the numerical systems
at its source and target. Equation (3) isolates an arithmetic limitation
of this entire structural comparison family; it does not resolve either
unrestricted SP target.

The resulting comparison has two incomparable branches:

    M_L < K < K+B_L < SP_L,
    M_L < B_L < K+B_L < SP_L.

Every theory before SP_L in these lines is consistent. The strictness
M_L<K and B_L<K+B_L is witnessed by Γ_L, using (3). The reverse
noninclusion K not entailing B_L is witnessed by the full-current
two-individual M_L-model of the model lemma in the ladder's §§1 and 4:
it satisfies K and refutes E₁, which belongs to B_L. The same model
establishes M_L<B_L, and E₁ establishes K<K+B_L. Finally the standard
three-object model satisfies K+B_L and HΓ_L, so it refutes the licensed
D(not Γ_L) instance and establishes the final strictness. These are
strict consequence-theory inclusions, not an assumption that SP_L itself
is consistent.
