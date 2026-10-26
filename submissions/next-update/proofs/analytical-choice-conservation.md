# Analytical conservation: the relative-constructibility route

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Exact statement and source inputs

Keep the original finitary relational C. Put

    B∞ = C + □Plenitude + Infinity_e + Infinity_t,
    F∞ = C + □Functional Choice + Infinity_e + Infinity_t,

with the two quantified Infinity principles. Interpret second-order
arithmetic at N_e, with set variables ranging over current numerical
extensions and set equality read extensionally. **Theorem:**

    F∞ ⊢ A  iff  B∞ ⊢ A       for parameter-free Π¹₄ sentences A.       (1)

Finite tuples in a quantifier block can be combined by numerical pairing.
Thus write A as `∀X∃Y∀Z∃W θ(X,Y,Z,W)`, with θ arithmetical. All numbers
and sets below are internal unless explicitly stated otherwise.

Three primary inputs are used, with different roles:

1. [McLarty, *Interpreting set theory in higher order arithmetic*, v5](https://arxiv.org/pdf/1207.6357),
   §§2–5, printed pp.2–6, especially Theorems 4.3, 5.2–5.3: finite-order
   arithmetic supplies suitable-tree and constructible interpretations
   with any fixed finite powerset height and global well-ordering. The
   canonical descending-number tree preserves ω. This is the source
   already used in [Frege arithmetic §36](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md)
   and the [full-Choice arithmetic audit](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/full-choice-arithmetic-conservativity.md).
2. [Simpson's author-hosted introduction](https://sgslogic.net/t20/sosoa/chapter1.pdf),
   printed p.56, outline of §VII.4: Σ¹₂ formulas are absolute to HCL(X)
   in the internal set interpretation of Π¹₁-comprehension. The statement
   is about internal interpretations, not only externally well-founded
   models. The detailed book location is §VII.4; only the author's
   introduction was available in this check.
3. [Montalbán–Shore, *The Limits of Determinacy in Second Order Arithmetic*](https://pi.math.cornell.edu/~shore/papers/pdf/Delta4DetSub.pdf),
   Proposition 1.4, printed pp.4–5: they apply that internal relative-L
   machinery to Π¹₄ conservation for ZFC without Powerset, with Collection,
   over Z₂. Their counterexample-preservation argument works for arbitrary
   Z₂ models. Their set theory alone does not supply the finite iterated
   powersets needed for an arbitrary finite typed proof.

The added argument connects the finite-rank interpretation to the low
relative-constructible real domain. Merely juxtaposing these source
theorems would not by itself prove (1).

## 2. Relative finite-rank interpretation: the Π¹₂ milestone

Let M be the full finite-type extensional numerical hierarchy obtained
from a B∞ model by the existing current-quotient interpretation. It
satisfies every fixed Z_m, including full comprehension with parameters
at any finitely many higher types. Its first two sorts are exactly the
source numbers and their admitted extensional properties. Neither its
numbers nor its internally well-founded relations need be externally
standard or well-founded.

Fix X in M's numerical powerset. The needed relativized form of McLarty
is:

**Relative finite-rank lemma.** For each external finite rank bound n,
M interprets a K satisfying ZFG[n+] and `V=L[X]`, with its ω identified
with M's numbers, containing the given X with its original membership.
Every K-real pulls back to an M-real with the same number membership.

Here is the extra parameter audit. Code X by the ordinary number-labelled
tree for its subset of the canonical ω-tree. Start constructibility from
the transitive base containing ω and X, or equivalently add X as a fixed
predicate to the Gödel construction. Every definability, satisfaction,
least-code and ordinal-comparison formula in the finite-order proof may
use that fixed second-order parameter. Full comprehension allows it.
Since X is a real, its transitive closure has a canonical countable
enumeration; there is no arbitrary unordered set of generators requiring
a new Choice premise. The relative constructible order is definable.

The suitable-tree construction and successive enlargement of its
definably well-ordered label class are unchanged. Each enlargement
includes the previous class as an initial segment. At each stage the
relative constructible interpretation extends the preceding one; the
finite cardinal-growth argument then supplies the requested n. The
hereditary-size restriction is taken **within relative L**, keeping
global selection and Replacement. Do not use the displayed condition
`u⊆rng(f)` from McLarty's H-definition without that restriction: doing
so would incorrectly admit every ambient real using the identity of ω.

The number trees and their arithmetic do not change. For a K-real r,
full comprehension in M forms

    r↓ = {m : canonical_number_tree(m) ∈* r}.                         (2)

The right side may quantify over the finitely many higher types used to
represent r. Such parameters are allowed. Extensionality in K gives
injectivity of this real map; its membership agrees with K. Formula (2)
does not assert that all M-reals are in K. The distinguished X is in K
because it was an initial constructibility parameter.

**Π¹₂ consequence.** Suppose M falsifies `∀X∃Y θ(X,Y)` and choose a
counterexample X. Construct K high enough for a proposed finite F∞ proof.
Every Y of K is an old M-real by (2), and arithmetical truth is unchanged
because the numbers, operations and real memberships agree. Thus K
still falsifies the sentence. The established internal full S5
interpretation of the finite proof fragment in K validates its Choice
and both Infinity assumptions and preserves its second-order arithmetic.
This contradicts that proof. No Shoenfield absoluteness is needed for
this Π¹₂ step.

The finite-rank lemma is the source-relativization argument just checked;
it is not inferred from equiconsistency alone.

## 3. The needed real-part invariance lemma

Let H=HCL^M(X), using the ordinary **number-labelled** suitable-tree
interpretation in M and its relative constructible hereditary-countable
part. Let K be the higher-labelled relative construction of §2, with
enough rank for the finite proof. The stronger bridge is

    Real(K)↓ = Real(H)↓.                                           (3)

This is equality of interpreted real domains under (2), not equality of
their sets, ordinals, higher types or whole theories. In particular it
does not identify either real domain with all reals of M.

### 3.1 The lower interpretation embeds, and its reals survive

Embed the original number labels into the enlarged well-ordered label
class C. An old suitable tree stays suitable: a path using its embedded
nodes pulls back uniquely to a numerical path. Tree equality and
membership between old objects are preserved in both directions.
A higher-type bisimulation between two number trees pulls back to a
numerical binary relation by M-comprehension, so additional relation
types do not silently identify new pairs of old objects.

The coded stages of the old relative constructible hierarchy therefore
embed in the higher tree interpretation. Their finite set operations,
membership, satisfaction on a fixed stage, and definable-subset
construction agree. This includes internally nonstandard formula codes:
pull both old and higher satisfaction relations back to numerical codes
for the old countable stage. They satisfy the same compositional
clauses; M's number induction on internal formula complexity proves
uniqueness, hence agreement on every internal code. Thus each old
relative-constructible real remains
relative-constructible. Its transitive closure has a constructible
countable enumeration, so it is retained in every relevant H_Θ part
with Θ≥ω. This proves the right-to-left inclusion in (3).

### 3.2 Countable diagrams from K are well-founded in M

Suppose a transitive K-set A has in K an enumeration by ω. Pull its
membership diagram back to a numerical relation E in M, replacing
duplicate enumerators by their least numerical representatives.
Then E has no descending sequence admitted by M.

For otherwise let such a sequence be given. Take a suitable C-labelled
tree T representing A. Begin with the least daughter of T representing
the sequence's first element. Lift the sequence to a branch of T. At each
finite stage, the current subtree represents the current member of A;
the next related member is represented by at least one successor
subtree. Choose the least suitable successor in the fixed definable
well-order of C. These are unique choices. Numerical recursion forms
the finite prefixes, and comprehension forms their coherent sequence.
This recursion is available in the extensional numerical hierarchy;
equivalently, B's higher-type numerical recursion from
[the new recursor theorem](alternating-bit-recursion.md)
handles these relationally coded nodes. No arbitrary choices of
representatives are assembled. Include any additional finite type room
for these finite histories and their sequence in the source hierarchy
chosen for the proof. The resulting admitted M-branch
contradicts the suitability of T.

This argument is internal to M. It does not use external transfinite
induction on T. It supplies the important extra correctness which
K's satisfaction of Foundation by itself would not supply.

### 3.3 Every K-real has an old countable constructibility certificate

Fix r∈Real(K). Inside K, use `V=L[X]` to choose a constructible stage
containing r and X. Form its countable elementary Skolem hull containing
every natural number and the two objects r,X, using the definable
constructible order. The hull construction uses a countable list of
formulas, unique least witnesses, finite iteration and Replacement.
Condensation for relative L over a real gives its transitive collapse
as a countable L_β[X]. The collapse fixes ω,r,X. These arguments need
Separation and Replacement on the relevant sets, not full Powerset.

Retain more than the membership diagram. In K, also collect the sequence
of relative constructible stages through β and the satisfaction relations
used to verify their definable-subset steps. Since β and L_β[X] are
countable in K, this whole certificate has a countable transitive closure
in K: its additional items are indexed by the countable stage order,
formula codes and finite tuples from countable sets. K's own Choice and
Replacement supply one enumeration. Applying §3.2 to that larger
transitive closure reflects well-foundedness for the entire certificate.

The enumeration, membership diagram, and coded hierarchy/satisfaction
relations now pull back to numerical relations in M by (2). Their
arithmetic verification is preserved,
including quantification over all internal formula codes. Section 3.2
makes the membership/ordinal diagram well-founded in M's sense.
Consequently this is a number-tree certificate in M that r is
constructible from X. Since a constructible real is hereditarily
constructibly countable, r belongs to HCL^M(X). This proves the
left-to-right inclusion in (3).

The key claim is about the **certificate**, not merely an external
isomorphism with an object called L_β[X]. Its pulled-back numerical
relations must witness the same internal relative-constructibility
definition used in the source HCL interpretation. The preceding
verification, together with the least-successor lift, is what supplies
that compatibility.

## 4. Completing the Π¹₄ proof

Assume B∞ does not prove A. First-order/general-model completeness gives
a B∞ model falsifying A, hence its numerical hierarchy M with

    M ⊨ ∃X∀Y∃Z∀W ¬θ(X,Y,Z,W).

Fix such an X. Suppose π is a finite F∞ proof of A. Include its complete
finite list of types, abbreviation expansions, H-certificates for
Logical Equivalence, and second-order arithmetic decoding types. Build
the relative K of sufficient finite rank.

For each Y∈Real(H), M satisfies `∃Z∀W ¬θ(X,Y,Z,W)`, a Σ¹₂ formula with
parameters in H. The imported internal Shoenfield theorem gives this
same assertion in H. Hence H falsifies A. By (3), K has exactly H's
numbers and reals, with the same arithmetic and memberships. Induction
on the fixed finite syntax of A therefore gives K⊨¬A.

Inside K build the full internal S5 hierarchy only for π's finite type
fragment, as in the existing arithmetic audit. Global well-ordering
supplies the selecting operations at every world. Taking individuals
and worlds to be K's ω verifies both quantified Infinity principles.
The numerical bridge preserves all K-subsets of ω, not only its numbers:
pullback along its Frege-number bijection and rigid characteristic
predicates give the two directions. Thus π would imply K⊨A, a
contradiction. This proves (1) using the two interpretation lemmas
in §§2–3. The converse implication is immediate from
F∞⊇B∞.

No uniform finite powerset bound for the whole language is asserted.
One K is chosen after the finite proof π, and its construction uses
finitely many of M's available types. All old optional premises remain
premises; none is necessitated as a theorem of C.

**Stronger-base corollary.** The construction
uses only the source current-quotient hierarchy and preservation of its
numerical properties. Those are available already from C+I_e, the weak
numerical noncollapse assumption of the Frege notes. The finite-history
recursion in §3.2 takes place in that extensional hierarchy and does not
require an original-C operation representing it. Thus the same argument
shows Π¹₄ conservation down to C+I_e, not only B∞. In particular,

    F∞ ⊢ A  iff  B∞ ⊢ A  iff  C+Infinity_e ⊢ A  iff  C+I_e ⊢ A.     (4)

This changes
neither the two Infinity premises on F∞ nor the interpreted counting
base. It is a corollary of the transfer, not a claim that
modal or higher-type statements are conserved.

Finite real parameters are allowed through universal closure: for a
Π¹₄ formula A(P₁,...,P_k), apply (1) or (4) to `∀P₁...P_k A`.
The additional universal variables join the first universal real block.
This does not assert conservation over arbitrary additional axioms
about named parameters. Equivalently, the countermodel construction
can carry a finite tuple by coding it together with the chosen X.

## 5. Scope and sharpness

The theorem is Π¹₄ conservation, with the weaker-base extension (4). Section 3 supplies the higher-rank/low-real bridge; an arbitrary model of the boxed-Plenitude package is not assumed to be a ZF model. The entire countable construction/satisfaction certificate and the relative-L restriction on hereditary bounds are required in that argument.

The [explicit separator](analytical-choice-separation.md) gives a constructible-countable-collection formula and its typed transfer. Its universal presentation is Π¹₅, and the fixed-parameter presentation can be Σ¹₄. No minimal-complexity claim is made. The Feferman–Lévy model theorem is imported, with its source and preservation requirements stated in that proof.
