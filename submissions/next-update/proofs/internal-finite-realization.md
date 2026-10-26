# Operation realization on internally finite domains

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Framework and prior result

Work in fixed relational C. Inputs have any admitted type σ; outputs have
a relational type τ=ρ₁…ρₖt, including τ=t. Thus σ→τ is admitted even
when σ=e. Write

    Finσ(D) := ∃n (Nσn ∧ nD).

This is internal Frege-finiteness. We use the Frege definitions of zero
and successor, numerical induction, and current extension-invariance of
finite cardinality. No external enumeration is assumed.

The exact criterion for **externally specified finite lists** is already
proved in [relational-coding-recursion, §13](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-coding-recursion-20261022.md):

    ∃f ⋀ᵢ f(aᵢ)=bᵢ  ↔  □⋀ᵢⱼ(aᵢ=aⱼ → bᵢ=bⱼ).

The extension below replaces that external list by an internally finite
property and a current functional graph. It is not a rediscovery of the
finite-list theorem. Also distinguish unrestricted domain decoding,
which [domain-decoding.md](domain-decoding.md) identifies with Plenitude.

## 2. The exact internal finite-domain theorem

Fix D:σt and U:στt. Suppose U is total and single-valued on the current
extension of D:

    ∀x (Dx → ∃!y U(x,y)).

No requirement is imposed on U outside D. Define

    Compatible_D(U) :=
      ∀x x' y y' [(Dx ∧ Dx' ∧ U(x,y) ∧ U(x',y'))
                   → □(x=x' → y=y')].

The quantifiers and graph premises are current. In particular this does
not assert a boxed universal law about future members of D or U.

**Theorem 2.1 (C).** Under Finσ(D) and the displayed functionality,

    ∃f^(στ) ∀x(Dx → U(x,f(x)))  ↔  Compatible_D(U).

**Necessity.** For current graph entries U(x,y), U(x',y') with Dx,Dx',
functionality and representation give f(x)=y and f(x')=y'. NI makes both
identities necessary. At any possibility identifying x and x', congruence
for f identifies y and y'. This direction needs no finiteness.

**Sufficiency.** Induct on the numerical cardinality n, carrying universal
quantification over D and U and the conditional conclusion when nD,
functionality and compatibility hold. At zero, D has no current instances,
so the constant-bottom operation suffices.

For (Sn)D choose a with Da and n(D−a), exactly as the definition of
successor permits. Here (D−a)x means Dx∧x≠a. The restricted graph retains
functionality and compatibility. By induction choose an operation f
representing it. Choose the current unique b with U(a,b). Define the
admitted pointwise override

    f'(x)[r̄] := (x=a ∧ b[r̄]) ∨ (x≠a ∧ f(x)[r̄]).

The empty output argument tuple covers τ=t. C gives f'(a)=b.
For a current x in D−a we have U(x,f(x)), so compatibility gives

    □(x=a → f(x)=b).

At any future point and any output argument tuple, if x=a the two outputs
f(x),b agree by this implication; if x≠a the override retains f(x).
Consequently f'(x) and f(x) are necessarily universally coextensive.
Intensionality gives f'(x)=f(x), and hence U(x,f'(x)) currently. This
covers D−a; the value at a covers the remaining instance. The induction
proves the theorem for every internal finite cardinality. ∎

No optional assumption was used inside Logical Equivalence. In particular
the override does not require the old input x to stay distinct from a:
compatibility supplies the correct output when they merge.

**Corollary 2.2.** If Finσ(D) and

    ∀x x' (Dx ∧ Dx' ∧ x≠x' → □(x≠x')),

then every current total unique graph on D with relational outputs is
representable. Current equal inputs have equal outputs, necessarily by
NI; current unequal inputs stay unequal, so compatibility follows.
Neither D's rigidity nor output distinctness is required.

The same protected-domain hypothesis gives **finite functional choice**
for a merely serial relation on D. Run the same cardinality induction,
choose one current output at the newly adjoined point, and use protected
input distinctions to preserve the previous values. Uniqueness of the
given relation is unnecessary for this corollary.

## 3. Finite operation closure is exactly uniform collapse

Now let D be an internally finite domain at a **relational** type τ.
Define its uniform-collapse condition by

    ∀a b c d∈D,
      (a≠b ∧ c≠d) → □((a=b) ↔ (c=d)).             (UC)

This asserts equality of the equality propositions, equivalently the
displayed necessary biconditional. Merely requiring the diamonds of the
two equalities to agree would be weaker and is not the condition used.

**Theorem 3.1 (C).** The following are equivalent:

1. Every current transposition of two members of D, fixing the other
   current members, has an ambient operation representative on D.
2. Every current permutation graph of D has such a representative.
3. Every current total unique endomap graph D→D has a representative.
4. Every current total unique operation table Dᵏ→D has a representative,
   for each externally fixed finite positive arity k.
5. UC.

The implications 4⇒3⇒2⇒1 are immediate. For 1⇒5, take distinct current
a,b and distinct current c,d. A current permutation taking a to c and b
to d is a composition of at most two transpositions: first swap a with
c, then swap the image of b with d. The second swap fixes c. The assumed
representatives compose to an operation h with h(a)=c, h(b)=d. NI gives
□(a=b→c=d). Apply the same construction in reverse to obtain the converse
implication under the box. This proves UC without using finiteness.

For 5⇒3, let U be a current endomap graph. For two current entries
x↦y, x'↦y', if y=y' currently, NI supplies compatibility. Otherwise
current functionality gives x≠x', and UC supplies
□(x=x'→y=y'). Theorem 2.1 realizes U.

For 5⇒4, take two current input tuples with outputs y,y'. If their outputs
are currently equal, use NI. If their inputs are currently identical,
functionality makes their outputs equal. In the remaining case some
coordinate pair xⱼ,x'ⱼ is distinct and y≠y'; UC implies that a future
identity of that coordinate pair identifies y,y'. Thus a future identity
of the entire tuples identifies the outputs.

To apply Theorem 2.1, code a tuple by its haecceity
H_x̄:=λz̄.⋀ⱼzⱼ=xⱼ. C necessarily identifies two such codes exactly when
all their coordinates agree. The current property of codes of Dᵏ is
Frege-finite, by finite product and finite-image closure. Here are the
internal closure arguments, including the change of counting type.
Current extension-invariance of a numerical cardinality follows by
N-induction: the zero clause tests current emptiness; the successor
clause deletes the same witness from two coextensive properties and
applies the induction hypothesis. This gives agreement on which
properties a number counts, not identity of coextensive properties.

For a finite image at another type, induct on the **source** cardinality,
with the assertion that the image has some finite cardinality at its
own target type. Adding a source point adds at most one output point.
If that output is already present, use extension-invariance; otherwise
the fresh-point successor lemma gives a target finite cardinality for
the enlarged image. Finite unions use the same induction, adjoining one
point at a time. For a product, adjoining one point of the first factor
adjoins one finite slice, an image of the remaining product. This proves
finite product closure by induction on the finite arity and on each
source cardinality. None of these arguments enumerates a nonstandard
finite domain. Realize the graph on codes and compose with H. All output
types remain relational. ∎

This proof shows that a finite domain's possible identifications, rather
than its current cardinality alone, govern operation closure. UC allows
distinct elements to merge, but then every distinct current pair merges
at the same possibilities. No current domain predicate is boxed.

**Two useful extremes.** Every domain with at most two current elements
automatically satisfies UC, so C realizes every finite-arity table on
that domain. This does not require its two elements to remain distinct.
If D contains one protected pair, UC is equivalent to necessary
distinctness of every distinct current pair in D.

## 4. Finite fields automatically acquire all operation tables

Suppose D is a current internally finite nontrivial field, with genuine
ambient addition and multiplication representatives. The elementary
field-collapse theorem in [field-operations.md, §2](field-operations-under-max.md)
gives, for every distinct current a,b∈D,

    □(a=b ↔ z=u),

where z,u are the field's zero and one. Thus any two distinct current
pairs have necessarily equivalent equality propositions: UC holds.
Theorem 3.1 yields the following strong closure theorem:

**Corollary 4.1 (C).** Every current total unique finite-arity operation
table on such a field has an ambient representative. In particular all
current permutations, their inverses, normalized field inverse, and all
other current scalar functions on the finite field are representable.

This is pointwise existence for each current table, not one operation
uniformly choosing all representatives. No ND, Plenitude, or necessary
field laws are required. The field laws give current object identities;
NI and the finite-domain theorem do the remaining work. Finiteness is
essential to the sufficient realization theorem used here. The argument
does not establish this closure for arbitrary infinite real fields.

## 5. Changes of presentation: the exact finite criterion

For a current bijection graph U:D→E between internally finite relational
domains, Theorem 2.1 applies in either direction. Both directions have
ambient representatives exactly when current corresponding entries
x↦y, x'↦y' satisfy

    □(x=x' ↔ y=y').

Thus current graph isomorphism is insufficient; bidirectional operation
transport requires matching equality propositions. A protected two-point
domain can be mapped operationally onto a coalescible two-point domain,
but the inverse cannot be represented. This is the finite version of the
one-way real-field isomorphism in field-operations.md, §6. It identifies
the obstruction completely for finite domains rather than merely giving
a necessary condition.

## 6. Why these results do not supply another global closure axiom

Demanding realization of all graphs on all internally finite domains
recovers ND: two-point assignments to protected logical bottom/top already
force input distinctness to be necessary. ND conversely gives realization
by Corollary 2.2. Likewise, at any relational type τ, demanding swap
closure for **every** finite domain implies NDτ: place any two distinct
objects together with bottomτ and topτ in one finite domain, then use
UC and that protected pair. NDτ gives the converse.

There is a separate quantifier-order trap. Even on a fixed singleton
input domain, requiring one ambient operation which takes each current
unique graph to its output is a unique-description operator
dτ:(τt)→τ. Such an operator realizes every current total unique graph
V:στt by x↦dτ(λy.V(x,y)); conversely the corresponding Plenitude
instance supplies dτ after totalization by bottomτ. Thus uniform graph
decoding at every relational output type recovers full Plenitude.

The substantive new result here is the internal finite-domain criterion
and its swap/operation-table/finite-field consequences. These should be
used as theorems, not presented as a new axiom independent of ND or
Plenitude. The exact current-domain scope avoids both collapses.

## Sources and status

- The external finite-list result is relational-coding-recursion, §13;
  its §§12–14 supply finite-property and haecceity constructions.
- Frege finite-cardinality definitions, finite extension-invariance and
  induction are those in the map's background and the cited arithmetic
  notes. The internal override proof above supplies the new extension.
- The field-collapse input and the real-field comparison retain their
  attribution in field-operations.md. Their infinite-domain results are
  not inferred from this finite theorem.
- Every argument here is in the original finitary relational language;
  no e-valued operation, external standardness assumption, or unlicensed
  necessitation is used.
