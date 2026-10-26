# Max excludes sequence shifts, Boolean stacks, and endomorphism closure

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Surjective operations cannot identify protected pairs

Fix a relational type τ, a current domain D:τt, and an admitted operation
f:τ→τ which currently maps D onto D:

    ∀x(Dx→D(fx)),       ∀x(Dx→∃y(Dy∧fy=x)).

Neither assertion is boxed. Only the second is needed below once the
specified inputs belong to D.

**Theorem 1.1 (C + pure Max).** For a,b∈D,

    fa=fb  →  ◇(a=b).

Thus a current surjection cannot send necessarily distinct current domain
members to the same object. Any fixed finite family with one common
f-value can possibly coincide simultaneously; no assertion is made about
one possibility collapsing an arbitrary infinite fibre.

**Finite proof.** Let m=cτ, the bound from the singleton full model.
Max supplies `◇AtMost_m(τ)`. For a,b∈D with fa=fb, current surjectivity
supplies two finite chains:

    a₀=a, a₁,...,a_m∈D,       f(a_(i+1))=a_i;
    b₀=b, b₁,...,b_m∈D,       f(b_(i+1))=b_i.

Only finitely many existential witnesses are chosen; no Choice schema is
used. NI makes these identities and fa=fb necessary. At an AtMost_m
possibility, some a_i=a_j with i<j. Applying f i times gives
a₀=a_(j−i), so applying it another j−i times gives
`f^(j−i)(a)=a`. Thus a has a positive period at most m, and similarly
b does. If q=m!, then f^q(a)=a and f^q(b)=b. Applying f^(q−1) to
fa=fb gives a=b.

This finite case split uses only finitely many transported current
identities. It proves `□(AtMost_m(τ)→a=b)`, which together with the
Max possibility gives ◇(a=b). For several inputs choose a chain for
each and use the same finite possibility. No assertion about preimages
of new future members of D is used. ∎

The [finite-quotient theorem](finite-collapse.md) gives the
same conclusion externally: a quotient of a surjective unary algebra is
surjective, and a finite surjection is injective. The proof above isolates
the finitary C argument. The conclusion is not current injectivity;
current fibre collisions remain possible provided their inputs can merge.

## 2. Integer sequences have arithmetic but cannot have a shift operation

Let R=Z^N be the ordinary standard ring of all integer sequences, with
pointwise addition, multiplication and negation. Its zero and one are
the constant sequences 0 and 1. Let T(x)ₙ=x_(n+1) be left shift.

**Theorem 2.1.** At every fixed relational type, Max forbids an operational
copy of R with protected zero and one and an ambient representative of T.
Addition and negation suffice; multiplication is unnecessary.

If T were represented, abstraction would give the admitted difference
operation Δ(x)=T(x)−x. It is currently onto R: for any y take the standard
integer sequence x₀=0, x_(n+1)=xₙ+yₙ. Then Δ(x)=y. But
Δ(0)=0=Δ(1), contradicting Theorem 1.1 and the protected unit. ∎

**Nonvacuous positive model.** The unital homomorphism

    χ:R→F₂,       χ(x)=x₀ modulo 2

and quotient lifting give a pure-Max model containing an et-copy of the
**entire standard R**, with addition, multiplication, negation and
protected zero and one. Its root profiles may make those two objects
literally logical bottom and top. Composition represents every pointwise
integer polynomial operation.

The same model can represent zero insertion J(x)=(0,x₀,x₁,...):
χ(Jx)=0 always, so expand the quotient algebra by the constant-zero
unary map and lift it together with the ring operations. The ordinary
graph of T exists at the full current root and is a left inverse of J
on its image. It has no ambient operation representative.

Thus the standard sequences, arithmetic, zero insertion and uniquely
defined shift graph are all available. What fails is an exact operation
implementing this basic sequence transformation, at any relational type.

**Scope.** R is the external standard sequence ring realized as a current
structure. The negative argument also applies to any current structure
where the difference map is onto and kills a protected pair. It does not
assume that an arbitrary Henkin collection called “sequences” contains
every recursively defined partial-sum sequence.

## 3. No Boolean stack at any fixed relational type

Let D be a nonempty current domain at relational type τ. Suppose admitted
operations push₀,push₁,pop:τ→τ and head:τ→t map D as appropriate, and
for every current x∈D satisfy

    pop(push₀(x))=x=pop(push₁(x)),
    head(push₀(x))=⊥_t,       head(push₁(x))=⊤_t.

The three τ-valued operations map D into D; values outside D are
unrestricted. No empty-stack convention, induction, length function,
or numerical coding is assumed.

**Theorem 3.1.** C plus pure Max excludes this package at every fixed τ.

The push₀ recovery equation makes pop currently onto D. For any x∈D,
push₀(x) and push₁(x) have the same pop-value. Their head equations are
necessary by NI. Since logical bottom and top are necessarily distinct,
the pushed objects are necessarily distinct by congruence. This
contradicts Theorem 1.1. ∎

The readout labels are actual truth values, or any other protected pair.
Two coalescible objects merely named “false” and “true” do not satisfy
the equations. This is an obstruction to **every encoding** of the stack,
without Frege numberhood or a noncollapse premise, rather than another
calculation about the old predecessor/parity graphs.

The positive boundary is nonvacuous. Encode all ordinary finite binary
words in one common-component fibre at et in a free-current Max model.
The trivial quotient realizes push₀, push₁ and pop simultaneously,
indeed every word-valued function. Every ordinary graph, including
truth-valued head, exists currently. What cannot be added is an ambient
head with the protected truth-value outputs. Distinct word codes in
that fibre can coalesce, directly displaying the failed readout.
There is still an admitted predicate whose **current truth** records
the first bit. Current truth-equivalence is weaker than the displayed
identities with the constant bottom/top propositions; the theorem concerns
the latter exact Boolean output requirement.

## 4. Matrix closure and an endomorphism obstruction at every type

### A finite matrix obstruction at et

The integer ring has an operational et-copy with protected zero and one.
Its ordinary 2-by-2 matrix ring M₂(Z) has no such copy at et. A unital
map M₂(Z)→F₂ would preserve

    E₁₂E₂₁=E₁₁,       E₂₁E₁₂=E₂₂,       E₁₁+E₂₂=I.

Commutativity makes the images of E₁₁ and E₂₂ equal; their sum is zero
in F₂, contradicting the protected identity. Apply the et ring criterion.
This obstruction is type-specific: no failure at all larger types is
inferred from it.

### The standard endomorphism ring has no nonzero finite quotient

Let V=⊕_(n∈N) Z e_n and E=End_Z(V), with pointwise addition and
composition. Define ordinary endomorphisms by even/odd coordinates:

    i₀(e_n)=e_(2n),            i₁(e_n)=e_(2n+1),
    p₀(e_(2n))=e_n,            p₀(e_(2n+1))=0,
    p₁(e_(2n))=0,              p₁(e_(2n+1))=e_n.

They satisfy three ring identities:

    p₀i₀=1,       p₁i₁=1,       i₀p₀+i₁p₁=1.       (*)

Every finite unital ring is directly finite: yx=1 implies xy=1.
Indeed left multiplication by x is injective (cancel with y), hence
surjective. Choose z with xz=1; then y=y(xz)=(yx)z=z, so xy=1.

In any nonzero finite image of E, the first two equations in (*) therefore
give i₀p₀=i₁p₁=1. The third gives 1+1=1 and hence 1=0, a contradiction.
Thus E has no nonzero finite quotient of **any** size.

**Theorem 4.2.** At no fixed relational type can pure Max have an
operational copy of E with protected zero and identity.

Finite-quotient necessity would yield a quotient of size at most cτ
preserving that distinction. More generally the same conclusion holds
for any current represented unital ring containing witnesses to (*).
The equations give a finite obstruction: at an AtMost_m possibility,
current yx=1 and the finite list x⁰,...,x^m force xy=1 by pigeonhole
and cancellation. Apply this to both pairs in (*), then use the
transported third identity. No universal ring law on future domain
members is required.

For detail in that finite cancellation: a collision x^i=x^j, i<j,
and the current identities y^i x^i=1 and y^i x^j=x^(j−i) make
x^d=1 at that possibility, where d=j−i. The current identity
yx^d=x^(d−1) then gives y=x^(d−1), and hence xy=1. Only finitely
many such current identities are transported by NI.
Finally the current additive identities (-1)+(1+1)=1 and (-1)+1=0
make a possible equality 1+1=1 imply 1=0, again by NI and congruence.

The starting module is compatible: taking the coefficient of e₀ modulo
two maps V onto C₂. Quotient lifting therefore gives a Max model of
its standard additive group with each integer scalar unary map and a
protected pair 0,e₀. The endomorphism obstruction is not due to
inconsistency of that module or divisibility of its additive group.

When zero and identity are genuine operations on a module with a protected
pair 0,v, their distinction is automatically necessary: their actual
values at v are 0 and v, and NI transports those identities. Thus the
protected-unit premise has an ordinary mathematical meaning here.
The conclusion concerns a **coherent operational ring realization**.
Bare current endomorphism graphs do not automatically supply one, and
current agreement on the module is not silently promoted to identity
of whole function objects.

## 5. Assessment and limits

The simplest consequence is the Boolean-stack prohibition; the familiar
algebraic example is the missing shift despite operational integer-sequence
arithmetic. The endomorphism example gives a further reason that raising
the carrier type cannot systematically restore ordinary algebraic closure.

These belong to one finite-image research development, not a count of
every example as a separate major theorem. The surjection result has a
direct finite C proof; the positive models use earlier quotient lifting.
The examples do not assume a field or divisible group and do not merely
rename the canonical Frege numerical entities.

Nothing here proves Max inconsistent or denies ordinary current sequence,
module or ring mathematics. The relevant functional graphs still exist.
The failures concern operation representatives with exact identities and
the indicated protected outputs. Current surjectivity is not boxed, and
external standard structures are distinguished from arbitrary Henkin
versions of their vocabularies.

## Sources

* This note, §§1–5, direct source `misc`, unpaginated, for the finite
  surjection proof and new sequence, stack, matrix and endomorphism results.
* [Finite quotients](finite-collapse.md), §§1–3, for the
  necessary bounded quotient and constructive positive-model theorems.
* [Finite carrier bound](finite-type-capacities.md),
  §§1–3, for cτ and the pure Max possibility instance.
* [Current analysis model](current-analysis-under-max.md),
  Construction, for the free-current positive witnesses.
* Bacon and Dorr, *Classicism*, 16 May 2023 draft, §2.4, pp.35–36,
  for pure Max. These new algebraic deductions are not attributed to it.
