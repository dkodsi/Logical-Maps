# A Henkin countermodel to necessary noncollapse from predecessor

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Exact question and already established direction

Fix the original finitary relational type system of C. For a closed type
`σ`, put `νσ:=(σt)t`, and use the existing Frege definitions `0σ`, `Sσ`,
`Nσ`, and `Iσ:=◇I*σ`. C proves `Iσ↔I*σ`.

    PredOpσ := ∃P^(νσ νσ), ∀n (Nσ n → P(Sσ n)=n).

No values at zero or nonnumerical inputs are prescribed. Since zero is
never a successor in C, PredOpσ implies current Iσ: apply P to an equality
of successors of current numbers to obtain their equality. No separate
current noncollapse assumption is needed.

The reverse implication `□Iσ→PredOpσ` was already proved by stable
least-preimage realization in
[numerical-inverses.md, §2](numerical-inverses.md). The implication
`PredOpσ→□Iσ` holds in action models extensionally full at every object,
as proved in [model-separations.md, §8](numerical-models.md). The present
note disproves its extension to arbitrary Henkin C models.

We use the free-current-root algebra and its C-validity verification in
[Frege infinity, §§37.4–37.5](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md).
That construction accepts arbitrary C component algebras; it does not
require full action-model components. The necessary clauses are repeated
below so that the new use can be checked independently.

## 2. A compactness component with nonstandard numerical collapse

Write `kσ:=Sσ^k(0σ)` only for external standard integers `k≥0`. Expand
the auxiliary language by constants

    pσ : νσ → νσ,                  for each closed counting type σ;
    hσρ : νσ → νρ,                for each ordered pair σ,ρ.

All these operation types are admitted. The constants are construction
devices; the final claims about their existence are in the original pure
language.

Consider the following countable theory Γ over C:

1. `¬Iσ`, for every closed counting type σ.
2. `pσ((k+1)σ)=kσ`, for every σ and every external standard k.
3. `hσρ(kσ)=kρ`, for every σ,ρ and every external standard k.
4. For each external positive integer r, at least r pairwise distinct
   propositions exist.

Clause 3 is not needed for the predecessor counterexample; retaining it
gives the simultaneous arithmetic-transport strengthening. Clause 4 ensures
an externally infinite proposition carrier in the eventual Henkin
component; it will give quantified Infinity_t at the full current root.

**Lemma 2.1.** Every finite subset of Γ is satisfiable in a finite full
standard S5 model of C.

**Proof.** Choose a finite nonempty set of worlds W and a finite nonempty
individual set E, both sufficiently large. Use the full constant-domain
intensional model:

    D_e=E;       D_t={0,1}^W;
    D_(αβ)= all functions D_α→D_β,                 β≠e.

Application is ordinary function application, truth is evaluation at a
world, the quantifiers use the full constant type domains, and equality
of objects is represented by the constant true or constant false
proposition. This is the familiar full standard S5 interpretation of C.
In particular it validates its abstraction rules and Logical Equivalence.

Every type carrier is finite. The current Nσ-field is the standard
successor orbit: the full predicate domain contains that orbit as an
extension, so the defining induction clause excludes every other object.
Consequently Nσ is finite. Successor cannot be an injection on a finite
set whose range omits zero; therefore I*σ, hence Iσ, is false at every
world, at every type. This verifies clause 1, even for types not mentioned
in the chosen finite subset.

Increasing |E| and |W| makes the carriers of every fixed type large
enough for the required finite list of numerals. More explicitly, e has
|E| elements, t has 2^|W| elements, and every relational type has at
least as many elements as t, by constant functions and inhabitedness.
If |Dσ| exceeds the largest relevant index, its listed standard
numerals are distinct: a predicate with exactly k current instances
distinguishes kσ from every other listed numeral. The same calculation
holds at every world, so these distinctions are necessary.

For each of the finitely many pσ and hσρ constraints, the inputs are
pairwise distinct numerical objects, and equal inputs have the same
specified output. Full function domains therefore supply operations with
exactly the finitely prescribed values. Alternatively, the finite
interpolation construction using necessary input distinctions realizes
those values by permitted relational abstraction. The operations need
not obey predecessor or transport laws on the rest of the finite
numerical fields. Finally, choose |W| large enough for the finitely many
propositional-size requirements. ∎

Because C is a finitary theory with the standard Henkin/BBK completeness
construction, Lemma 2.1 gives a Henkin C algebra K satisfying all of Γ.
This is compactness for Henkin semantics, not compactness for full standard
models. Equivalently, each finite proof of a contradiction would use a
finite part of Γ and would contradict Lemma 2.1; a complete witnessed
extension and its quotient by provable identity give K. The relevant
completeness source and term-algebra construction are specified in
[Frege infinity, §§37.2–37.3](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md).

Thus K has all the following properties simultaneously:

* `¬Iσ` holds for every closed counting type.
* Each pσ is correct on every *standard* successor numeral.
* Each hσρ gives every standard cross-type numerical value.
* D_t^K is externally infinite.

There is no contradiction. The universal numerical predecessor law has
not been imposed in K. In fact it fails there, since it would imply Iσ.
The component therefore has numerical objects beyond its standard orbit;
the current-field induction theorem cannot infer a universal statement
from an external infinite list of standard instances.

## 3. Attach an extensionally full current root

Choose an element a of D_e^K. Put `D_e^r=ℕ` and let `π_e` send every
root individual to a. For each relational type, flattened as
`τ=τ₁…τ_l t` (including l=0 for t), define recursively

    D_τ^r = P(D_τ₁^r × … × D_τ_l^r) × D_τ^K.

A root relation is a pair `(A,u)`: an arbitrary current extension A
and a component object u. Let `π_τ(A,u)=u`. At t this reads
`D_t^r={0,1}×D_t^K`. Truth at r is the first coordinate.

Application slices the current extension and applies the component
operation to the projected argument. For example, for an operation f
and an argument x,

    π(f(x)) = π(f)(π(x)).

The current truth of Boolean combinations and quantified formulas is
computed in the ordinary classical way over the root domains. Their
component coordinates are computed in K over its own entire domains.
Component quantifiers are not restricted to images of π. A lambda
abstraction pairs its current extension with the K interpretation of
the same body under the projected free-parameter assignment.

**Lemma 3.1.** These clauses give a C algebra at the root.

**Proof.** The current Boolean and quantifier clauses validate the H
logical axioms. Application and abstraction give β and η coordinate by
coordinate. Current equality is genuine equality of root objects. If
equality is treated through its logical definition, full current
predicate extensions distinguish any two distinct root objects, giving
the same interpretation. Its component coordinate is K's equality of
the projected objects. Substitution of identical objects therefore
preserves every operation and truth value.

For an instance of Logical Equivalence, use its actual H-proof
certificate. H-equivalent bodies agree in current truth under every
root assignment, so their root abstractions have the same current
extension. The corresponding component abstractions are identical in K,
since K satisfies C. Thus the root abstractions are literally identical
in both coordinates. This uses only H-equivalence, never an equivalence
derived from the additional assumptions in Γ.

All these clauses are defined at every admitted type. No countable union
has to be admitted in K: arbitrary current extensions are supplied by
the first factors of the root domains. This is exactly the free-current
construction recalled in §1. ∎

In particular, for a proposition q,

    r ⊨ □q  iff  q^r=(true,⊤^K).

This follows from C's definition `□q := q=⊤`. It lets us check the
failure of necessary noncollapse without pretending that K itself is a
single ordinary Kripke world.

## 4. Root numbers are standard; predecessor is genuinely universal there

**Lemma 4.1.** At r, for every σ,

    {n : r ⊨ Nσ n} = {kσ^r : k∈ℕ}.

**Proof.** The full current predicate factor contains the external
standard successor orbit as a current extension; choose any component
coordinate, for example bottom. That predicate is currently zero-containing
and successor-closed. The defining induction clause for Nσ therefore
puts every root number in the orbit. Conversely every standard numeral
satisfies every current inductive predicate, by external finite induction.
This proves equality of current extensions, without identifying any
two merely coextensive intensional objects. ∎

Every root type carrier is externally infinite. The individual carrier
is ℕ, the proposition carrier is infinite by clause 4 of Γ, and the
recursive full current relation domains are infinite at every higher
type. Full current extensions therefore distinguish every two standard
σ-numerals by a predicate with exactly one of their indicated finite
cardinalities. Thus the root standard orbit has no repetitions.

It follows both that Iσ holds at r and that the **quantified** Infinity
axiom holds there at every σ: all root numbers are standard finite
cardinalities, and no such cardinality counts its infinite type domain.
In particular both requested axioms Infinity_e and Infinity_t hold.
This is more than verification of each finite lower-bound instance.

Now lift pσ to a root operation Pσ. Its component coordinate is pσ^K.
Define its current extension, with `X:σt`, by

    Pσ^0(b,X)  iff  ∃k∈ℕ
                     [b=(k+1)σ^r ∧ r ⊨ kσ^r(X)].

This is an external specification of a permitted full current extension,
not an object-language infinitary disjunction. No additional predicate
or inverse is required to exist in K.

For each standard k, the current profile of `Pσ((k+1)σ^r)` is exactly
the current profile of kσ^r. Its component coordinate is

    pσ^K((k+1)σ^K)=kσ^K,

by Γ. Hence these two root objects agree in both coordinates:

    Pσ((k+1)σ^r)=kσ^r.

By Lemma 4.1 these are **all** root numerical arguments. Therefore
`r⊨PredOpσ`, for every closed counting type σ. This is an identity of
intensional output objects, not merely a current coextension claim.

## 5. Necessary noncollapse fails, and transport can hold simultaneously

The component coordinate of the root term Iσ is its K value. Since
`K⊨¬Iσ`, that value differs from `⊤^K`. Therefore

    r ⊨ Iσ ∧ ¬□Iσ,

for every σ. Equivalently, the root admits a possibility at which numerical
noncollapse fails. Its predecessor law is valid on all current numbers,
but it does not transfer universally to the extra component numbers.

The constants hσρ in Γ can be lifted in the same way. Give a root
operation Fσρ component coordinate hσρ^K and current profile

    Fσρ^0(b,X) iff ∃k∈ℕ [b=kσ^r ∧ r ⊨ kρ^r(X)].

Then `Fσρ(kσ^r)=kρ^r` as an identity of root objects for every standard
k. By Lemma 4.1, Fσρ preserves zero and successor on the entire root
numerical field. Every canonical arithmetic-transport instance ATσρ
therefore holds, nonvacuously.

**Theorem 5.1.** In the ordinary classical metatheory, there is a Henkin
C model with a designated root satisfying simultaneously, for every
closed counting type σ and every ordered pair σ,ρ:

    PredOpσ;       Iσ;       ¬□Iσ;       ATσρ;

and satisfying the quantified Infinity axioms at e and t (indeed at
every closed counting type).

Consequently neither PredOpσ nor the entire collection of canonical
transport and predecessor principles entails □Iσ over unrestricted C.
The construction uses Henkin completeness/compactness and ordinary
set formation; it makes no claim of a full standard countermodel.

## 6. The exact transfer failure

The obstruction is now concrete rather than speculative:

1. The root's numerical field is the external standard orbit.
2. Its predecessor identities are genuine identities and persist to K.
3. They give predecessor at every standard numeral of K.
4. K has additional numbers; its universal predecessor law fails, as
   does Iσ.

Here “new” means new membership in the numerical field, not necessarily
a new underlying entity. In fact C's equivalence
`¬Iσ ↔ Nσ(bottom_νσ)` identifies a concrete new number in K. The same
bottom entity has a root representative but is not a root number.
Every standard K numeral remains distinct from bottom: otherwise its
successor would be identical to it, and the standard predecessor
identities would force a contradiction by finitely many backward steps
to zero. Thus this component number lies outside the transported root
numerical orbit.

Thus the invalid step is passing from identities at the transported
current numbers to a universal identity over all component numbers.
Neither Necessity of Identity nor current numerical induction supplies
that passage. In particular full current extensional comprehension is
insufficient: it is present at r in this countermodel.

For comparison, PredOpσ does force stable distinctions among current
numbers. Fix its witness P. Use numerical induction on n to prove

    ∀m∈Nσ, n≠m → □(n≠m).

At n=0, any distinct numerical m is a successor by the numerical cases
lemma, and zero is necessarily distinct from every successor. For
n=S(k), split m into zero or S(l). The zero case is immediate. In the
successor case current inequality gives k≠l; the induction hypothesis
makes that inequality necessary, while NI makes both equations
`P(S(k))=k` and `P(S(l))=l` necessary. Future equality of the successors
would contradict their necessarily unequal P-images. This proves the
induction step, including internally nonstandard current n and m.

In particular each current number remains distinct from its successor.
Since `S(bottom)=bottom` is a C identity, each current number remains
distinct from bottom. None of this excludes a **new** numerical bottom
in K. The countermodel has exactly that behavior.

The converse `□Iσ→PredOpσ` remains valid in C. A sufficient extra
condition for the forward implication is numerical collection at σ:
the current predecessor equations are necessary pointwise by NI, and
collection turns them into `□∀n∈Nσ, P(Sσ n)=n`. Successor is then
necessarily injective on all future numbers, yielding □Iσ. The full-model
standardness argument in the earlier note is a different sufficient
transfer mechanism.

No claim about NInv or NSections is needed in constructing the model.
The separate proof in
[numerical-predecessor-sections.md](numerical-sections.md)
now establishes `AT ↔ NInv ↔ NSections` over C; its prefix, bounded
collection, and least-preimage arguments were independently reviewed by
this note's author. Applying that theorem, the same root also satisfies
NInv and NSections while necessary noncollapse fails at every type.
This is an ordinary mathematical consequence of the separately reviewed
theorem, with no additional formal verification claim.
