# Numerical inverses, arithmetic transport, and decoding

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Framework, definitions, and existing inputs

Work in the fixed finitary relational language of Classicism C. All type
indices below are fixed schematic types, not object-level type variables.
Put `νσ := (σt)t`. Write `0σ`, `Sσ`, and `Nσ` for the Frege zero, successor,
and natural-number predicate; `Iσ := ◇I*σ` is numerical noncollapse.
C proves `Iσ ↔ I*σ`. Noncollapse must not be identified with actual Infinity
in bare C. An operation with numerical output is admitted even when its
counting base is `e`; no operation with output `e` is used.

The principal existing inputs are:

* The canonical zero/successor graph `Jσρ`, its current totality and
  functionality under `Iσ`, and its bijectivity under `Iσ ∧ Iρ`:
  [relational coding, §§34–35](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-coding-recursion-20261022.md).
* The same source's canonical operation `F_j : νσ → νρ`, obtained from a
  necessary injection `j : ρ → σ` by
  `j_*X := λy. ∃x (Xx ∧ y=jx)` and `F_j(n) := λX. n(j_*X)`.
  C proves that `F_j` preserves zero and successor. It carries numbers to
  numbers, and `Iρ` implies `Iσ`. With both noncollapse assumptions it is a
  numerical bijection. These facts do not assume BF or Plenitude.
* Numberhood persistence, conditional persistence of distinctness of numbers,
  and bounded numerical Barcan:
  [Frege infinity, §18](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md).
  Conditional distinctness says, for current numbers,
  `m≠n → □(Iσ → m≠n)`. Bounded Barcan says, under `Iσ` and `Nσ b`,

      [∀m∈Nσ (m≤b → □(Iσ → X(m)))]
          → □(Iσ → ∀m∈Nσ (m≤b → X(m))).                 (BBF)

  It allows arbitrary admitted predicates and parameters, including modal
  formulas, and applies to internally nonstandard bounds.
* Explicit realization of necessarily unique relational outputs by pooling:
  [choice uniformization, §2](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/choice-uniformization.md).
  We give the relevant operation explicitly below, rather than assume a
  general choice or graph-realization principle.
* The Frege Swap lemma:
  [pure possibility and infinity, §1, Lemma 3](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md).
* The existing all-counting-type predecessor obstruction for Pure Maximalism:
  [relational coding, §38](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-coding-recursion-20261022.md).

For `f : νσ → νρ`, say that it is a **numerical map** if it maps `Nσ` into
`Nρ`, and a **numerical bijection** if its restriction is a bijection of
these current fields. A **numerical inverse** is an admitted total operation
`g : νρ → νσ` which maps `Nρ` into `Nσ` and satisfies

    g(f(a))=a  for a∈Nσ;       f(g(b))=b  for b∈Nρ.

There is no requirement off the numerical fields. In particular these are
not inverse identities on the whole type carriers.

An operation `f : νσ → νρ` is **canonical** if

    f(0σ)=0ρ;       ∀n∈Nσ, f(Sσ n)=Sρ(f(n)).

Internal induction shows that it maps numbers to numbers and agrees with
`Jσρ` there. Under `Iσ ∧ Iρ` it is a numerical bijection. Conversely an
operation realizing `Jσρ` on numbers satisfies these equations.

Use the following guarded schemata, with `Iσ ∧ Iρ` in their antecedents:

* **AT:** a canonical operation exists from `νσ` to `νρ`.
* **CInv:** every canonical operation has a numerical inverse.
* **NInv:** every numerical bijection has a numerical inverse.
* **NSections:** every numerical surjection has a numerical right inverse,
  taking numerical values on the target field.

These are schemata over all fixed counting types unless indices are shown.

## 2. Least-preimage realization without numerical collection

**Theorem 2.1.** Suppose `□Iσ`, and let `f : νσ → τ`, where `τ` is any
relational output type. Assume stability of distinctions on its current
numerical image:

    ∀m,n∈Nσ, f(m)≠f(n) → □(f(m)≠f(n)).                (SI)

Then an admitted operation `μ_f : τ → νσ` selects a numerical preimage of
every member of the current image `f[Nσ]`. If `f` is injective on `Nσ`,
then `μ_f(f(a))=a` for every current numerical `a`.

**Proof.** Define the admitted least-preimage relation

    L_f(b,a) := Nσ a ∧ f(a)=b ∧
                 ∀z∈Nσ (z<a → f(z)≠b).

Under `Iσ`, numerical induction with arbitrary admitted predicates gives
the least-number principle. For a current `b∈f[Nσ]`, choose its current
least preimage `a`. This is a proof-level witness, not a simultaneous
object-level choice function.

We claim that `a` remains the unique least preimage necessarily. Its
numberhood persists and `f(a)=b` persists by Necessity of Identity. For
each current `z∈Nσ` with `z≤a`, current arithmetic gives `z<a` or `z=a`.
In the first case leastness gives `f(z)≠f(a)`, whose necessity follows
from SI. In the second case Necessity of Identity and the Peano order
laws under future `Iσ` exclude `z<a`. Thus

    ∀z∈Nσ (z≤a → □(Iσ → (z<a → f(z)≠b))).

Apply BBF at the current bound `a`, with
`X(z) := (z<a → f(z)≠b)`. Since `□Iσ`, the result excludes every future
numerical preimage below `a`, including numerical objects not currently in
the field. Consequently `□L_f(b,a)`. The C theorem that `Iσ` gives a
linear numerical order also gives uniqueness of least preimages; its
necessitation yields

    □∀a' (L_f(b,a') → a'=a).

Define, by permitted abstraction,

    μ_f(b)(X) := ∀a'^(νσ) (L_f(b,a') → a'(X)),     X:σt.

At every accessible point there is exactly the indicated witness `a`, so
`μ_f(b)` and `a` are necessarily universally coextensive. Intensionality
gives the actual identity `μ_f(b)=a`. Hence `μ_f(b)` is numerical and
`f(μ_f(b))=b`. When `f` is injective on the current numerical field, its
unique preimage of `f(a)` is `a`, establishing the left-inverse equation.
The operation is total; its values outside the current image are irrelevant.
This proves the theorem. ∎

The essential device is **bounded** Barcan at the chosen least preimage.
New preimages above it do not matter. No full BF, numerical collection,
standardness assumption, Plenitude, or Functional Choice is used. The
conclusion concerns each current input, not an unjustified boxed universal
over a potentially enlarged future image.

**Corollary 2.2.** Over C, `□Iσ ∧ □Iρ` supplies numerical right inverses
for all numerical surjections `νσ → νρ`, and numerical inverses for all
numerical bijections between those fields.

For current numerical `m,n`, the values `f(m),f(n)` are current
`ρ`-numbers. Conditional persistence of their distinctness together with
`□Iρ` supplies SI. Apply Theorem 2.1. ∎

**Corollary 2.3.** C+ND proves NSections and NInv. More generally, under
`Iσ`, ND gives numerical preimage selection for arbitrary relational images
as in Theorem 2.1.

Indeed propositional ND supplies modal axiom 5, and
`Iσ=◇I*σ` therefore implies `□Iσ`. ND at the output type supplies SI.
No boxed ND, Atomicity, or additional BF premise is required. ∎

**Corollary 2.4.** No Pure Contingency implies NSections and NInv.
For each closed counting type, `Iσ` is a closed pure sentence; NPC makes
each true `Iσ` necessary. Corollary 2.2 applies to every guarded instance.
This claim does not assert that NPC entails ND.

There is also a different sufficient package for injections.
Let `NCOLLσ` denote numerical collection
`(∀n∈Nσ □P(n)) → □∀n∈Nσ P(n)`. If `f` is injective on `Nσ` and satisfies
SI, then NCOLLσ gives a decoder on its current numerical image without
assuming `□Iσ`: for fixed `b=f(a)`, each current numerical `n` satisfies
`□(f(n)=b → n=a)`, by NI when `n=a` and SI otherwise. Collection boxes
this universally over future numbers; persistence of `Nσ a` and NI give
a necessarily unique preimage. Pool that fiber exactly as above. For a
numerical injection, `□Iρ` suffices for SI. This is an alternative bound,
not a claim that numerical collection is necessary, and this direct-fiber
argument does not cover arbitrary noninjective surjections.

## 3. Canonical inverses are exactly arithmetic transport

**Theorem 3.1.** Over C, the following all-type schemata are equivalent:

1. AT.
2. CInv.
3. Whenever `j : ρ → σ` is necessarily injective and `Iσ ∧ Iρ`, the
   canonical operation `F_j : νσ → νρ` has a numerical inverse.

**Proof, 1⇒2.** For a canonical `f : νσ → νρ`, use the opposite AT instance
to obtain a canonical `g : νρ → νσ`. Each composite preserves zero and
successor. Numerical induction gives `g(f(n))=n` and `f(g(m))=m` on their
respective fields. Thus `g` is a numerical inverse. This only proves
pointwise identities on numbers; it does not identify whole operations
by their current extensions.

The implication 2⇒3 uses the canonicality of `F_j`.

**Proof, 3⇒1.** Fix `σ,ρ` with `Iσ ∧ Iρ`, and use the common relational
counting type `κ:=σρt`. There are C-definable necessary injections

    jσ(a) := λs^σ r^ρ. s=a;       jρ(b) := λs^σ r^ρ. r=b.

Inhabitedness of the unused argument type proves injectivity, necessarily.
The induced operations are canonical maps

    A:=F_jσ : νκ → νσ;            B:=F_jρ : νκ → νρ.

Upward preservation of noncollapse gives `Iκ` from `Iσ`. By clause 3,
`A` has a numerical inverse `U : νσ → νκ`.

The inverse of a canonical numerical bijection is canonical. Explicitly,
`U(0σ)=U(A(0κ))=0κ`. If `n∈Nσ`, then `U(n)∈Nκ` and
`A(Sκ(U(n)))=Sσ(n)`. Applying the left-inverse law to this numerical
argument gives `U(Sσ n)=Sκ(U(n))`. Thus `B∘U` is canonical from `νσ`
to `νρ`, proving AT. ∎

Consequently NSections implies NInv, and NInv implies AT. For the first
implication, a right inverse to a numerical bijection is also a left inverse
by injectivity. The reverse implication AT⇒NInv is **not established here**:
canonical maps form a special class of numerical bijections.

## 4. Transport gives predecessor; Maximalism blocks canonical inverses

**Theorem 4.1.** C proves that `Iσ` and the one upward transport instance
`ATσ,σt` imply an admitted predecessor operation at counting type `σ`:

    ∃P : νσ → νσ, ∀n∈Nσ, P(Sσ n)=n.                  (PredOpσ)

**Proof.** Let `κ:=σt`, let `H(x):=λz^σ. z=x` be the haecceity injection
`σ → κ`, and put `d:=⊥κ`. C proves `□∀x, H(x)≠d` and necessary
injectivity of `H`. Define

    A_X := H_*X ∪ {d};       T(k) := λX^(σt). k(A_X).

The Frege Swap lemma gives the fixed-deletion identity

    Nκ k ∧ A(d) → [(Sκ k)(A) ↔ k(A−d)].              (FD)

For the forward direction, take the element `y` deleted by the successor
witness. If `y=d`, the conclusion is immediate. If `y≠d`, Swap exchanges
the deleted `y` with `d`. Conversely, delete `d` in the successor
definition. This argument is a C theorem with its hypotheses discharged.

For our `A_X`, `A_X(d)` holds necessarily. Also `A_X−d=H_*X` is an
intensional identity: the defining properties are necessarily universally
coextensive because `d` is necessarily outside the image of `H`. Numberhood
of `k` persists. Applying the necessitated FD theorem at all future
arguments `X` therefore gives, by Intensionality,

    Nκ k → T(Sκ k)=F_H(k).                            (†)

This step uses the necessary version of the finite-cardinality argument,
not an illicit replacement of merely currently coextensive properties.

Upward noncollapse gives `Iκ` from `Iσ`. Choose canonical
`U : νσ → νκ` by the specified transport instance, and set `P:=T∘U`.
For `n∈Nσ`, canonicality, (†), and numerical induction on the canonical
endomorphism `F_H∘U` give

    P(Sσ n)=T(Sκ(U(n)))=F_H(U(n))=n.

There is no requirement on `P(0σ)` or on nonnumerical inputs. ∎

**Corollary 4.2.** For every fixed closed counting type `σ`, Pure
Maximalism refutes upward canonical transport `νσ → ν(σt)` and refutes
the existence of a numerical inverse for the C-definable canonical map
`F_H : ν(σt) → νσ`.

Pure Maximalism proves `Iσ` at every fixed counting type, but refutes
PredOpσ by the existing finite-overflow argument. To recall its exact
scope, in a full one-world singleton-individual model the carrier of `σ`
has some positive external finite size `m`. The pure sentence

    (m+1)σ=(m+2)σ ∧ mσ≠(m+1)σ

is true there. Maximalism makes it possible. A current predecessor would
give `P((m+1)σ)=mσ` and `P((m+2)σ)=(m+1)σ`; NI makes these equations
necessary, contradicting that possibility. Theorem 4.1 now forbids the
upward transport. Since `F_H` is a canonical numerical bijection under
Maximalism, its numerical inverse would itself be canonical and would
give precisely the forbidden transport. ∎

Thus every counting type supplies an explicit numerical bijection which
Maximalism cannot invert. The canonical graph and predecessor graph still
exist. This is an operation-realization obstruction, not a proof that
Maximalism is inconsistent, nor a denial of its ordinary arithmetic laws.

## 5. A two-point decoding principle is exactly ND

Fix any counting type `σ`; set `α:=νσ` and `β:=αt=ν(σt)`.
The two objects `0σ` and `1σ:=Sσ(0σ)` are necessarily distinct in C,
independently of Iσ.

Define **TwoDecσ**: whenever an admitted `f : α → β` is injective on
the current field `Nσ`, there is an admitted `g : β → α` satisfying

    g(f(0σ))=0σ;       g(f(1σ))=1σ.

**Theorem 5.1.** Over C, TwoDecσ is equivalent to all-type ND, for every
fixed counting type `σ`.

**Proof, ND⇒TwoDecσ.** Injectivity gives `f(0σ)≠f(1σ)`, and ND makes
this necessary. The admitted finite interpolant

    g(y)(X) := (y=f(0σ) ∧ 0σ(X)) ∨
                (y≠f(0σ) ∧ 1σ(X))

is necessarily coextensive with `0σ` at the first input and with `1σ`
at the second. Intensionality gives both required identities.

**Proof, TwoDecσ⇒ND.** For an arbitrary currently true proposition `p`,
define `j_p : α → β` by

    j_p(n)(r) := p ∧ r=n.

It is currently injective even on the whole carrier `α`: equality of
two outputs and evaluation at the first input, using current `p`, force
equality of the inputs. TwoDecσ supplies its two decoder identities.
Their necessity, together with necessary `0σ≠1σ`, gives

    □(j_p(0σ)≠j_p(1σ)).

C proves `j_p(0σ)=j_p(1σ) ↔ □¬p`. Right-to-left follows from necessary
universal coextension of two empty predicates. For left-to-right, NI
makes the equality persist; evaluating it at `0σ` at each future point
and using necessary `0σ≠1σ` forces `¬p` there. Thus the displayed
inequality is equivalent to `□◇p`. Discharging the arbitrary assumption
`p` proves modal axiom B, `p→□◇p`. The recorded C theorem B⇒ND
then gives all-type ND. ∎

For completeness, B⇒ND uses only NI and modal duality: `a≠b` gives
`□◇(a≠b)` by B; at any accessible point, equality of `a,b` would imply
its necessity by the necessitated NI theorem, contradicting that possible
inequality. Hence `□(a≠b)`.

**The field-membership distinction is essential.** The output type `β`
is itself the numerical carrier `ν(σt)`, but `j_p(n)` is not shown to
belong to `N(σt)`. Accordingly this result does not turn genuine
number-to-number NInv into ND. Requiring merely numerical *types* rather
than numerical *values* would erase the distinction.

## 6. Arbitrary numerical-image decoding is exactly ND under Iσ

For fixed `σ`, let **NDecodeσ** be the schema asserting, for each
relational `τ`, that every admitted `f : νσ → τ` injective on `Nσ`
has an admitted `g : τ → νσ` with `g(f(n))=n` for all `n∈Nσ`.
Let **ImageSectionsσ** assert, for every such `τ` and every admitted
`f`, that some admitted `g` takes a numerical preimage of each member
of the current image `f[Nσ]`. No values outside that image are prescribed.

**Theorem 6.1.** Over C+Iσ,

    ImageSectionsσ  ↔  NDecodeσ  ↔  ND.

ND gives ImageSectionsσ by Theorem 2.1 and Corollary 2.3. A section of
the image of an injection is a decoder, so ImageSectionsσ implies
NDecodeσ. NDecodeσ implies TwoDecσ, hence ND by Theorem 5.1.
These implications establish the cycle. ∎

The equivalence for unrestricted image decoding is stated with Iσ.
Only the two-point equivalence has been proved here without that premise;
the collapsed-field case of full decoding has not been resolved.

## 7. Consequences and scope

The numerical transport, inverse and section principles are equivalent by [the numerical-sections theorem](numerical-sections.md), with the guarded noncollapse premises stated there. The proofs below retain useful direct constructions under their explicit hypotheses. The [Henkin countermodel](predecessor-henkin-countermodel.md) preserves the distinction between current and necessary noncollapse.

The proved implication pattern, for the guarded all-type numerical schemata,
is

    ND ⇒ NSections ⇒ NInv ⇒ AT ⇔ CInv ⇔ inverse existence for every F_j.

The final equivalence restricts `j` to necessary injections and both
counting bases to noncollapsed fields. AT gives PredOpσ under Iσ,
already using just the upward pair `(σ,σt)`. NPC independently gives
NSections and NInv by Corollary 2.4.

The independently developed model checks in
[model-separations.md](numerical-models.md) sharpen this hierarchy:

* The finite-support monotone-map model has NPC, both quantified Infinity
  axioms at `e,t`, and all numerical noncollapse instances, while failing
  ND, Actuality, and Atomicity. Corollary 2.4 therefore gives nonvacuous
  NSections and NInv there. In particular NInv does not imply ND,
  Actuality, or Atomicity; nor does NSections. These are deductions from
  that model audit and the present theorem, not new model verification
  badges or independently certified Lean results.
* The full star model in that note has boxed Actuality, boxed Atomicity,
  and quantified Infinity at `e,t`, while failing AT_e,t. By Theorem 3.1,
  it fails the all-type NInv and NSections schemata. Thus even the boxed
  structural principles plus those two size axioms do not supply
  numerical inverse closure.

For unrestricted arbitrary-image decoding, dropping the Iσ premise remains a separate question. The two-point fragment requires no such premise; the sufficient construction here uses least-number reasoning under Iσ. The numerical equivalences themselves are settled by the linked section theorem.

The substantial new proof is the least-preimage realization in §2: bounded
Barcan controls future preimages below a current least witness, avoiding
full numerical collection. The other main innovations are the exact
canonical-inverse reformulation (§3), the modal fixed-deletion route from
transport to predecessor (§4), and the two-point collapse to ND (§5).
No new arithmetic operation closure beyond these claims is asserted.
