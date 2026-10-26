# Arithmetic transport: nonvacuous model separations

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi.

## 1. Exact target and imported positive theorem

Work over Classicism C in its original finitary pure language and fixed
admitted closed types. For counting types σ and ρ put

    νσ := (σt)t,
    ATσρ := (Iσ ∧ Iρ) → ∃f^(νσ νρ) ∀n (Nσ n → Jσρ(n,fn)).

Here `Nσ` is Fregean natural numberhood, `I*σ` says that zero is not a
successor and successor is injective on `Nσ`, and `Iσ := ◇I*σ`.
`Jσρ` is the least relation containing the zero pair and closed under
synchronized successor. These definitions and its functional-graph
theorem are in
[`relational-coding-recursion-20261022.md`, §§34–35](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-coding-recursion-20261022.md).
Write **AT** for the schema of all these fixed-type instances.

The reviewed ordinary proof in [`positive-transport.md`, §§2–4](numerical-transport.md)
establishes

    C ⊢ □Iσ → ∀n (Nσ n → Jσρ(n,Fσρ n)),
    Fσρ := λn X. ∃m (Jσρ(n,m) ∧ mX).

In particular, `ND_t → AT`: propositional ND gives modal axiom 5, hence
`Iσ → □Iσ`. The same theorem yields **NPC → AT**, because `Iσ` is a
closed pure sentence and No Pure Contingency gives `Iσ → □Iσ`.
Consequently an ND-without-AT countermodel is impossible; C5 is a stronger
sufficient premise than needed. Plenitude also gives AT by functionalizing
the current graph, completed by a default off the source numerical field.

The positive theorem uses internal induction, so it includes nonstandard
internal numbers. The external standardness argument below is used only
to check particular semantic examples and their nonvacuity.

**Infinity convention.** `Iσ` is numerical noncollapse. It is not defined
as the quantified Axiom of Infinity at σ. The latter says that no member
of `Nσ` holds of the universal σ-property. Both claims are verified
separately below. Finite schema instances of Infinity are not substituted
for the quantified axiom.

## 2. An extensional-fullness lemma for checking nonvacuity

Let an action model be extensionally full at an object V, and let
`kσ := Sσ^k 0σ` be its standard numerals. Then its current `Nσ`-extension
is precisely the external successor orbit `{kσ : k ∈ ℕ}`.

Indeed, extensional fullness supplies a property whose current extension
is that orbit. It contains zero and is successor-closed, so the defining
second-order induction clause for `Nσ` puts every `Nσ`-member in it.
Conversely each standard numeral satisfies every current inductive
property, by ordinary finite induction. This argument concerns current
extensions; it does not identify an arbitrary coextensive property with
a rigid one.

If the σ-domain is infinite, its standard numerals are pairwise distinct.
For `k ≠ l`, take a current property with exactly k instances, supplied by
extensional fullness. Unfolding the finite definitions shows that `kσ`
holds of it and `lσ` does not. Thus zero is not a successor and successor
is injective on the numerical orbit: `I*σ`, hence `Iσ`, holds. The same
finite calculation shows that no standard numeral holds of the universal
property, so **quantified Infinity at σ** holds as well.

All full action models are extensionally full. So are the ideally full,
finitely pinned action models used below: *Classicism*, Definitions
D.1–D.3 and the following remark, pp. 73–74; see also the explicit
`extensionally-full` condition in
[`finite-support-one-object.yaml`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/groups/finite-support-one-object.yaml).
This admits a property with any chosen current extension, not a
necessarily constant truth evaluator on arbitrary transported arguments.

If both e and t have infinite domains, every admitted closed relational
type has an infinite domain: constant relations inject the infinite
proposition domain into each such type. Thus the preceding lemma applies
to every counting type. In contrast, on a finite category with finite
individual domains, all recursively constructed full domains are finite.
At every object the numerical orbit is finite, and an injective successor
on it cannot omit zero from its range. Therefore `I*σ` fails everywhere,
and every `Iσ` fails. In that situation all AT implications are vacuous.

## 3. All AT without ND, Actuality, or Plenitude

Use the existing
[`finite-support-monotone-maps`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/finite-support-monotone-maps.yaml)
model: one object, individuals ℕ, arrows all monotone maps ℕ → ℕ, and the
ideally full domains of finitely pinned intensions. Its source is Bacon
and Dorr, *Classicism*, Proposition D.5(3), construction p. 77; the
one-object NPC argument is on p. 79.

1. **All AT holds.** The model has No Pure Contingency, since every closed
   pure term is fixed by every arrow in this one-object model. Section 1
   therefore gives every AT instance, with the explicit pure operation F.
2. **No vacuity.** The e-domain is ℕ. There are infinitely many distinct
   propositions, for example `p_n := {h : h(0)=n}`, each pinned by `{0}`.
   Section 2 gives `Iσ` for every counting type and quantified Infinity at
   both e and t. Those two quantified axioms are also already recorded in
   this model, with the original nonvacuity argument.
3. **Even propositional ND fails.** Let
   `p := {h : h(0)=h(1)}`. It is pinned by `{0,1}`, differs from top at the
   identity, and is carried to top by any constant arrow c, because every
   composite `h ∘ c` is constant. Thus distinct propositions can coincide.
   Individual ND also fails under a constant arrow.
4. **Actuality fails.** For finite S, the true proposition
   `q_S := {h : h|S = id|S}` is finitely pinned. An actuality witness would
   be a true proposition contained in all `q_S`, hence exactly `{id}`.
   But `{id}` is not finitely pinned: any finite S is fixed by a nonidentity
   monotone map that fixes a sufficiently long initial segment and shifts
   the tail. Therefore no witness exists.
5. **Plenitude fails**, since its recorded implication to Actuality is a
   theorem of C. C5 fails because ND already fails at the root.

This proves, with every numerical antecedent true,

    C + AT + Infinity_e + Infinity_t + ¬ND_t + ¬Actuality + ¬Plenitude.

Here `Infinity_e,t` are the quantified axioms. The record's interpretation
of extra signature constants is immaterial: NPC and all arithmetic terms
used here concern the pure language.

The existing
[`finite-support-permutations`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/finite-support-permutations.yaml)
model gives a stronger positive background: **C5 + AT + both quantified
Infinity axioms**, with Actuality and Plenitude still false. Its AT verdict
follows from either ND or NPC. This is the permutation construction in
*Classicism*, Proposition D.5(1), pp. 75–76.

## 4. AT with boxed Actuality, without C5 or Plenitude

The existing
[`finite-support-sections-and-projection`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/finite-support-sections-and-projection.yaml)
model has individuals ℕ at W0 and ℕ×2 at W1, all sections
`f_T(n)=(n,T(n))`, and the projection π, with `π f_T=id`.
Its full construction and previously established verdicts are in the
[write-up](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/writeups/finite-support-sections-and-projection.md).

Every arrow out of W0 is split, so its transport is injective at every
type. Hence local ND holds at W0, and Section 1 gives all AT there.
The model has boxed Actuality, but C5 and Plenitude fail; these are
recorded verdicts, not new assumptions. NPC also fails: the closed pure
sentence ND at e holds at W0 but fails at W1 under the collapsing π.

The transport conclusion is nonvacuous. The individual domain is infinite
at both objects. At W0 the propositions
`q_n := {f_T : T(n)=0}` are pairwise distinct and pinned by `{n}`.
Transport along any section is injective, so W1 also has infinitely many
propositions. Extensional fullness and Section 2 give `Iσ` at both objects
for every counting type, together with both quantified Infinity axioms.
Thus this example also has stable noncollapse; the direct theorem of
Section 1 supplies all transport instances at either object. Its failure
of C5 is the separate fact that π collapses individuals at W1.

The new deductions here are the AT and nonvacuity conclusions. The
underlying model was constructed on 27 September 2026 by Claude Opus 5.5
in a session with Cian Dorr; the source write-up reports informal review
by Cian Dorr and Christopher Sun of the original construction, not of
these new conclusions.

## 5. Actuality without nonvacuous arithmetic transport

### 5.1. A finite frame and an explicitly asymmetric pair

Take the category with two objects W0,W1 and one nonidentity arrow
`h:W0→W1`. Put `D_e(W0)=ℕ`, `D_e(W1)={*}`, and let h collapse all
individuals. Construct the **full** action model, admitting every
relational intension. This is an instance of the general full action
construction of *Classicism*, §3.5 and Appendix D, pp. 58–61, 73–74.

At W0 both e and the predicate type et have infinite domains. Section 2
gives `I_e ∧ I_et` and the quantified Infinity axioms at those types.
Fullness supplies the identity singleton at each object, so **boxed
Actuality holds**. Independently, **boxed Atomicity at every relational
type** holds. At an object V, a full relation domain is the powerset of
the appropriate arrow-and-argument coordinates; algebraic entailment is
inclusion of these intensions. Any nonempty intension contains a singleton
coordinate, which is admitted by fullness and whose only proper subset
is bottom. This proof works at every object. It is exactly the existing
[`full-atomicity`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/arguments/full-atomicity.yaml)
argument, sourced to *Classicism*, p. 61. Atomicity is not inferred merely
from the existence of an actuality witness.

At W1 the hierarchy is the ordinary full singleton one-world hierarchy.
Thus e has one member and et has two. Consequently

    2_e = 3_e,             but             2_et ≠ 3_et

at W1: the first two numerals are both the empty overflow cardinality;
`2_et` counts the universal et-property while `3_et` does not.

Suppose a root operation f realizes `J_(e,et)`. Its root numerical
identities include `f(2_e)=2_et` and `f(3_e)=3_et`, by the current
single-valuedness of J. Identity and application are preserved under
transport. At W1 the equal inputs therefore force the unequal outputs
equal, a contradiction. Hence **AT_(e,et) fails with a true antecedent**.

Conversely `AT_(et,e)` holds. The necessary haecceity injection
`H:e→et`, `H(x)=λz(z=x)`, gives the explicitly definable numerical
operation in §35 of the earlier research note,

    F_H(n)(X) := n(λY. ∃x (Xx ∧ Y=H(x))).

It preserves zero and successor and realizes `J_(et,e)` under the current
noncollapse hypotheses. Therefore this small model has a current
arithmetic bijection represented by an operation, while its inverse
arithmetic bijection cannot be represented by an operation. No Maximalism
or speculative consistency claim is involved. The direction e→t would
be vacuous here because the root proposition domain is finite; the stated
negative instance deliberately uses e→et.

### 5.2. Both quantified Infinity axioms and failure at e→t

For the stronger Infinity convention, use a countable star category:
one root W0, terminal objects W_k for `k∈ℕ`, and exactly one arrow
`h_k:W0→W_k` to each leaf. Put ℕ individuals at W0, one individual at
each W_k, and use the collapsing individual maps and full relational
domains.

The root has infinitely many individuals and infinitely many propositions:
its proposition domain is the power set of `{id} ∪ {h_k:k∈ℕ}`.
Section 2 gives both quantified Infinity axioms and `Iσ` at every closed
counting type. Fullness again gives boxed Actuality and, by the separate
singleton-coordinate argument above, boxed Atomicity at every relational
type.

At every leaf, e has one member and t has two. Thus
`2_e=3_e` but `2_t≠3_t`. The identical two-value argument proves
**¬AT_(e,t)** at the root. In particular

    C + □Actuality + □Atomicity_r + Infinity_e + Infinity_t
      + every current Iσ

does **not** entail AT. Combined with §3, this establishes independence
between AT and Actuality even over the two quantified Infinity axioms.
The monotone-map model is also propositionally atomless, as recorded in
Proposition D.5(3). Thus AT is independent of Atomicity at t and of its
all-relational-type schema over those same two Infinity axioms; the
negative-to-AT witness even has necessary all-type Atomicity.
Neither current Infinity nor current numerical noncollapse has silently
been treated as necessary. The collapse at the leaves is exactly why
the positive stable-source theorem does not apply.

## 6. Remaining requested model families and vacuity audit

| Construction, evaluated at its recorded root | AT | Why / nonvacuity |
|---|---|---|
| Finite-support monotone maps of ℕ | All instances hold | NPC; every Iσ true; quantified Infinity at e,t. |
| Finite-support permutations of ℕ | All instances hold | ND or NPC; every Iσ true; quantified Infinity at e,t. |
| Finite-support sections and projection | All instances hold | Root ND; every Iσ true; quantified Infinity at e,t. |
| Full idempotent monoid, recorded singleton individuals | All instances hold vacuously | All domains finite at the sole object, so every Iσ false. |
| Full two-object retract, recorded singleton individuals | All instances hold vacuously | Finite domains at both objects; root ND also supplies the positive theorem. |
| Full Boolean-valued atom plus atomless component | All instances hold | Plenitude or ND; e-based instances vacuous, t/tt comparison nonvacuous. |

The two full finite-category records admit the explicitly documented
**fixed-infinite-individual** setting in
[`full-action-models.yaml`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/groups/full-action-models.yaml).
These settings are constructions, not newly invented model record IDs.

* **Idempotent monoid `{1,k}`, `k²=k`, fixed ℕ individuals.** NPC still
  gives all AT. Both e and et are infinite, so the e/et instances are
  nonvacuous; t has four elements, so its noncollapse antecedent is false.
  Propositional ND fails because k sends `{1}` and `∅` to the same empty
  proposition. Actuality holds because the full domain contains `{1}`.
  Plenitude fails directly: an operation prescribed to send `{1}` to top
  and `∅` to bottom would carry the equalized inputs to still-distinct
  outputs under k. Extensional fullness supplies the total functional
  relation prescribing these current values, with bottom as default.
  This is a two-arrow nonvacuous AT-without-ND example.
* **Two-object retract, fixed infinitely many individuals.** Root arrows
  are split, so root ND and AT hold. The e/et pair is nonvacuous, whereas
  the finite proposition domains keep `I_t` false. This model's recorded
  root **satisfies Plenitude**; it is not a Plenitude counterexample.
* **Boolean atom plus atomless component.** The exact existing model has
  `D_e={*}` and `D_t=2×RO(ℝ)`, full admitted function spaces and crisp
  equality. It satisfies C5 and Plenitude, so AT follows. Its t-domain
  and tt-domain are infinite, and full crisp characteristic functions of
  the standard numeral orbits establish noncollapse there, so AT_(t,tt)
  and AT_(tt,t) are nonvacuous. Propositional Atomicity fails. This shows
  Atomicity is unnecessary for nonvacuous AT; it is not a separation from
  Actuality or Plenitude. The singleton e-base makes e/t instances vacuous.

Sources for the last three rows are respectively
[`full-idempotent-monoid.yaml`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/full-idempotent-monoid.yaml),
[`full-two-object-retract.yaml`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/full-two-object-retract.yaml),
and [`full-boolean-valued-atom-and-atomless.yaml`](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/full-boolean-valued-atom-and-atomless.yaml).
The Boolean construction is based on Bacon, *Could the truths of
mathematics have been different?*, 9 October 2025 draft, online appendix
§B.2, pp. 7–9 (PDF pp. 41–43), with the specialization and exact verdicts
proved in the linked model write-up. This note does not extend those
verdicts to an unspecified stronger Boolean-valued semantics.

## 7. A precise full-model obstruction criterion

There is a useful semantic explanation of the two-value obstruction.
Consider a full action model at W with `Iσ ∧ Iρ`. Its current numerical
fields are standard by §2. Then ATσρ holds **if and only if** at every
object V reachable from W and every pair of standard indices i,j,

    iσ^V = jσ^V  →  iρ^V = jρ^V.                  (collapse inclusion)

**Necessity.** J contains every synchronized standard pair, and its
current uniqueness forces any realizing operation to have the values
`f(kσ)=kρ`. Transport these identities to V. Equal source numerals must
have equal images.

**Sufficiency.** Fullness admits the relation intension R whose extension
at an arrow `h:W→V`, on arguments `n∈D_νσ(V)` and `X∈D_ρt(V)`, is

    R_h(n,X) iff ∃k∈ℕ (n=kσ^V and kρ^V(X) is true at V).

Read R as an operation `f:νσ→νρ`. For any fixed standard j and any
reachable V, the value of `f(jσ)` at X is the displayed union over all k
with `kσ^V=jσ^V`. Collapse inclusion makes every contributing `kρ^V`
equal to `jρ^V`, and k=j contributes. Hence `f(jσ)` and `jρ` have the
same whole intension, so they are identical. All current numbers are
standard; these values therefore realize J on the current numerical
field. QED.

This criterion uses the actual fullness of the action model. It is not
claimed for arbitrary Henkin models or arbitrary finitely pinned models:
their domains need not contain the countable union just constructed.
The general positive theorem in §1 needs neither such a union nor
external standardness. The criterion also shows why the finite-frame
example is directionally asymmetric: its source collapse relation can
be included in the target's in one direction and fail inclusion in the
other.

## 8. Exact numerical-stability characterization with extensional fullness

The all-type schema has a stronger characterization than the individual
full-model criterion in §7. Let an action model be **extensionally full
at every object**. This includes full models and the ideally full,
finitely pinned models above. At any evaluation object the following
six schemata are equivalent:

    (a) ATσρ for all counting types σ,ρ;
    (b) AT_(σ,σt) for every counting type σ;
    (c) Iσ → PredOpσ for every counting type σ;
    (d) Iσ → □Iσ for every counting type σ;
    (e) NSections for all pairs of counting types;
    (f) NInv for all pairs of counting types.

Here `PredOpσ` means an admitted P with `P(Sσ n)=n` for every current
σ-number. `NSections` and `NInv` have exactly the guarded meanings in
[`numerical-inverses.md`, §1](numerical-inverses.md): under `Iσ ∧ Iρ`,
every current numerical surjection has a numerical right inverse, and
every current numerical bijection has a numerical inverse, respectively.
No equations off the numerical fields are required. The guard in (c) is
essential: a vacuously true AT instance with false `Iσ` does not supply
a predecessor operation.

Thus the adjacent predicate-type transports already detect every failure
of local numerical stability in this semantic class. The assertion is
about the original arithmetic formulas in these models, not an
unrestricted theorem of C.

**Shortest proof.** The implication (a)→(b) is immediate. Theorem 4.1 of
`numerical-inverses.md` proves (b)→(c) already in C, by the haecceity
injection and Frege fixed-deletion lemma. For (c)→(d), let `Iσ` hold at W
and take its predecessor operation P. Every standard numeral kσ is
currently numerical, so

    P(Sσ kσ)=kσ

holds for every external k. Necessity of Identity preserves each such
equation at every future object V. Extensional fullness at V makes
every V-number a standard numeral by §2. Therefore the transported P
is a left inverse of successor on all V-numbers, making successor
injective there. Zero is not a successor by a theorem of C. Hence
`I*σ`, and so `Iσ`, holds at every V: `□Iσ` holds at W. This is a
semantic argument using standardness at each object, not an illicit
object-language passage from infinitely many boxed instances to a boxed
universal sentence.

Corollary 2.2 of `numerical-inverses.md` gives (d)→(e), by stable least
preimages. A right inverse to a numerical bijection is a left inverse
as well, so (e)→(f). Finally NInv gives inverses for the canonical maps
induced by necessary injections; Theorem 3.1 of that note gives (f)→(a).
This proves all six equivalences. The same theorem also makes canonical
numerical invertibility, CInv, equivalent to them.

In fact the predecessor argument proves the unguarded pointwise
characterization **`PredOpσ ↔ □Iσ`** in this semantic class. The reverse
direction holds in C: apply the least-preimage theorem (Theorem 2.1 of
`numerical-inverses.md`) to successor under `□Iσ`; numerical distinctions
of its values are stable, and its numerical injectivity makes the
resulting decoder a left inverse.

**Independent cardinality proof of (b)→(d).** This also checks that
future domain growth has not been mistaken for finite collapse.

**Numeral-collapse calculation.** At any object V and distinct standard
indices i,j, the σ-numerals iσ and jσ are equal exactly when

    every object U reachable from V has fewer than min(i,j) σ-entities.

For if U has at least `min(i,j)` entities, extensional fullness supplies
a property with exactly that many instances. The smaller numeral holds
of it and the larger does not, so their intensions differ at U. In the
other direction neither numeral holds of any property at any reachable
object: their entire intensions are empty and hence equal. The case
`min(i,j)=0` gives no equality, because the empty property always
distinguishes zero from a positive numeral.

By §2, every current numerical object is a standard numeral. It follows
that `I*σ`, and equivalently `Iσ`, holds at V exactly when the sizes of
the σ-domains at objects reachable from V have **no uniform finite
bound**. If there is no bound, the calculation makes all standard
numerals distinct and proves successor injectivity. If there is a bound,
the finite sizes have a largest attained value K. Then Kσ differs from
`(K+1)σ`, while their successors `(K+1)σ` and `(K+2)σ` are both empty,
so successor is not injective. The same bound applies at every future
object, so `◇I*σ` also fails. A finite current σ-domain alone would not
justify this conclusion: future growth can keep every numeral distinct.

Now assume (b), suppose `Iσ` holds at the evaluation object W, and
suppose it fails at some reachable V. The unboundedness characterization
at W implies `I_(σt)` there: at every object U, extensional fullness
gives at least as many σ-properties as σ-entities, and in the finite case
it gives all `2^|Dσ(U)|` different current extensions. Hence the σt-domain
sizes are also unbounded over W's future objects.

At V the σ-domain sizes have a largest attained finite value K; all types
are inhabited, so `K≥1`. Choose U reachable from V with exactly K
σ-entities. Its σt-domain has at least `2^K>K` entities. Therefore, at V,

    (K+1)σ = (K+2)σ,        but        (K+1)_(σt) ≠ (K+2)_(σt).

The second inequality is witnessed at U by a property of exactly K+1
σ-properties. Since both root noncollapse antecedents hold, (b) supplies
an operation realizing `J_(σ,σt)` at W. Its two standard numeral value
identities persist to V, contradicting the displayed collapse mismatch.
Thus `Iσ` cannot fail at a reachable object, proving (d). QED.

This theorem applies in particular to all action-model constructions
reviewed above. It does not automatically extend to the Boolean-valued
construction merely by calling its current projection extensionally
full: that would need a suitable all-world semantic argument. It also
does not infer quantified Infinity from `Iσ`: unbounded future finite
domains suffice for numerical noncollapse even when the current domain
is finite.

## 9. Exact consequences and remaining boundary

The new ordinary deductions establish the strict implications

    ND_t → AT,                 Plenitude → AT,                NPC → AT.

The reverse directions fail: §3 refutes AT→ND_t and AT→Plenitude;
the sections/projection model in §4 refutes AT→NPC. C5 is consequently
sufficient but unnecessary. AT is independent of Actuality and of
Atomicity, with the strong quantified-Infinity witnesses in §§3 and 5.2.
No candidate
ND-without-AT example remains open after the reviewed positive theorem.

The full-model collapse-inclusion criterion and the adjacent-type
stability characterization are semantic classifications for the stated
model classes, not object-language equivalences over C. Whether AT has
a particularly simple exact axiomatization over unrestricted C weaker
than ND or NPC is not settled here. Section 8 proves that AT supplies
inverses for all current numerical bijections in the stated semantic
class. Whether AT alone supplies them in arbitrary C-models, potentially
with nonstandard numerical fields, is not settled here.
