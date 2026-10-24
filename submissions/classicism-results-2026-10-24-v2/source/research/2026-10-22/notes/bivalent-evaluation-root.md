# Bivalent evaluation: a finite propositional presentation of boxed Plenitude

Original mathematical arguments developed by OpenAI Codex, 22 October 2026.
These are research notes, not a claim of literature priority or formal verification.
The fixed framework is C, with the relational type system and theoremhood
restrictions in `topics/classicism/background.md`. No optional assumption is
silently necessitated. A necessary consequence is obtained by necessitating the
corresponding C-theorem with its premises discharged, then applying K to boxed
premises.

## Definitions

For an operation E of type t→t, define

    Eval(E) := ∀p [(p → Ep = ⊤) ∧ (¬p → Ep = ⊥)].

**Bivalent Evaluation (BE)** is ∃E Eval(E).
**Unique Bivalent Evaluation (UBE)** is ∃!E Eval(E).
**Persistent Actuality (PA)** is

    ∃w [w ∧ □◇w ∧ ∀p (p → w ≤ p)].

Eval says that E records the actual truth value of each proposition as one of
the two rigid Boolean values. It does not identify the proposition with that
truth value. In particular BE is compatible with contingency.

Alternative concise equivalent notation:

    Eval(E) ↔ ∀p [Ep ∈ {⊥,⊤} ∧ (Ep ↔ p)].

Here membership in the displayed two-element set means the identity disjunction
Ep=⊥ ∨ Ep=⊤. Merely requiring Ep↔p would be trivial, witnessed by the identity
operation; the identity-valued bivalence clause is essential.

## Theorem 1: BE is exactly ND plus Actuality

The following are equivalent over C:

1. BE.
2. ND at all types and Actuality.
3. ND at type t and Actuality.
4. Persistent Actuality.

### BE implies ND at every type

Fix E satisfying Eval and arbitrary a,b of any admitted type. Suppose a≠b.
Then E(a=b)=⊥, whereas E⊤=⊤. NI makes both equations necessary. At any accessible
point where a=b, NI and the definition □q := q=⊤ give (a=b)=⊤. Substitution then
makes E(a=b)=E⊤, contradicting the necessary distinctness of ⊥ and ⊤. Thus
□(a≠b). No BF, choice or type restriction is used: the identity proposition
(a=b) has type t even when a,b have type e.

### BE implies Actuality

Put w := ∀p (Ep→p). Eval makes w true at the evaluation point. If q is true,
Eq=⊤, hence □Eq. Universal instantiation is a C-theorem, so necessarily
w→(Eq→q). Consequently w≤q. Thus w entails every actual truth.

### ND_t plus Actuality implies BE

Choose a true actuality witness w and define E := λp.(w≤p).
If p is true, w≤p. Entailment is a necessary condition by 4, so Ep=⊤.
If p is false, w≤¬p. Since w is true it is nonbottom; ND_t gives □(w≠⊥),
equivalently □◇w. At every accessible point w≤¬p still holds. If w≤p also held
there, Boolean algebra would give w=⊥, a contradiction. Thus □¬(w≤p), so Ep=⊥.
These equations establish Eval(E). This direction uses only ND at t.

### Persistent Actuality

ND_t plus Actuality immediately gives PA. Conversely, if w witnesses PA,
the same construction E(p):=(w≤p) proves BE: the preceding proof uses ND only
through □◇w. Hence PA implies ND at every type and Actuality.

The case for PA→ND can also be seen directly. Every actual inequality a≠b is
entailed by w. If a=b at a future point, NI makes that identity necessary there,
but □◇w guarantees a further point with w and hence with a≠b.

## Theorem 2: one boxed finite sentence is equivalent to the whole □Plenitude schema

Over C,

    □BE  ↔  □PA  ↔  □Plenitude.

From □BE, Theorem 1 gives □ND at every type and □Actuality. The recorded theorem
`c5-and-necessary-actuality-imply-atomicity` gives Atomicity, and
`c5-and-atomicity-imply-necessary-plenitude` gives □Plenitude.
Conversely □Plenitude gives □ND and □Actuality by the recorded results
`necessary-plenitude-r-implies-necessary-distinctness-necessary-r` and
`necessary-plenitude-r-implies-necessary-actuality`. Necessitating the implication
ND_t∧Actuality→BE proved in C gives □BE. The PA equivalence is the boxed version
of Theorem 1.

Thus a natural finite formula involving only propositions and operations on
propositions presents an all-type schema. This is an equivalence in the fixed
framework, not a change to the reference logic.

## Theorem 3: uniqueness isolates the missing domain condition

Over C,

    UBE  ↔  BE ∧ BF_t  ↔  C5 ∧ Actuality  ↔  Plenitude ∧ BF_t.

The first equivalence is proved independently in the companion
`rigidity-actualization.md`, §1. Its reverse implication uses no existence
principle beyond BE: if ∀p□Xp, modify E by E'(p):=(Ep↔Xp). Every actual input
has E'p=Ep, so E' also satisfies Eval. Uniqueness gives E'=E; consequently,
necessarily and for every p, (Ep↔Xp)↔Ep, which classically entails Xp. This is BF_t.

BF_t and BE supply ND_t; `nd-t-and-bf-t-imply-necessary-nd-t` then yields □ND_t,
and `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r`
yields C5. Conversely C5 gives BF at all types, and Actuality gives BE by
Theorem 1. C5+Actuality gives Plenitude by the recorded completeness chain.
Plenitude gives ND and Actuality; with BF_t these give UBE.

In particular □UBE and □BE are equivalent, hence both equivalent to □Plenitude.
The pointwise quantifier order remains material: BE can hold without UBE, and
UBE can hold without □BE. Proposed model witnesses need the ordinary
proved-record Engine verification before being reported as established here.

## Theorem 4: a single evaluator that remains an evaluator collapses contingency

Over C,

    ∃E □Eval(E)  ↔  Extensionality.

Suppose E necessarily evaluates actual truth. For an arbitrary true p,
Eval(E) gives Ep=⊤ and NI gives □(Ep=⊤). At every accessible point, Eval(E)
also gives ¬p→Ep=⊥. Hence □p. Thus every truth is necessary, which gives
the Fregean Axiom, and in C the Fregean Axiom is equivalent to Extensionality.
Conversely under Extensionality, the identity operation λp.p is necessarily
a bivalent evaluator, because propositions are necessarily ⊥ or ⊤ and all
truths are necessary. The corresponding derived equivalences must be checked
against the recorded Fregean/Extensionality results rather than assumed from
ordinary higher-order logic.

This distinguishes □∃E Eval(E), the positive benchmark, from ∃E□Eval(E), a
collapse. Under □Plenitude the evaluator at each world is unique, but it need
not be the same evaluator at different worlds.

## Consequences and definition proposals

The companion rigidity report proves that under UBE, c_E(F):=λx̄.E(F[x̄]) is
the unique rigid relation coextensive with F. These canonical actualizations
preserve Boolean operations and quantifiers, and represent actual-extension
equivalence by identity in the rigid core. The higher-type extensional core
requires hereditary support; merely taking all rigid relations is insufficient.

For presentation, the finite formula □∃E Eval(E) is a promising equivalent
form of □Plenitude. The terminology should not conceal the quantifier order:
“a bivalent evaluator at every world” is accurate; “one evaluator for all
worlds” states Theorem 4's collapsing principle.

Source background: Bacon and Dorr, Classicism, draft of 16 May 2023, §§2.1–2.3,
pp. 20–34, as transcribed in the cited records. Direct source of the new
equivalences is this original research note, not that paper. No named human
checker or Lean verification is claimed.
