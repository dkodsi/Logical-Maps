# A strict hierarchy of actual-truth evaluators

Consolidated ordinary mathematical note, 22 October 2026. Framework: the database's C, with relational function codomains. No language extension, record edit, or Lean claim. The principles below use only propositions and operations t→t, although their equivalents include all-type schemata. Their distinctions are substantial: every adjacent implication in the five-level hierarchy is strict.

For E:t→t put

    Eval(E) := ∀p[(p→Ep=⊤) ∧ (¬p→Ep=⊥)],
    Global₂(E) := □∀p(Ep=⊤ ∨ Ep=⊥).

All displayed equalities are literal identities, not merely current equivalences.

| Level | Simple operator principle | Exact strength over C |
|---|---|---|
| 1 | ∃f ∀p[p↔fp=f⊤] | Actuality |
| 2 | ∃E Eval(E) | ND + Actuality |
| 3 | ∃E[Eval(E)∧Global₂(E)] | Gallin Comprehension = ND + Strong Actuality |
| 4 | ∃!E Eval(E) | C5 + Actuality = BE + BF_t |
| 5 | ∃E □Eval(E) | Extensionality |

The implications run downward from stronger levels to weaker levels. At level 1 the operation may take arbitrary proposition values; only its top fiber encodes actual truth. Level 2 requires actual outputs to be the two constant propositions. Level 3 requires the outputs on *future* inputs also to be endpoints, while evaluation need only be correct now. Level 4 requires uniqueness among all ordinary actual evaluators. Level 5 requires a single evaluator to remain correct at every world.

## Proofs and exact scopes

**Level 1.** Given an actuality witness w, define f(p)=w∧p. If p is true, w≤p, so f(p)=w=f⊤; if p is false, w≤¬p, so f(p)=⊥≠w. Conversely suppose f has the displayed truth fiber and put

    v:=∀p(fp=f⊤→p).

Then v is true. For true q, fq=f⊤; NI preserves this identity, and the necessary universal instance from v gives □(v→q). Thus v entails every actual truth and witnesses Actuality. No endpoint restriction on f is needed. This is the single-fiber extraction of the structural report's kernel-canonicalization argument; see `quotient-abstraction-lane.md`, §§1–2, and `choice-uniformization.md`, §21.

**Level 2.** A bivalent evaluator makes every actual inequality necessary: if a≠b then E(a=b)=⊥, whereas E⊤=⊤; if a=b became true, NI would make (a=b)=⊤ there and substitution would contradict those endpoint equations. For Actuality use v=∀p(Ep→p). Conversely ND_t and an actual world w give the evaluator E(p):=(w≤p). For false p, w≤¬p and □◇w make w≤p necessarily false; for true p it is necessarily true. Hence BE is exactly ND+Actuality, equivalently the one-witness formula

    ∃w[w ∧ □◇w ∧ ∀p(p→w≤p)].

See `bivalent-evaluation-root.md`, Theorem 1.

**Level 3.** Apply Gallin Comprehension at tt to the identity predicate. It supplies E coextensive with truth, with E and ¬E persistent. Thus every future Ep is ⊤ or ⊥. Conversely such E sends every X to λz̄.E(Xz̄), a coextensive relation whose positive and negative instances persist. The existing database equivalence identifies this with ND+Strong Actuality.

There is automatically exactly one evaluator satisfying the *level-3* condition, without BF. If E,E′ both satisfy it, q:=∀p(Ep=E′p) is true now. A future disagreement is between fixed endpoints and persists forever; but BE gives B(q), i.e. □◇q, which rules out any such permanent disagreement. Hence □q and E=E′. This is uniqueness within the globally two-valued subclass, and must not be confused with level 4. See `gallin-bivalent-evaluator.md`, Theorems 1–3.

**Level 4.** BF_t identifies any two ordinary BE witnesses because their actual output identities are necessary by NI, and BF_t boxes the outer ∀p. Conversely, given ∀p□Xp, modify a BE witness by

    E′(p):=(Ep↔Xp).

On every current p, Xp=⊤, so E′p=Ep and E′ is also a BE witness. Uniqueness forces the operation identity E′=E. Its necessary pointwise content is `(Ep↔Xp)↔Ep`, which entails Xp. Thus □∀pXp, proving BF_t. BE supplies ND_t; ND_t+BF_t gives C5. This proves the listed equivalences. See `bivalent-evaluation-root.md`, Theorem 3, independently checked in `rigidity-actualization.md`, §1.

Level 4 entails level 3: current endpoint equations are individually necessary, and BF_t boxes their universal quantifier. This also shows exactly why level-3 uniqueness is too weak to yield BF_t.

**Level 5.** If one E necessarily satisfies Eval, then for every true p the current identity Ep=⊤ remains necessary. At every future point the assumed correctness of E rules out ¬p, because that would require Ep=⊥. Hence p is necessary. All truths are therefore necessary, giving Extensionality by the recorded C equivalences. Conversely under Extensionality the identity operation is necessarily an evaluator. See `bivalent-evaluation-root.md`, Theorem 4.

## Strictness: four explicit countermodels

These selections were checked by the proved-only Engine on 22 October 2026, with all optional assumptions in each queried premise set.

| Weaker level holds, next stronger fails | Recorded construction | Reason |
|---|---|---|
| 1 but not 2 | `full-two-object-chain` | Actuality holds; ND fails. |
| 2 but not 3 | `full-two-object-double-retraction` | ND+Actuality hold; two distinguishable returns refute Strong Actuality. |
| 3 but not 4 | `full-two-object-retract` | Gallin Comprehension holds; BF_t fails. |
| 4 but not 5 | `full-involution-group` | C5+Actuality hold in the full two-world group model; contingent propositions refute Extensionality. |

The model descriptions and original source caveats remain in their records under `topics/classicism/models/`. The strictness claims are relative consistency/model-separation statements. They do not assert that any one principle is absolutely true or false.

## The extra modal-scope distinction: necessary local evaluation

Between levels 4 and 5 lies the especially useful principle

    □∃E Eval(E)  ⇔  □Plenitude.

It says each world has an evaluator, allowed to differ from world to world. It is also equivalent to □∃!E Eval(E), and to C5+□Actuality. The latter equivalences follow from the previous proofs and the recorded completeness chain. Thus the hierarchy can be refined to six strictly separated positions by inserting necessary local evaluation between levels 4 and 5.

**Crucial correction:** level 4 is C5+Actuality, not □Plenitude. The full Boolean-valued model `full-boolean-valued-atom-and-atomless`, with Boolean algebra `2×RO(R)` evaluated at its isolated atom, has C5+Actuality and a unique ordinary BE witness, but fails □Actuality and □Plenitude. The full involution group then separates □Plenitude from Extensionality. Both separators were checked by the proved-only Engine.

This is the same quantifier-order distinction between `□∃E Eval(E)` and `∃E□Eval(E)` that appears in choice operators. The former gives a noncollapsing, finite propositional presentation of boxed Plenitude; the latter collapses contingency. Functional Choice adds the independently analyzed choice component: `FC⇔Actuality+RInv` and `□FC⇔□Actuality+SRInv`, as proved in `functional-choice-by-sections.md`.

## Why the level-3 evaluator is useful

Its unique evaluator necessarily preserves finite Boolean operations and, for every *current* predicate F of every input type, satisfies the literal identities

    E(∀x Fx)=∀x E(Fx),     E(∃x Fx)=∃x E(Fx).

No BF is needed: a false universal of endpoint values has a counterexample whose falsity persists; B prevents a currently true such universal from later acquiring that counterexample. The corresponding existential argument is dual. The outer ∀F must not silently be moved under □. That stronger necessary universal law is selected-world relative Barcan and remains unresolved in the scratch research.

The same evaluator gives each relation its unique coextensive representative with globally endpoint instances. These operators are idempotent Boolean retractions and commute literally with pullback. In contrast, asking even the pointwise modal law `E(□p)=□Ep` forces level 5, Extensionality. Details and independent audit: `gallin-bivalent-evaluator.md`, §§4–9.
