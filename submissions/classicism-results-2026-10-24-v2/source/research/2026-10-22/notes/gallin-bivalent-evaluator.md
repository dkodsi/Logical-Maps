# Gallin comprehension as a unique Boolean evaluator

Scratch research, 22 October 2026. Ordinary mathematics over the database's fixed logic C; no record edits, no Lean claim. Prepared by the choice lane. The existence, uniqueness, and unboxed quantifier-commutation arguments below were independently checked by the rigidity lane on 22 October. The parent requested special care about new objects at future points; the proofs explicitly allow them. Nothing below asserts a necessarily correct evaluator of actual truth.

## 1. Exact definitions and comparison with the existing record

For an operation E:t→t write

    BE(E) := ∀p[(p→Ep=⊤) ∧ (¬p→Ep=⊥)],
    Range₂(E) := □∀p(Ep=⊤ ∨ Ep=⊥),
    GBE(E) := BE(E) ∧ Range₂(E).

Thus E correctly evaluates current truth, while at every accessible point its value on every proposition there is one of the two constant propositions. Its future evaluations need not be correct about future truth. Equivalently GBE(E) is

    [∀p(p↔Ep)] ∧ □∀p(Ep=⊤ ∨ Ep=⊥).

This equivalent version is the recommended compact definition.

The recorded Gallin Extensional Comprehension schema is, for every finite tuple of argument types,

    ∀X^(σ̄t) ∃Y^(σ̄t)
      [Persistent(Y) ∧ Persistent(¬Y) ∧ ∀z̄(X[z̄]↔Y[z̄])],
    Persistent(Y) := □∀z̄(Y[z̄]→□Y[z̄]).

The existing principle record attributes that formulation to Bacon–Dorr, *Classicism*, draft of 16 May 2023, §2.3 n.37, p.28, comparing Gallin's convention. The proved records already establish GC ⇔ ND+Strong Actuality. The two relevant reverse proofs use only GC at type t→t applied to the identity predicate. Our contribution here is the single-operator presentation, its uniqueness, and its quantifier laws; no literature novelty claim is made.

Relevant records: `gallin-extensional-comprehension-r`, `gallin-comprehension-implies-nd`, `gallin-comprehension-implies-strong-actuality`, `nd-and-strong-actuality-imply-gallin-comprehension`. Ordinary BE alone is analyzed in the parent's `.reproduction/classicism-research/bivalent-evaluation-root.md`; it is equivalent to ND+Actuality, a strictly weaker condition than GC.

## 2. Existence equivalence

**Theorem 1.** Over C, Gallin Extensional Comprehension is equivalent to `∃E GBE(E)`. Its type-t→t instance applied only to the identity predicate suffices.

**Forward.** Apply that instance to X=λp.p. It gives E coextensive with truth, with E and ¬E persistent. At any accessible point and any proposition p at that point, classical case distinction says Ep or ¬Ep. In the first case persistence gives □Ep, equivalently Ep=⊤. In the second it gives □¬Ep, equivalently Ep=⊥. This proves Range₂(E), and its root instance plus coextension gives BE(E).

**Reverse.** For any current X define Y(z̄)=E(X[z̄]). Coextension follows from BE(E). At every accessible point, including on argument tuples first appearing there, Range₂(E) says Y(z̄) is literally ⊤ or ⊥. Necessity of identity makes its corresponding truth or falsity persist. Hence both Y and ¬Y are persistent. This is GC. No Barcan principle is needed: the necessary range formula already quantifies over every future input.

## 3. A modal lemma and uniqueness

Recall that BE yields B at the current point: `p→□◇p` for every p. Here is the direct argument. If p is true, BE gives Ep=⊤ and E⊥=⊥. NI preserves both identities necessarily. Therefore p cannot become identical to ⊥ at any future point, since substitution would equate ⊤ and ⊥ there. Thus □(p≠⊥), i.e. □◇p. This is the usual C equivalence B⇔ND, but only the displayed B instances are needed below.

**Lemma 2 (persistent falsity).** If q is true and `□(¬q→□¬q)`, B(q) entails □q. Indeed B(q) gives □◇q. At a future point, ¬q would yield □¬q and contradict ◇q.

**Theorem 3.** There is at most one E satisfying GBE(E), in the literal identity sense of C.

Let E,E′ be such witnesses and put q:=∀p(Ep=E′p). Ordinary BE makes q true now. If q fails at any future point, some proposition p there has different E,E′ values. Both values are endpoints, so one is literally ⊤ and the other ⊥. NI preserves those endpoint identities, and this same witness therefore keeps q false at every later point. Consequently `□(¬q→□¬q)`. Lemma 2 gives □q, and C's modalized Functionality/Intensionality gives E=E′.

The restriction to GBE witnesses is essential. Unique *ordinary* BE is substantially stronger: the parent's analysis identifies it with BE+BF_t, hence C5+Actuality. In contrast GC and unique GBE hold at the root of the full two-object retract model, which fails BF_t and C5.

## 4. Exact quantifier commutation without BF

**Theorem 4.** Suppose GBE(E). For every admitted input type σ and every current F:σ→t,

    E(∀x^σ Fx) = ∀x^σ E(Fx),
    E(∃x^σ Fx) = ∃x^σ E(Fx).

These are identities of propositions, with the ordinary outer quantifier `∀F`. No BF_σ, BF_t, or C5 is assumed.

**Universal case.** Put Q:=∀x E(Fx). At any accessible point where Q is false, choose a counterexample x at that point. Range₂(E) gives E(Fx)=⊥. NI preserves this identity at every subsequent point. The same x remains a legitimate instance for universal elimination, so Q stays false there. This proves `□(¬Q→□¬Q)` even when the counterexample first appeared at the future point.

If Q is true now, Lemma 2 gives □Q and hence Q=⊤. If Q is false now, the preceding witness argument gives □¬Q and hence Q=⊥. Thus Q is currently literally one endpoint. Ordinary BE, applied pointwise under ordinary quantification, gives `Q↔∀x Fx`. It follows that E(∀x Fx) is exactly the same endpoint as Q. This proves the identity.

**Existential case.** Put R:=∃x E(Fx). If R is true now, a witness has E(Fx)=⊤, so NI makes that witness remain true and R=⊤. If R is false now, every E(Fx)=⊥. For every current x, ordinary BE identifies E(¬Fx)=¬E(Fx), so ∀x E(¬Fx) is true now; the universal proof makes this latter proposition literally ⊤. To avoid using an unproved boxed Boolean law here, an alternative direct argument is as follows. R has persistent truth at every future point, by its witness and Range₂(E). Applying B to the currently true ¬R rules out any future R, since persistent R would contradict the future possibility of ¬R. Thus R=⊥. Ordinary BE gives `R↔∃x Fx`, and E(∃x Fx) is the same endpoint.

**Scope warning.** For each current F, NI makes the displayed equality persist. Accordingly this proof gives `∀F □[E(∀x Fx)=∀x E(Fx)]` as well. It does not move the outer ∀F under □. The stronger statement `□∀F[...]`, covering entirely new future functions in one necessary universal, is not established by this argument and is deliberately not claimed. No inference from pointwise identities to an operation identity with input type σt is being made without BF_(σt).

## 5. Necessary finitary Boolean structure

**Theorem 5.** Every GBE evaluator necessarily preserves the Boolean constants and all finitary Boolean operations. In particular,

    □(E⊤=⊤ ∧ E⊥=⊥),
    □∀p(E(¬p)=¬Ep),
    □∀p,q(E(p∧q)=Ep∧Eq),
    □∀p,q(E(p∨q)=Ep∨Eq).

At the root, BE makes each universal equation true. At a future counterexample all E-values are endpoints by Range₂(E), as are finite Boolean combinations of those endpoint values. An unequal pair of endpoints remains unequal by NI. Thus falsity of each universally quantified Boolean law is persistent, even when its offending inputs first appeared at the future point. Lemma 2 makes each law necessary. The constants already follow from BE and NI. The same reasoning handles every fixed finite Boolean term.

Hence GC gives a unique globally two-valued Boolean homomorphism which evaluates current truth and commutes pointwise with all current quantifiers. This conclusion is stronger and more precise than describing GC only as replacement of each relation by an extensionally equivalent persistent relation.

## 6. Separations and limits

The recorded full two-object double-retraction model has ND+Actuality but fails Strong Actuality and therefore GC; it separates ordinary BE from existence of GBE. The full two-object retract has GC but fails BF_t/C5; it separates unique GBE and the unboxed quantifier laws proved above from unique ordinary BE and from a Barcan assumption. Full Gallin/group examples can have contingent propositions while satisfying GC, so the result is noncollapsing.

Do not confuse Range₂(E) with `□BE(E)`. The latter says one fixed evaluator correctly tracks truth at every world and is equivalent to Extensionality; it is a collapse principle. Range₂ only fixes the *form* of every output and permits a future proposition's endpoint value to disagree with its future truth.

Open in this scratch argument: whether the necessary universal quantifier-commutation law of §4 follows from GC alone, and whether its schema has a useful exact strengthening characterization. No verdict is attached to that question here.

## 7. The canonical selected world and the exact stronger quantifier condition

**Proposition 6.** Given GBE(E), put

    w := ∀p(Ep↔p).

Then w is a true strong world, `□◇w`, and

    E = λp(w≤p).

The first claim is the recorded GC→Strong Actuality proof specialized to E. For completeness, w is true by BE. At any future point and any p there, Ep is an endpoint. If Ep=⊤, NI and the necessary universal instance from w give w≤p; if Ep=⊥ they give w≤¬p. Hence w is necessarily a world. Since w is currently true, B(w) gives □◇w.

At a future point, Ep=⊤ implies w≤p as just shown. Conversely if w≤p and Ep=⊥, then w≤¬p as well, forcing w=⊥, contrary to ◇w there. Thus, necessarily for every p, Ep=⊤ iff w≤p. Both sides of the desired equation Ep=(w≤p) are endpoint propositions: the left by Range₂, and the right because w is necessarily a possible strong world. Therefore they are identical. Modalized Functionality now gives the operation identity.

For any input type σ, the stronger necessary universal commutation law is consequently equivalent to the following **selected-world Barcan condition**:

    □∀F^(σt) [ (∀x^σ □(w→Fx)) → □(w→∀x^σ Fx) ].

The opposite implication between the two sides of the implication is always available by necessitated universal elimination. Thus the condition says exactly that the selected-world evaluator commutes with σ-quantification at every accessible point. In comparison, Theorem 4 proves its unboxed current instance for every σ. It would be incorrect to replace this relative condition by ordinary BF_σ: the full two-object retract satisfies all these selected-world conditions while failing BF_t.

**Full-action-model check.** Suppose a full action model has actual singleton world w={1_W} and every arrow h:W→V has a unique retraction j_h:V→W. At V the transported evaluator tests the value of a proposition along j_h. Indeed uniqueness gives `j_(gh) g=j_h` for every g:V→U, making that evaluation an endpoint proposition. The transported evaluator commutes with all quantifiers, because D_σ(j_h):D_σ(V)→D_σ(W) is surjective: D_σ(j_h)D_σ(h)=id. This argument works for every type and includes entirely new functions at V. Therefore full-action models with this root condition satisfy the stronger boxed commutation law. A countermodel to its derivability from GC, if one exists, cannot be obtained merely by choosing another full model with the same singleton-world/unique-retraction condition.

## 8. A canonical extensionalization, with no choice principle

For a relation type τ=σ̄t define

    TwoVal(Y) := □∀z̄(Y[z̄]=⊤ ∨ Y[z̄]=⊥).

This is equivalent over C to `Persistent(Y)∧Persistent(¬Y)`. Under GC let E be its unique evaluator and define

    Λ_τ(X)[z̄] := E(X[z̄]).

**Theorem 7.** Under GC:

1. Each X has exactly one Y such that TwoVal(Y) and Y is currently coextensive with X; that Y is Λ_τ(X).
2. `Λ_τ X=Λ_τ Y` iff X,Y are currently coextensive.
3. Λ_τ is idempotent as an operation, fixes precisely the TwoVal relations, and necessarily preserves every finite Boolean operation.
4. It commutes literally with every admitted pullback: for f:σ→ρ and P:ρ→t, `Λ_(σt)(P∘f)=Λ_(ρt)(P)∘f`. The analogous multiple-argument substitution identity follows directly.

For uniqueness in (1), two coextensive TwoVal relations make q:=∀z̄(Yz̄↔Zz̄) true now. A future disagreement is between fixed endpoints, so falsity of q persists. Lemma 2 yields □q, hence Y=Z. This proof covers future arguments absent now. Claim (2) follows from (1) and current coextension. Idempotence follows necessarily pointwise from E⊤=⊤, E⊥=⊥ and Range₂(E), and therefore is an operation identity without BF. The same equations show that every TwoVal relation is fixed; the image always has TwoVal. Theorem 5 gives the finite Boolean laws. Pullback commutation is the direct lambda identity `E(P(fx))=E(P(fx))`.

Thus Gallin comprehension may be presented as **unique extensionalization into relations with globally two-valued instances**, and its uniform idempotent operator is automatic. This is a simpler exact strengthening of bare Actuality's kernel canonicalization: bare Actuality gives a current-extension quotient, while GC identifies a canonical, globally persistent Boolean representative. It is not an application of Functional Choice or Plenitude.

The uniform operator is itself unique if its defining condition includes necessary TwoVal output for *all future inputs*: root coextension makes the universal comparison true, and global two-valued outputs make a future counterexample persist, so Lemma 2 again gives literal operator equality. Merely saying that every current output has TwoVal would leave a BF-related quantifier-scope gap in this uniqueness argument.

## 9. A sharp modal boundary

**Proposition 8.** Over C, existence of an ordinary BE evaluator satisfying even the unboxed pointwise law

    ∀p E(□p)=□(Ep)

is equivalent to Extensionality. The same holds with ◇ in place of □. Thus quantifier coherence in Theorem 4 does not license a modal-homomorphism claim.

Indeed BE makes every current Ep an endpoint, so □(Ep)=Ep. It also gives E(□p)↔□p and Ep↔p at the current point. The displayed equality therefore yields p↔□p for every p, hence every truth is necessary. Conversely under Extensionality the identity evaluator works. The diamond case uses ◇Ep=Ep and gives p↔◇p, which is equivalent to modal collapse by negation. Global bivalence is not needed for this obstruction.

## 10. A necessary quantifier law that is available

Although direct necessary universal commutation remains open here, the following stronger-scope **absorption** identities do follow without BF:

    □∀F^(σt) E(∀x E(Fx)) = E(∀x Fx),
    □∀F^(σt) E(∃x E(Fx)) = E(∃x Fx).

Consider the two displayed sides as predicates of F. Both are globally TwoVal by Range₂(E). At the root, ordinary correctness of E makes the inner quantified matrices coextensive, so the two predicates of F are currently coextensive. The uniqueness theorem for TwoVal coextensions therefore makes them identical operations. Modalized Functionality gives the displayed necessary universal identities, including inputs first appearing at a future point.

Equivalently let w:=∀p(Ep↔p), with E=λp(w≤p). Necessarily, wherever w is true, E(Fx) and Fx have the same truth value for every x available there. Thus w entails the equivalence of the two quantified matrices, and outer evaluation by w yields the same proposition. This proof does not need a shift of ∀F through □.

The distinction is exact: absorption seals the result with an outer E on both sides. Removing that outer E on the quantified normalized side is precisely the stronger selected-world Barcan issue in §7. These safe necessary identities are useful when constructing the extensional Henkin core in the independently audited `gallin-extensional-core.md`.
