# Independent audit: Functional Choice = Actuality + right inverses

OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematics; no claim of human checking, Lean verification, or literature novelty. Main database unchanged.

## 1. Verdict

**PASS.** Theorem 22 and both difficult lemmas in `choice-uniformization.md` §15 are sound in the fixed C and relational type system. They do not secretly assume Plenitude, BF, ND before it has been derived, or identity of merely coextensive predicates. The resulting theorem is

    Functional Choice ⇔ Actuality ∧ RInv,

where RInv means ordinary pointwise right inverses for all actually surjective operations between relational types. Theorem 22 covers individual inputs to Functional Choice even though all RInv instances have relational source and target.

The main proof needs only these right-inverse instances: the fixed instance (tt)→t, and, for each desired choice instance σ→τ with τ≠e, the instance D→A where A=στt and D=tA.

The strong/boxed corollary also passes with the distinction between ordinary and strong inverse equations retained. The shorter condition □Actuality+RInv does not suffice for □FC; the recorded full two-object retract verifies that separator.

## 2. Framework and records checked

I used the previously read topic guide, topic definition and background, and read the exact Functional Choice, Relational Choice, Plenitude and Actuality records. The local comparison is ordinary finite-term mathematics over C. No operation has output type e.

For a relational type ρ, write a·X for pointwise conjunction of the proposition a with X. An equation in what follows is an identity of entities, not merely an assertion of actual coextension. □p is p=⊤, and ◇p is p≠⊥.

The required recorded directions FC→Plenitude→Actuality and C5+□Actuality→□Plenitude were checked by a proved-only `load_topic`/`Engine` query with empty engine background. The source for FC/Plenitude is Bacon–Dorr, *Classicism*, 16 May 2023 draft, §2.3, pp.31–33, with Actuality in Proposition 2.15, pp.32–33. The new decomposition itself belongs to the present research argument, not to that source.

I independently checked the BE characterization used in §15 against `bivalent-evaluation-root.md`, Theorem 1. Here

    Eval(E) := ∀p [(p→Ep=⊤) ∧ (¬p→Ep=⊥)],
    BE := ∃E Eval(E).

The identity-valued clauses are essential. Merely Ep↔p would not supply the Boolean coefficients used below.

## 3. Lemma 22.1: the proposed map really is surjective

Choose an Actuality witness w: w is true and w≤p for every actual truth p. Assume for contradiction

    ◇R,  where R:=¬◇w.

For H of type tt put

    T(H):=(w∧◇(R∧H⊤))∨(¬w∧H⊥).

This has type (tt)→t. Fix an arbitrary actual proposition q. Define two-slot operations by

    H_(b,q)(r):=((r=⊤)∧b)∨((r≠⊤)∧q).

C proves H_(b,q)⊤=b and H_(b,q)⊥=q as identities: the needed masks at ⊤,⊥ are the necessarily fixed Boolean values. No ND assumption is required.

If q is true, use b=⊤. Actuality gives w≤q and w≤◇R. Hence w∧q=w and w∧◇R=w, and Boolean algebra gives T(H_(⊤,q))=q. If q is false, use b=⊥. Actuality gives w≤¬q, so w∧q=⊥ and T(H_(⊥,q))=¬w∧q=q.

These are identities justified by algebraic entailment, not merely truth equivalences. The two cases prove ∀q∃H(T(H)=q). They do not construct a single q↦H operation and do not assume one exists. This distinction blocks a possible circularity objection.

## 4. Lemma 22.1: the no-section contradiction is modal-safe

RInv supplies g:t→tt with T(gq)=q for every actual q. Only its two actual instances q=w and q=⊥ are needed.

Because w is true, T(gw)=w yields

    ◇(R∧(gw)⊤).

Likewise T(g⊥)=⊥, evaluated where w is true, yields

    ¬◇(R∧(g⊥)⊤).

But R is ¬(w≠⊥), so the implication R→w=⊥ is a theorem of C. Applying Leibniz under this identity gives, as another theorem with the parameters w,g,

    □[R→((gw)⊤↔(g⊥)⊤)].

Thus R∧(gw)⊤ and R∧(g⊥)⊤ are necessarily equivalent, and their possibilities agree. This contradicts the displayed pair.

The argument therefore proves □◇w. It has not necessitated the optional Actuality premise, the assumed possibility ◇R, or the entire pointwise inverse equation. The only necessary conditional used in the contradiction is a C theorem, valid for its free parameters.

## 5. Persistent Actuality yields BE without another assumption

For completeness, define E(p):=(w≤p). If p is actually true, Actuality gives w≤p. This order condition is itself an identity, so NI makes it necessary; hence E(p)=⊤.

If p is actually false, Actuality gives w≤¬p, again necessarily. At any accessible point, w≤p would then force w=⊥. The established □◇w excludes that. Thus □¬(w≤p), equivalently E(p)=⊥. Consequently Eval(E).

This also derives ND at every admitted type. If a≠b, Eval gives E(a=b)=⊥ and E⊤=⊤, with both equations necessary by NI. If a=b held at an accessible point, the identity proposition a=b would be ⊤ there by NI, so substitutivity would equate those two E-values, contradicting ⊥≠⊤. This supplies ND after, rather than before, the critical right-inverse argument.

## 6. Lemma 22.2: fully expanded selector construction

Let U^(στt) be actually serial, with τ relational. Fix x₀ and y₀ with Ux₀y₀ using ordinary existential instantiation. Let w be an Actuality witness and E satisfy Eval. Both exist under BE by its independently checked characterization; alternatively retain the witness w constructed in Lemma 22.1.

Set A=στt, D=tA, and

    H_(x,y)(u,v):=(u=x∧v=y),
    Valid(k):=∃x,y(Uxy∧k=H_(x,y)),
    D_x(u,v):=w∧u=x,
    RangeD(b):=∃x(b=D_x),
    V(k)(u,v):=w∧∃x,y(Uxy∧k=H_(x,y)∧u=x).

All displayed types are admitted even when σ=e. Pair-haecceity injectivity is a theorem: equality of H_(x,y) and H_(x′,y′), evaluated at x,y, gives x=x′ and y=y′; the converse is Leibniz substitution. This theorem may be used necessarily and under the relevant quantifiers.

Consequently C identifies V(H_(x,y)) with the relation (u,v)↦w∧Uxy∧u=x. If Uxy is actually true, w≤Uxy and this entity is exactly D_x. The reduction is an identity. It follows from theorem-level haecceity manipulations followed by substitution of the identity w∧Uxy=w; it does not apply Logical Equivalence to an equivalence proved under the optional Uxy assumption.

The D_x are injective in x: evaluate D_x=D_x′ at u=x and any v, using actual truth of w. None is bottom. Similarly every pair code H_(x,y) is nonbottom. Thus ⊥_A is not Valid.

For H∈D abbreviate k=H⊤, b=H⊥, α=E(Valid(k)), β=E(RangeD(b)). The proposed operation π:D→A is explicitly the admitted Boolean lambda term

    π(H):= α·V(k) ∨ ¬α·[(¬β·b)∨(β·D_(x₀))].

By Eval, α and β are literally ⊤ or ⊥ according to the actual predicates. Therefore π has the three actual identity clauses stated in the research note. No Plenitude or function-valued if-then-else is hidden in this notation.

If b=D_x for some x, seriality provides y with Uxy; a two-slot H with H⊤=H_(x,y) has π(H)=D_x=b. If b is outside RangeD, take H⊤=⊥_A and H⊥=b. The first slot is invalid, the second lies outside RangeD, and π(H)=b. The necessary two-slot operation with values k,b∈A is explicitly

    H(r)[u,v]:=((r=⊤)∧k[u,v])∨((r≠⊤)∧b[u,v]).

Again this only proves pointwise existential surjectivity. RInv, at the relational types D,A, now supplies s:A→D with π(sb)=b.

For x≠x₀, put k_x=(s(D_x))⊤ and b_x=(s(D_x))⊥. If k_x were invalid and b_x outside RangeD, then π(s(D_x))=b_x=D_x would contradict being outside RangeD. If k_x were invalid and b_x in RangeD, then π(s(D_x))=D_(x₀)=D_x would contradict x≠x₀. Hence k_x=H_(a,y) with Uay. The valid clause gives D_a=D_x, so a=x. Thus

    k_x=H_(x,y) and Uxy

for some actual y. No uniform choice of this y has yet been assumed.

Write τ=ρ₁…ρ_nt, allowing n=0, and define

    d(x)[z̄]:=∃y(k_x(x,y)∧y[z̄]).

Whenever k_x=H_(x,y₁), C identifies d(x) with y₁: substitute the identity and use the theorem-level reduction ∃y(y=y₁∧y[z̄])↔y₁[z̄], followed by the admitted lambda/eta principles. This works also at τ=t, where z̄ is empty. It needs neither BF nor actual extensionality.

Finally let γ_x=E(x=x₀) and define

    h(x):=γ_x·y₀ ∨ ¬γ_x·d(x).

Eval makes h(x₀)=y₀ and, for x≠x₀, h(x)=d(x). The established identities give U(x,h(x)) for every actual x. This proves the full allowed Functional Choice instance.

## 7. Finite adversarial stress test for Lemma 22.1

The smallest full two-object chain gives a concrete check that the argument detects the expected obstruction. Take one individual at each point. At the root, a proposition is (x,y)∈2², where x is actual truth and y is its terminal truth. Choose w=(1,0). Then ◇w=(1,0), R=(0,1), and ◇R=⊤.

A root entity H of type tt is described by an arbitrary root truth table H₀:2²→2 and a terminal map H₁:2→2. Its value on p=(x,y) is (H₀(p),H₁(y)). There are 16·4=64 such H. The proposed T becomes

    T(H₀,H₁)=(H₁(1),H₁(0)).

It is plainly onto the four propositions. If it had a coherent section s, the terminal component of s(x,y) would depend only on y. But the section equation forces that component H₁ to have H₁(1)=x and H₁(0)=y; varying x while fixing y is impossible. Thus this very T has no section.

This is the same obstruction proved abstractly, not a separate assumption on all C-models. It also confirms that merely having a finite surjection does not license an operation-valued section in this semantics.

## 8. Boxed corollary and exact scope

SRInv means a right inverse satisfying □∀b f(gb)=b, equivalently the appropriate composite identity by Modalized Functionality. It is stronger than an ordinary right inverse.

□FC gives □Actuality and C5; it gives ordinary sections and BF boxes their pointwise inverse equations, yielding SRInv.

Conversely □Actuality+SRInv gives Actuality+RInv, hence FC by the audited theorem and therefore ND. A strong section makes its surjection necessarily surjective. The tt-endomorphism mask argument from Theorem 17 then yields BF_t; together with ND_t this gives C5. Proved records give C5+□Actuality→□Plenitude. Over that package, the audited FC follows from RInv and every closed pure FC instance is necessary by recorded No Pure Contingency. Hence □FC.

This establishes the exact corollary □FC⇔□Actuality+SRInv. Necessitating the finite proofs behind Theorem 22 gives the fully boxed pointwise formulation □FC⇔□(Actuality∧RInv), understood schema by schema.

The engine confirms that `full-two-object-retract` satisfies □Actuality and FC, while refuting □FC and C5. Since FC gives RInv, this verifies the claimed strict failure of the shorter unboxed-section premise □Actuality+RInv.

## 9. Sharper consequences

1. **One small right-inverse fragment suffices for the modal obstruction.** Actuality plus RInv only for operations tt→t gives BE and hence all-type ND. Therefore this fragment alone is inconsistent with Max_C+Actuality, by the recorded Max_C/ND incompatibility. No full RInv schema is needed for that negative result.
2. **Explicit surjection witnessing a failure.** In any model with Actuality but without BE, any chosen Actuality witness w must fail □◇w. The formula T in §3 is then an actual surjection tt→t with no right inverse. Thus the proof produces a witness, rather than merely deriving an abstract incompatibility.
3. **Application to the recorded coalesced maximalist root.** The engine confirms Max_C and Actuality there. It follows that this specific low-type RInv instance fails at its root. This conclusion is a new application of the audited proof; it should not be attributed to the historical source or inserted into the database without its own argument provenance.
4. **No redundancy claim for Actuality alone.** The audit does not show RInv⇒Actuality, nor establish the consistency or inconsistency of bare Max_C+RInv. The sharpened theorem removes LInv from the earlier decomposition; it does not remove the Actuality conjunct.

Validation: main records unchanged. The required validator is run after saving this report; the result is sent in the accompanying audit update.
