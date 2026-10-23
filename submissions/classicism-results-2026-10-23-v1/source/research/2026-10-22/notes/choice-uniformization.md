# Choice and uniformization: research notes, 22 October 2026

New arguments by Codex (OpenAI), not yet checked by a human. These notes do not edit the database. Framework throughout is the map's fixed Classicism C; all operations have relational output types. `B` abbreviates C + □Plenitude, equivalently the recorded C5 + Atomicity package. C proves NI, modalized Functionality/Intensionality, and the basic normal T4 modal laws. Existing records derive BF, □ND, □Rigid Comprehension, No Pure Contingency and Actuality from B.

## 1. A minimal uniform unique-witness principle collapses modality

Let NUW_t be the single sentence

    ∀F^(tt) [□∃!q^t Fq → ∃q^t □Fq].

**Theorem 1.** Over C, NUW_t is equivalent to Extensionality (the all-relational-type schema).

Proof. Fix arbitrary p and define

    F_p(q) := (p ∧ q=⊤) ∨ (¬p ∧ q=⊥).

C proves, without hypotheses, that F_p is uniquely instantiated; necessitating its universal closure and instantiating gives □∃!q F_p(q). (At every point exactly one of p and ¬p holds, and ⊤≠⊥ necessarily.) NUW_t gives q with □F_p(q). Suppose p. By T, F_p(q), hence q=⊤. NI gives □(q=⊤). The necessarily true implication F_p(q)∧q=⊤→p now gives □p. We have proved ∀p(p→□p), modal collapse. Given actually coextensive X,Y of any relational type, modal collapse boxes their universal coextension; Intensionality identifies them. Thus Extensionality follows.

Conversely Extensionality gives p→□p for every proposition p (the nullary instance identifies each true p with ⊤). If □∃!q Fq, T gives some q with Fq, and modal collapse gives □Fq. No choice axiom is used.

The same proof shows that replacing unique existence by existence gives an equivalent principle. The boxed NUW_t is equivalent too: its necessity implies NUW_t by T; Extensionality implies its own necessity and necessitation of the converse theorem then gives □NUW_t.

### Modal Plenitude

Define MP by the schema

    ∀U^(στt) [□Functional(U) → ∃f^(στ) □∀x Ux(fx)],  τ≠e.

**Theorem 2.** MP is equivalent to Extensionality over C. Only its σ=τ=t instance is needed for the forward direction.

For the forward direction use U_p(x,q):=F_p(q), ignoring x. It is necessarily functional. A uniform representing operation f gives □F_p(f⊤), so the argument above applies. For the reverse direction, Extensionality gives ordinary Plenitude (record `extensionality-r-implies-plenitude-r`), and modal collapse boxes the chosen representing equation. This does not assume necessitation from an optional premise.

The version with `□Serial(U)` instead of `□Functional(U)` is Modal Functional Choice. It implies MP and hence Extensionality; over Extensionality it is equivalent to ordinary Functional Choice/Relational Choice. Thus all-type Modal Functional Choice is equivalent over C to Extensionality + Relational Choice. MP itself needs no choice.

Even restricting the modal chooser to necessarily nonempty properties does not avoid collapse: the switching F_p is necessarily uniquely instantiated.

**Separation.** `full-involution-group` in the ordinary choice metatheory has four propositions, satisfies □Functional Choice and fails Extensionality, so □Functional Choice does not imply MP/NUW_t. This is a concrete noncollapsing witness, not merely missing closure arrows.

## 2. Stable unique outputs characterize BF

For an input type σ and relational output type τ=ρ̄t, define SUGR_(σ,τ) by

    ∀U^(στt) [
      (∀x^σ ∃y^τ □(Uxy ∧ ∀z^τ(Uxz→z=y)))
      → ∃f^(στ) □∀x^σ Ux(fx)
    ].

**Theorem 3.** BF at σ implies SUGR_(σ,τ) for every relational τ. Conversely SUGR_(σ,t) implies BF at σ. Hence the all-type stable unique graph representation schema is exactly BF over C.

Forward proof. Given U define, by lambda abstraction,

    f := λx^σ r̄^ρ̄ . ∃y^τ(Uxy ∧ y[r̄]).

Fix actual x and choose y with the boxed stable-unique clause. At every accessible point Uxy holds and every U-output at x is y. Consequently f(x) and y are necessarily universally coextensive; Intensionality gives f(x)=y. NI and □Uxy then give □Ux(fx). Generalize over actual x and apply BF at σ to obtain □∀x Ux(fx). The construction is a term; Plenitude and Choice are unnecessary.

Reverse proof. Let P^(σt) satisfy ∀x□Px. Put U(x,q):=Px∧q=⊤. For each x, q=⊤ satisfies the boxed stable-unique clause. SUGR_(σ,t) gives f with □∀x(Px∧fx=⊤), hence □∀xPx. This is BF at σ.

### A second exact criterion under ordinary Plenitude

**Theorem 4.** Under Plenitude and BF at σ, for every actually functional U^(στt), τ≠e,

    (∃f^(στ) □∀x Ux(fx))  ↔  ∀x∃y □Uxy.

Left-to-right is boxed universal instantiation, with y=fx. Right-to-left: V(x,y):=□Uxy is actually serial by the right-hand premise, and actually functional by T and actual functionality of U. Plenitude gives f with ∀x□Ux(fx); BF gives the boxed universal claim. Thus the obstruction to uniform representation, when BF and Plenitude hold, is precisely the lack of a fixed modal output for some input.

In particular if U is actually functional and weakly persistent (`∀xy(Uxy→□Uxy)`), such a uniform representing operation exists. This holds in B and does not collapse modality.

## 3. Four singleton-selection normal forms

For C^((σt)(σt)), let Sel(C) say

    ∀F^(σt) [
      (∀x ((CF)x→Fx)) ∧
      ((∃x Fx)→∃!x (CF)x)
    ].

Let Respect(C) say

    ∀F,G [(∀x(Fx↔Gx))→∀x((CF)x↔(CG)x)].

Respect means coextensive outputs, NOT identical outputs. Types σ may include e, since the operator's output σt is relational.

**Theorem 5.** Over C the following all-type schemata are equivalent respectively:

| Operator form | Existing principle |
|---|---|
| ∃C Sel(C) | Relational Choice |
| ∃C [Sel(C)∧Respect(C)] | Transversal Choice |
| ∃C □Sel(C) | Modalized Relational Choice |
| ∃C □[Sel(C)∧Respect(C)] | Modal Well-Ordering |

The first and third equivalences are direct constructions. For Relational Choice, apply it once to V(F,y):=Fy∨¬∃zFz, which is serial. If S is its functional subrelation, put C(F)(y):=S(F,y)∧Fy. Conversely for any serial U put S(x,y):=(C(λz Uxz))y. Necessarily serial/functional forms give exactly the same proof with boxes: V is necessarily serial by logic, and all the lambda constructions are available at every point. This gives the modal equivalence without BF, Atomicity, Plenitude or any assumptions about constant domains.

For the second forward implication (TC→operator), use the recorded TC→Well-Ordering theorem, take an actual well-order R at σ, and put

    C(F)(x) := Fx ∧ ∀y(Fy→Rxy).

It selects the least element and respects coextension. Conversely let R be an actual equivalence relation, write [x]:=λz Rxz, and set G(y):=∃x(C([x]))y. A chosen y belongs to [x]. If two G-instances y,y' lie in one R-cell, their witnessing cells are coextensive, so Respect makes their selected singleton properties coextensive; singleton uniqueness gives y=y'. Thus G is a transversal.

For the fourth equivalence, Modal Well-Ordering gives the same least-element construction necessarily. Conversely a necessarily correct extension-respecting selector proves □Transversal Choice by applying the preceding lambda construction at every point; the recorded boxed TC→WO equivalence gives □Well-Ordering. Its modal singleton-selection part gives Modalized Relational Choice, hence Intensional Choice. The existing theorem `necessary-well-ordering-and-intensional-choice-imply-modal-well-ordering` then yields Modal Well-Ordering. The use of the existing theorem is legitimate: no optional hypotheses were silently necessitated.

**A sharper collapse boundary.** Replace Respect(C) under the box by

    ∀F,G [(∀x(Fx↔Gx))→CF=CG].

Already at σ=t this stronger modal singleton selector implies Extensionality. For true p, F_p from §1 is actually coextensive with K⊤:=λq(q=⊤), so CF_p=CK⊤. Necessary Sel makes CK⊤ necessarily coextensive with K⊤, hence identical by Intensionality. NI then gives that CF_p is necessarily K⊤. Necessary subpropertyhood CF_p⊆F_p yields □F_p(⊤), hence □p. Conversely under Extensionality the type-t selector choosing ⊥ if F⊥ and otherwise ⊤ is definable:

    C(F)(q):=Fq ∧ (q=⊥ ∨ ¬F⊥).

Since every proposition is ⊥ or ⊤, it is a selector; Extensionality identifies coextensive outputs; modal collapse boxes all clauses. For the ALL-type schema the converse also requires Relational Choice, just as for Modal Functional Choice.

## 4. Rigid Hilbert Choice: a noncollapsing necessary operator

For each relational τ≠e, RHC_τ says

    ∃ε^((τt)τ) □∀F^(τt)
      [(Rigid(F)∧∃y Fy)→F(εF)].

**Theorem 6.** Over B, the all-type RHC schema is equivalent to □Functional Choice.

Benchmark→RHC. Ordinary Functional Choice supplies an actual Hilbert chooser ε from V(F,y):=Fy∨¬∃zFz. Consider any actual F. In B, rigidity is invariant under the S5 modality: it is a boxed condition, and 4/5 fix its truth value. If F is nonrigid, it is necessarily nonrigid, making the desired conditional vacuous. If F is rigid and empty, weak inextensibility applied to ⊥ gives F≤⊥, hence F=⊥, and it is necessarily empty. If F is rigid and nonempty, F(εF) actually holds and persistence gives □F(εF). Thus every actual F necessarily satisfies the desired conditional. BF at τt boxes its universal closure. One and the same ε therefore works at all points on rigid properties.

RHC→benchmark. B gives Rigid Comprehension. Two rigid actual coextensions are identical: weak inextensibility of either against persistence of the other gives mutual entailment. Thus V(F,G):=Rigid(G)∧∀y(Fy↔Gy) is a total single-valued relation from τt to τt. Ordinary Plenitude supplies a canonicalizing operation c. Then ε(cF) chooses from every actual nonempty F. Applying this to each row of an arbitrary serial relation gives ordinary Functional Choice (with relational outputs). Finally No Pure Contingency in B boxes every closed Functional Choice instance.

**Genuine strengthening of B.** Proved-only Engine verifies B in `full-infinite-s5-metatheory-no-countable-choice-reals`, and the record's choice-free argument refutes Relational Choice at (t,t). Thus RHC fails there by the forward reduction above. `full-involution-group` with ordinary metatheoretic choice satisfies B+□Functional Choice with four propositions, so RHC remains compatible with contingency.

## 5. Uniform atomic choice and the monotonicity obstruction

**Theorem 7.** C+□Functional Choice gives, at every relational τ, an operation a_τ:τ→τ such that

    □[a_τ(⊥)=⊥ ∧ ∀X(X≠⊥→Atom(a_τX)∧a_τX≤X)].

Atomicity makes the relation of being an atom below a nonbottom X, with the unique default ⊥ at X=⊥, serial. Ordinary Functional Choice supplies a_τ. In C5, equality and distinctness at every type are necessary, as is algebraic entailment; BF moves quantifiers into boxes. Therefore Atom and the selecting relation are invariant, so each actual selected pair necessarily satisfies the relation. BF at τ boxes the universal selection statement. This is a genuinely uniform operation and does not fall foul of §1: lattice membership/atomhood is modally fixed, unlike contingent instantiation.

**Theorem 8.** At type t, existence of an order-preserving atomic selector is equivalent over C to Extensionality. No Atomicity premise is needed; the selector clause itself implies Atomicity.

Let a select an atom below every nonzero proposition and preserve ≤. Set c:=a(⊤), an atom. For any nonzero p, a(p) is an atom and a(p)≤c by monotonicity, so a(p)=c; hence c≤p. If c≠⊤, ¬c is nonzero, giving c≤¬c, contradiction. Thus c=⊤ and ⊤ is an atom; every nonzero proposition is then ⊤. Every truth is necessary, giving Extensionality as in §1. Conversely under Extensionality a(p):=p is such a selector.

## 6. Splitting operations: choice versus unique choice

All operation types here have relational domain and codomain, so both an operation and its proposed inverse are admitted.

**Theorem 9.** Over C+Plenitude, the schema 'every surjective operation between relational types has a right inverse' is equivalent to Functional Choice. Over B it is therefore equivalent to □Functional Choice, and requiring surjectivity/right-inverse equations necessarily does not change the principle.

Choice→splitting. For a surjection f:A→B the inverse-fiber relation U(b,a):=(fa=b) is serial; Functional Choice gives g:B→A with ∀b f(gb)=b.

Splitting→choice (relational input/output types first). Let U:A×D→t be serial. Fix a₀ and d₀ with U(a₀,d₀). Pair codes H_(a,d):=λxy(x=a∧y=d) lie at relational type ADt and are injective in both components. Define a functional relation V from codes k to A by

    V(k,a) iff [∃d(k=H_(a,d)∧U(a,d))]
       or [¬∃a',d'(k=H_(a',d')∧U(a',d')) ∧ a=a₀].

Plenitude supplies π:(ADt)→A representing V. It is surjective: for any a, seriality provides a valid U-pair code sent to a. A right inverse s:A→(ADt) has π(sa)=a. If a≠a₀, sa cannot be an invalid code (invalid codes map to a₀), and hence uniquely codes a valid U-pair (a,d). Choose d₀ at a₀; elsewhere decode sa. This defines a total single-valued subrelation S⊆U. Plenitude gives an operation selecting S when the output is relational.

For input or output type e, first pass to haecceity codes. A serial relation on arbitrary types σ,τ induces a serial relation on the full relational types σt,τt: on a haecceity input H_x require an output H_y with Uxy, and on non-haecceity inputs choose a fixed haecceity H_y₀. The preceding construction gives a functional subrelation, which pulls back to a functional subrelation of U by injectivity of haecceities. This is Relational Choice, and Plenitude then gives Functional Choice at the allowed outputs.

In B, an actual equation f(gb)=b is necessary by NI; BF at B gives □∀b f(gb)=b. Likewise actual surjectivity ∀b∃a fa=b implies ∀b□∃a fa=b by NI, then □∀b∃a fa=b by BF. Thus the actual and modal splitting versions coincide over B.

**Theorem 10.** Already over B, every injective operation between relational types has a necessary left inverse; no Relational/Functional Choice is required.

Given injective f:A→B and a default a₀, the relation assigning b its unique f-preimage when one exists and a₀ otherwise is total single-valued. Plenitude gives g with g(fa)=a for every a. NI and BF at A give □∀a g(fa)=a.

Bare-C splitting schemata may be interesting independently; no claim about their compatibility with Maximalism is established here. Retractions of all actual injections would force those injections to stay injective necessarily, since g∘f=id equations persist by NI. A suitable contingent injection might therefore give an incompatibility; no such general argument is yet supplied.

## 7. Retractions give ND, but C5 already supplies them

Let LInv denote the schema: every actually injective operation f:A→B, with A and B relational types, has an operation g:B→A with ∀a g(fa)=a.

**Theorem 11.** Over C, LInv implies B, hence all-type ND. Only A=t, B=tt is used.

For arbitrary true p define j_p(q):=λr^t(p∧r=q). If j_p(q)=j_p(q'), evaluate both properties at r=q: p makes the first true, so the second gives q=q'. Thus j_p is actually injective. A left inverse k gives k(j_p⊤)=⊤ and k(j_p⊥)=⊥. NI boxes both identities, so □(j_p⊤≠j_p⊥), since otherwise applying k would identify the necessarily distinct ⊤ and ⊥. The C-equivalence j_p⊤≠j_p⊥↔◇p follows as follows. If □¬p, both properties are necessarily empty, so identical by Intensionality. If they are identical, evaluate at ⊤: p would make the first true and the second false, so their necessary identity forces □¬p. Hence p→□◇p, which is B. The recorded theorem `modal-b-implies-distinctness-necessary-r` then gives ND.

Pure Maximalism is therefore incompatible with unboxed LInv (not merely its necessitation), by the recorded incompatibility with ND.

**Theorem 12.** BF + ND implies every actually injective operation between relational types has a necessary left inverse. Consequently C5 alone implies LInv, strengthening Theorem 10 by dropping Atomicity and Plenitude.

Given actual injection f:A→B choose a default a₀. Let V(b,a) mean `fa=b`, if b has an f-preimage, and `a=a₀` otherwise. Fix actual b. If b=fa for actual a, then NI makes fa=b necessary. For any actual a'≠a, injection gives fa'≠b; ND makes that inequality necessary. BF at A boxes the entire assertion that a is the unique preimage, so V has the same unique output a at every accessible point. If b has no actual preimage, ND makes fa≠b necessary for every actual a; BF at A gives □¬∃a fa=b, so a₀ is its necessarily unique V-output. Thus every actual b has a necessarily fixed unique V-output. Theorem 3, using BF at B, gives an operation g with □∀b V(b,gb); together with the necessary injectivity facts for actual inputs, NI and BF at A give □∀a g(fa)=a. Equivalently one can apply Theorem 3 directly to the inverse-with-default relation and then box the actual left-inverse identities.

**Separation checked with proved-only Engine.** `finite-support-permutations` satisfies BF, ND and □ND, and refutes Actuality, Boolean Completeness, Atomicity and Plenitude. By Theorem 12 it satisfies LInv (indeed necessary left-inverse existence). Thus LInv does not imply any of these stronger principles. Established interval: ND ≤ LInv ≤ C5. Neither equivalence at the ends has been proved here.

## 8. Proposed clearer definitions: status and scope

- **Definition-equivalent forms:** the four rows of Theorem 5 are proposed replacements/variants for Relational Choice, Transversal Choice, Modalized Relational Choice and Modal Well-Ordering. They use only a singleton-subproperty operator and, where appropriate, its respect for coextension. They preserve the fixed type system, include individual inputs, and require no language extension.
- **Definition-equivalent over C:** stable unique graph representation is BF (Theorem 3), while Modal Plenitude and the single type-t Necessary Unique Witness sentence are Extensionality (Theorems 1–2). The latter are NOT innocuous boxed versions of Plenitude: they interchange an existential with a box.
- **Definition-equivalent relative to B:** Rigid Hilbert Choice and surjection splitting are forms of □Functional Choice (Theorems 6, 9). Their equivalence must not be asserted over bare C without the specified assumptions.
- **Genuine weaker fragment:** NUW_t uses only type t, yet entails the full Extensionality schema. The t→tt fragment of injection retractions entails full ND; the full retraction schema has the nontrivial bounds in Theorems 11–12.
- **Genuine strengthening over C+□Functional Choice:** monotone atomic selection and Modal Plenitude collapse contingency, as witnessed by Theorems 2 and 8. Ordinary uniform atomic selection does not.
- **No extended language is used in these results.** All type-variable schemata retain the database's conventions; there is no quantification over types and no operation with output type e.

## 9. Pointwise retractions versus identities of operations

**Terminological correction to §§6–7.** LInv there means pointwise left inverses, `∀a g(fa)=a`. It does **not** by itself assert the identity of operations `(λa.g(fa))=(λa.a)`. By the C theorem Modalized Functionality, that identity is equivalent to `□∀a g(fa)=a`. Call the latter conclusion a **strong left inverse**, and let SLInv say every actually injective operation between relational types has a strong left inverse. Here “actually injective” is the displayed pointwise formula, not an unexplained category-theoretic definition of monomorphism.

Plenitude gives ordinary LInv by the inverse-with-default construction in Theorem 10. The full two-object retract model satisfies Plenitude and fails BF/C5, so ordinary LInv does not entail C5. The finite-support permutations model satisfies C5, hence ordinary LInv, but fails Plenitude and Actuality. Thus C5 and Plenitude are different sufficient conditions for ordinary LInv. Theorem 11 still gives its necessary condition ND. No equivalence of ordinary LInv and ND has been proved.

**Theorem 13 (strong retraction characterization).** Over C,

    SLInv  ⇔  C5.

Only the instances `t→tt` and `tt→tt` of SLInv are needed from left to right. C5 gives all-type SLInv, as proved in Theorem 12. No Atomicity, Actuality, Plenitude or choice is required.

Proof of the new direction. The `t→tt` instance gives ordinary LInv at those types, hence ND_t by Theorem 11. It remains to prove BF_t using the `tt→tt` instance. Fix P^(tt) and suppose `∀q □Pq`. Define the endomorphism F of type tt by

    (F H)(r) := Hr ∧ (r=⊤ → P(H⊥)).

For any actual H, the premise gives `□P(H⊥)`. It follows by ordinary normal modal logic that `□∀r((FH)r↔Hr)`, because the only extra condition is the fixed proposition P(H⊥), independently of r. Intensionality gives `FH=H`. Thus F is actually the identity pointwise, in particular actually injective. SLInv supplies K with `□∀H K(FH)=H`. Consequently F is necessarily injective: at every point equality of two F-images, followed by application of K, gives equality of their arguments.

For arbitrary propositions q,s define the coding operation

    H(q,s)(r) := (r=⊤ ∧ s) ∨ (r≠⊤ ∧ q).

C proves `H(q,s)⊥=q` and `H(q,s)⊤=s`; ⊥≠⊤ is necessary. Boolean algebra and Intensionality give the identity

    F(H(q,s)) = H(q,s∧Pq).

For clarity, this is an identity of properties, not mere actual coextension: substituting the definitions gives necessarily the same extension for every r, using the necessary identity H(q,s)⊥=q. Now put s=¬Pq and s=⊥. Both F-images are H(q,⊥). Necessary injectivity therefore gives, necessarily and for every q,

    H(q,¬Pq)=H(q,⊥).

Application at ⊤ yields `¬Pq=⊥`, hence `Pq` (indeed □Pq). Thus `□∀q Pq`. This is BF_t. The recorded theorem `nd-t-and-bf-t-imply-necessary-nd-t` gives □ND_t, and `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` gives C5.

The type tt endomorphism fragment alone therefore implies BF_t. More generally the identical mask-and-two-slot argument, at operations t→σ, gives BF_σ for relational σ. To prove Theorem 13 only σ=t is needed.

**Corollary.** Maximalist Classicism is incompatible with SLInv. More positively, C+□Functional Choice proves SLInv as a choice-free part of its C5 structure. This does not prove that Maximalist Classicism is contradictory in the original language: the incompatible natural extra axiom is explicit.

**Theorem 14 (simpler definition of BF).** Over C, Functionality is equivalent to BF. In fact Functionality with propositional outputs and fixed input σ is equivalent to BF_σ.

BF→Functionality is the recorded theorem `barcan-r-implies-functionality-r`. Conversely, suppose `∀x^σ □Px`. Since □Px is Px=⊤, the operations P and λx.⊤ have the same value at every argument. Functionality identifies them. Identity plus Leibniz gives their necessary coextension, hence `□∀x Px`. Thus this is exactly BF_σ. No distinctness or choice premise is used. Consequently C5 is also exactly ND + Functionality. Combined with Theorem 13 this identifies three concise presentations of the same package: necessary distinctness, ND plus operation extensionality, and strong retractions of all currently injective operations.

## 10. Weak Gallin comprehension and finite interpolation

**Theorem 15 (weak Gallin form).** The schema saying every relation X has a coextensive Y such that every actual instance of Y is necessarily an instance, and every actual noninstance is necessarily a noninstance, is equivalent over C to Bivalent Evaluation (BE):

    ∀X∃Y [coext(X,Y) ∧∀x(Yx→□Yx)∧∀x(¬Yx→□¬Yx)]
      ⇔ ∃E^(tt)∀p[(p→Ep=⊤)∧(¬p→Ep=⊥)].

For BE→the schema use Yx:=E(Xx). For the converse apply the schema to the truth property λp.p and let E be its coextension. The two persistence clauses are precisely the two required identities, with truth matching inherited from coextension. Tuple versions use the same construction. The independent proof in `/tmp/classicism-research/bivalent-evaluation-root.md` establishes BE⇔ND+Actuality, including its exact stronger and boxed variants; this note does not duplicate that proof. Thus weak Gallin comprehension is strictly weaker than full Gallin comprehension (the double-retraction model has BE but fails full Gallin) and strictly weaker than Plenitude (the sections-and-projection model has ND+Actuality but fails Plenitude).

**Finite interpolation cross-reference.** Root/cardinality research independently proves the sharper exact finite interpolation criterion: for any externally finite prescribed list x_i↦y_i with relational outputs, a representing operation exists iff `□∧_(i,j)(x_i=x_j→y_i=y_j)`. Its immediate clean corollary is “Finite Plenitude”⇔ND, with lists of length two already sufficient and length one a C theorem. This is a finite external schema, with no claim concerning internally nonstandard finite lists. See the root/cardinality report for the proof and precise formulation. A still simpler equivalent is Boolean Separation: for any distinct a,b there is a predicate P with Pa=⊤ and Pb=⊥. ND makes Pz:=(z=a) a witness; conversely these two identities preclude any possible identity of a and b by NI.

## 11. Persistence of injectivity and surjectivity: exact structural classifications

The following schemata speak about ordinary pointwise injectivity/surjectivity at the evaluation point. They do not use unannounced categorical definitions. Define

    Inj(f) := ∀a,a' (fa=fa' → a=a'),
    Surj(f) := ∀b ∃a fa=b.

Let PI be `∀f(Inj(f)→□Inj(f))` at all admitted operation types, and PS be `∀f(Surj(f)→□Surj(f))` at all admitted operation types. An operation's codomain must be relational; its domain may be e. For PI it suffices to restrict both domain and codomain to relational types.

**Theorem 16.** Over C,

    PI  ⇔  C5  ⇔  SLInv.

The source of the simplifying observation PI⇒C5 is parent/root, building on the mask proof of Theorem 13; the present note supplies the audit.

C5→PI: if f is actually injective, fix actual a,a'. If a=a', their identity persists by NI. If a≠a', then fa≠fa' by injection and ND makes that inequality necessary. In either case `□(fa=fa'→a=a')`. BF at the two argument types gives □Inj(f). This includes domain e. Conversely, the `t→tt` instance applied to j_p from Theorem 11 makes it necessarily injective whenever p is true. Since ⊤≠⊥ necessarily, `□(j_p⊤≠j_p⊥)`, giving p→□◇p and hence ND. The `tt→tt` instance applied to the mask endomorphism F in Theorem 13 gives BF_t by exactly the same proof. ND_t+BF_t gives C5. The proof uses only these two instances. Since Theorem 13 gives C5⇔SLInv, all three are equivalent.

**Theorem 17.** Over C,

    PS  ⇔  BF at every relational type.

The exclusion of type e from the conclusion is essential in the fixed language.

Right to left: suppose f:A→B is actually surjective. For each actual b choose an a with fa=b; NI gives □(fa=b), hence □∃a fa=b. Thus ∀b□∃a fa=b. Since B is relational, BF at B gives □∀b∃a fa=b. No choice operator, ND or BF at the domain A is needed.

Left to right: fix relational σ and a predicate P^(σt) with ∀q^σ□Pq. Write c_σ(p) for the constant relation of type σ taking value p on every argument; at σ=t it is p itself. Let A=tσ, and define the endomorphism F:A→A by

    (FH)(r)[u] := H(r)[u] ∧ (r=⊤ → P(H⊥)).

Here u is the tuple of remaining arguments of σ, empty at σ=t. For each actual H, □P(H⊥) gives FH=H by Intensionality, exactly as in Theorem 13. Hence F is actually surjective. PS makes it necessarily surjective. Work now necessarily, and fix arbitrary q^σ. Set

    T_q(r)[u] := (r=⊤) ∨ (r≠⊤ ∧ q[u]).

Thus T_q⊥=q and T_q⊤=⊤_σ. Surjectivity gives an H with FH=T_q. Evaluating at ⊥ gives H⊥=q; evaluating at ⊤ gives

    H⊤ ∧ c_σ(Pq) = ⊤_σ.

Boolean algebra implies c_σ(Pq)=⊤_σ. Since σ is relational and each argument type is inhabited, constant-relation embedding c_σ reflects identity, so Pq=⊤. In particular Pq. Necessarily every q therefore satisfies Pq, which is BF_σ. This proves every relational instance; taking σ=e would require the forbidden operation type t→e, so that substitution is not made.

**Verified strict separation.** The proved-only Engine verifies that `full-two-object-chain-new-individual` satisfies BF at all relational types (indeed necessarily) and refutes all-type BF at e. Its construction has one individual at W₀ becoming two at W₁; the haecceity of the old individual witnesses BF_e failure. Thus it satisfies PS by Theorem 17 while failing BF. This is a model-supported scope distinction, not merely a syntactic failure of the proof.

**Further structural distinction.** The same model refutes ND, and hence PI, while satisfying PS. In the positive benchmark C+□FC both kinds of persistence hold, since it includes C5. Pure Maximalism is incompatible with PI, whereas no claim is made here that it is incompatible with unboxed PS; the latter is only BF at relational types.

**Novelty correction for Theorem 14.** The BF/Functionality equivalence is already in the proved closure through `functionality-r-implies-tractarianism-r` and `tractarianism-r-implies-barcan-r`. The direct propositional-output proof here improves presentation but is not a new implication. The new structural classifications in Theorems 13, 16 and 17 should not inherit an exaggerated novelty claim from that simplification.

**Maximalism asymmetry, established with source caveat.** `coalesced-pinned-interpretations-root` and `coalesced-pinned-substitutions-root` are proved records satisfying Maximalism (pure and for Σ) and all-type BF. The proved-only Engine confirms these premise sets, with ND false. Thus these models satisfy PS while refuting PI. This is positive relative-consistency evidence for surjection persistence together with Maximalism, not merely an absence of a contradiction. The interpretation-root model's notes explicitly say the construction has not been checked by a second reader; no Lean verification is claimed. The direct source is Cian Dorr's construction of 19 October 2026 with its recorded verification, not an independently rechecked new model in this note.

## 12. Plenitude decomposes into Actuality and ordinary retractions

**Theorem 18.** Over C,

    Plenitude ⇔ Actuality + LInv ⇔ BE + LInv.

Here LInv is ordinary pointwise left-inverse existence, with relational domain and codomain, not the stronger operator identity. This gives a genuinely sharper decomposition than the sufficient condition C5+Actuality.

Forward: Plenitude gives Actuality and ND by recorded theorems, hence BE by the independent root proof. Given an actual injection f:A→B, its inverse-on-range with an arbitrary default value is a total single-valued relation. Plenitude represents it, giving ordinary LInv. This uses relational A so an operation with output A is admitted.

Reverse: LInv gives ND by Theorem 11, so Actuality+LInv gives BE. Assume BE+LInv and fix an actual total single-valued U^(στt), with τ relational and σ arbitrary, including e. Let w be an actual-world proposition from Actuality. Thus w is true and `w≤p` for every actual truth p. Let E be a bivalent evaluator. Put A=στt, B=tA, and use the pair codes

    H_(x,y)(u,v) := (u=x ∧ v=y).

These are injective in both components by a theorem of C. Define

    Valid(k) := ∃x,y (Uxy ∧ k=H_(x,y)),
    M(k) := E(Valid(k)).

For each actual k, M(k) is exactly ⊤ if k is valid and exactly ⊥ otherwise. All equalities in this assertion are identities, so NI allows their use inside further operations.

Define operations with values of type B as follows:

    C_x(r)(u,v) := (r=⊤ ∧ w ∧ u=x),
    J(k)(r)(u,v) := (r=⊤ ∧ k(u,v)) ∨ r≠⊤,
    F₀(k)(r)(u,v) := r=⊤ ∧ w ∧
        ∃a,b (Uab ∧ k=H_(a,b) ∧ u=a),
    f(k) := M(k)·F₀(k) ∨ ¬M(k)·J(k).

Multiplication of a proposition and a relational entity denotes pointwise conjunction. The pair-code identity gives, as an identity of B-entities,

    F₀(H_(x,y))(r)(u,v)
       = [r=⊤ ∧ w ∧ Uxy ∧ u=x].

When Uxy is actually true, w≤Uxy, so this is exactly C_x. Thus every actual valid k=H_(x,y) has f(k)=C_x; every actual invalid k has f(k)=J(k). These conclusions are identities, not only coextensions.

The map f is actually injective. Two valid inputs with equal images have C_x=C_(x'), and evaluation at r=⊤, u=x, with w true, gives x=x'. Functionality of U then gives y=y', hence the pair codes are identical. Two invalid inputs are recovered by J(k)⊤=k. A mixed equality is impossible because C_x⊥=⊥_A while J(k)⊥=⊤_A, and these constants are necessarily distinct. Nonemptiness of the component types supplies the harmless arguments for these evaluations; no choice operation is used.

By LInv, f has an ordinary left inverse g:B→A. For each actual x let y be its unique U-output. Then

    g(C_x)=g(f(H_(x,y)))=H_(x,y).

Define the candidate representing operation h:σ→τ by the lambda term

    h(x)[z̄] := ∃y^τ ((g(C_x))(x,y) ∧ y[z̄]).

For the actual selected pair (x,y), substitute the identity g(C_x)=H_(x,y). Ordinary quantified logic reduces the right side necessarily to y[z̄], since H_(x,y)(x,y') is y'=y. Intensionality therefore gives h(x)=y. Thus U(x,h(x)) for every actual x, proving Plenitude. There is no operation with output e in the construction: A and B are relational even when σ=e.

**Strict bounds, now both established.** The sections-and-projection model satisfies ND+Actuality and fails Plenitude, as shown by its recorded sequence n↦Z_n. By Theorem 18 it fails ordinary LInv. Hence ND does not entail LInv, even with Actuality added. The full two-object retract model satisfies Plenitude, hence LInv, but fails C5. Thus

    ND < LInv < C5

are both strict logical-strength comparisons, with explicit proved-record models. The finite-support permutations model also shows LInv does not imply Actuality or Plenitude.

**Corollary 18.1.** `□LInv`, SLInv, PI and C5 are equivalent over C. Indeed □LInv gives □ND=C5 by necessitating the proved implication LInv→ND; C5 implies LInv, and C5 is itself necessary by 4, so C5 gives □LInv. Theorem 13 gives the remaining equivalences. Here moving the existential inverse across the box is legitimate for this particular inverse problem; it is not a general modal choice rule.

**Corollary 18.2.** With RInv meaning every actual surjective operation between relational types has an ordinary right inverse,

    Functional Choice ⇔ Actuality + LInv + RInv.

The forward direction uses the preceding results. Conversely Actuality+LInv gives Plenitude, and Plenitude+RInv gives Functional Choice by Theorem 9. Necessitating this C-theorem gives the corresponding exact presentation of the benchmark:

    □Functional Choice ⇔ □(Actuality ∧ LInv ∧ RInv),

understood as the associated type schemata. The actual-world clause cannot simply be removed or unboxed: the full Boolean-valued model with one atom and an atomless component satisfies C5+Functional Choice but refutes □Functional Choice and □Actuality.

## 13. Full Boolean-valued models: Functional Choice measures the atomic part exactly

This section gives a semantic classification within a specified family, not a representation theorem for every Henkin model of C. It generalizes the recorded `full-boolean-valued-atom-and-atomless` construction. Work in ZFC. Let B be a nontrivial complete Boolean algebra with a designated atom a₀. Let E be any nonempty set, and put

    D_e=E, D_t=B, D_(στ)=(D_τ)^(D_σ)  (τ≠e).

Application is ordinary function application; abstraction is full; equality is crisp, with values 1_B and 0_B. Boolean connectives and quantifiers use the complete Boolean operations. Evaluate truth at a₀: p is true iff a₀≤p. This is a complete Boolean homomorphism to 2, so the construction validates C by the same argument as the recorded model. In particular □p is the crisp proposition expressing p=1_B, and C5 holds. Define the atomic part

    b_at := ⋁{a∈B : a is an atom}.

**Theorem 19.** In this model,

    ||Actuality|| = ||BE|| = ||Plenitude_(t,t)||
                  = ||FunctionalChoice_(t,t)|| = b_at.

Every all-type Plenitude or Functional Choice instance has value at least b_at; the displayed single type pair attains exactly b_at. Consequently □Plenitude and □Functional Choice hold iff B is atomic. The lower bound for Plenitude uses unique choice only; the lower bound for Functional Choice uses metatheoretic choice, which is explicit in the ZFC assumption.

BE calculation. For E':B→B, the Boolean value of Eval(E') is the meet over p∈B of

    (p→[E'p=1]) ∧ (¬p→[E'p=0]),

where brackets are crisp equality values. If E'p is neither 0 nor 1 for some p, the corresponding factor is 0. Otherwise each factor is p or ¬p according as E'p=1 or 0. A nonzero meet d of these chosen literals decides every p: d≤p or d≤¬p. Such a d is an atom. Indeed if 0<q≤d, take p=q; the second possibility is impossible and the first gives d=q. Conversely for each atom a define E'_a(p)=1 iff a≤p, and 0 otherwise. Atomicity of a implies the meet of its chosen literals is exactly a, since the p=a factor bounds it above by a. Thus the join of Eval(E') over all full-domain operations E' is b_at.

Actuality calculation. For a candidate w∈B its contribution is

    w ∧ ⋀_{p∈B} (p→[w≤p]).

If w is an atom this is w. If w=0 it is 0. If w is nonzero and not an atom, choose 0<q<w. Both w≤q and w≤¬q are false, so the meet includes ¬q and q and is 0. The existential join is therefore b_at.

Plenitude/Functional Choice lower bound. At each atom a, the projection π_a(p)=1 iff a≤p is a complete Boolean homomorphism. Applying it to any closed choice instance gives the ordinary classical instance on the underlying full set domains. A functional relation has its uniquely determined representing function, and a serial relation has a choice function in ZFC. These functions are in the full domains. Therefore each atom lies below each instance's Boolean value, so b_at is a lower bound.

Matching upper bound from one relation. Let

    U(p,q) := (p∧[q=1]) ∨ (¬p∧[q=0]).

The Boolean value of both Serial(U) and Functional(U) is 1: for each p the candidate q=1 contributes p and q=0 contributes ¬p to the appropriate existential; all other outputs contribute 0. For f:B→B the value of ∀p U(p,f(p)) is exactly the literal meet computed in the BE argument. Its existential join is therefore b_at. The Plenitude and Functional Choice axioms at (t,t), taking a meet over all U, have value at most b_at. Together with the lower bound this proves the equality.

**Theorem 20 (Gallin-style classification within this full family).** These full Boolean-valued models satisfy □Functional Choice exactly when their Boolean truth algebra is a powerset algebra. More precisely, a complete atomic B is isomorphic to P(W), W its set of atoms, by p↦{a∈W:a≤p}; the inverse sends S⊆W to ⋁S. This isomorphism extends recursively by conjugation to every full operation type. The resulting presentation is the full constant-domain intensional model

    D_e=E, D_t=P(W), D_(στ)=(D_τ)^(D_σ),

with p true at w iff w∈p. This is the explicit sense of “Gallin-style” used here; no claim that all C+□FC Henkin models have full external function domains is intended.

Both E and W can be chosen arbitrarily large. In particular infinite individuals and infinitely many worlds coexist with □FC, and finite choices are also allowed. The typed domain cardinals in this family satisfy |D_t|=2^|W| and |D_(στ)|=|D_τ|^|D_σ|. These are metatheoretic cardinal calculations in the full construction; they are not assertions that the object language proves a particular continuum hypothesis.

**Why inverse axioms alone do not capture the benchmark.** In every complete-B model above, all injective operations have strong left inverses and all surjective operations have strong right inverses, necessarily. They are actual set functions on full domains, so inverse-on-range with a default and ZFC choice provide literal inverse functions. All identities, injection predicates and surjection predicates have crisp Boolean values; the whole splitting statements have value 1_B. Thus categorical splitting alone does not eliminate an atomless component. The necessary Actuality clause does: its Boolean value is 1 exactly when b_at=1. The model B=2×RO(R), designated at its isolated atom, is the recorded concrete separator satisfying C5+FC and both necessary splitting schemata while failing □FC.

The benchmark therefore has the exact structural presentation

    □FC ⇔ □Actuality + SLInv + RInv,

where RInv is ordinary right-inverse existence. Forward follows from prior theorems. Conversely SLInv gives C5 and hence □LInv. With □Actuality, the necessitated Theorem 18 gives □Plenitude. Under that package, ordinary RInv gives □FC by Theorem 9. Retaining □Actuality is essential; replacing it by Actuality admits the atom-and-atomless separator.

## 14. Bijection stability lies strictly between structural requirements

Let PB_rel mean that every actually bijective operation **between relational types** remains necessarily bijective. The input-type restriction is explicit: a proposed inverse with output e is not an admitted operation. Let BI mean that every such current bijection has a strong two-sided inverse.

**Theorem 21.** Over C, PB_rel⇔BI, and PB_rel implies PS (equivalently BF at relational types). C5 implies PB_rel, but the converse is false.

PB_rel→BF_rel uses the same mask endomorphism from Theorem 17: it is actually pointwise the identity, so actually bijective; its necessary surjectivity gives BF_σ for every relational σ. Now let f:A→B be actually bijective, where A,B are relational. PB_rel makes it necessarily bijective. For each actual b, choose an actual a with fa=b. NI makes that equation necessary, and necessary injectivity makes a the necessarily unique preimage of b. Stable unique graph representation (Theorem 3), using BF_B, gives g:B→A with □∀b f(gb)=b. Necessary injectivity then gives □∀a g(fa)=a. This is BI. The converse is immediate from the two necessary inverse identities. C5 implies PB_rel by PI and PS.

**Finite separator: PB_rel does not imply C5 or ND.** In `full-two-object-chain` with singleton individuals, let d_i(σ) be the finite cardinal of type σ at W_i. For relational σ=σ₁…σₙt, full intensions give

    d₀(σ)=2^(Π_j d₀(σ_j)+Π_j d₁(σ_j)),
    d₁(σ)=2^(Π_j d₁(σ_j)),

with d₀(e)=d₁(e)=1 and empty products 1. All relational cardinalities are powers of two, and d₀(σ)>d₁(σ). Write the two products as 2^u and 2^v, with u≥v. Binary uniqueness of 2^u+2^v shows that if d₀(A)=d₀(B) for relational A,B, then d₁(A)=d₁(B). An actual bijection therefore has equally large finite source and target after the nonidentity arrow. BF, which this model satisfies, makes its transported operation surjective; it is consequently bijective. Thus PB_rel holds at the root, and trivially at the terminal world, so even □PB_rel holds. Nevertheless ND fails because distinct root propositions can become identical at the terminal world. This is a new verdict on the specified existing model, proved here rather than supplied by its current record.

**Infinite separator: BF does not imply PB_rel.** In the same full two-object chain with the individual set N fixed at both objects, let S=P(N). The type et has domain S×S at the root (its root extension and its terminal extension) and S at the terminal object; transport is the second projection. Define

    tail(b)={n:n+1∈b},
    prepend(i,a)=({0} if i=1 else ∅) ∪ {n+1:n∈a}.

The operation F:et→et has underlying maps

    F₀(a,b)=(prepend(1_{0∈b},a), tail(b)),
    F₁(b)=tail(b).

They commute with second-coordinate transport, and the full intension domains contain the resulting operation. Explicitly, its root extension at input (a,b) and individual n reads the head bit of b when n=0 and the bit n−1 of a otherwise; its terminal extension reads bit n+1 of b. F₀ is a bijection, with inverse

    (c,d) ↦ (tail(c), prepend(1_{0∈c},d)).

F₁ is surjective and noninjective. Thus PB_rel fails although BF holds. This uses Infinity in an essential way for this example: an infinite bit stream can absorb the bit discarded by transport. No computational approximation is used.

**Even the finite separator refutes RInv.** This verifies that the Plenitude hypothesis in Theorem 9 cannot be silently replaced by BF, Relational Choice, or bijection stability. In the singleton-individual chain, a root proposition is a pair (x,y)∈2×2 and a terminal proposition is y. A root entity H of type tt consists of a subset A of the four root propositions and a subset B of the two terminal propositions; transport forgets A. Define f:tt→t by

    f₀(A,B)=(1_{1∈B},1_{0∈B}),
    f₁(B)=1_{0∈B}.

These maps commute with transport and define a full-model operation. f₀ is surjective. A right inverse g₀ would have to assign to the root target (x,y) a pair (A,B) with B exactly the two-bit subset whose bits at 1 and 0 are x and y. But transport coherence requires this B to depend only on y, since (0,y) and (1,y) have the same transport. This is impossible. Hence RInv fails, even though the model has BF, □Relational Choice and □PB_rel. The point is an actual failure of operation-valued choice, not a failure of ordinary finite set-theoretic choice.

## 15. A sharper decomposition: Functional Choice is Actuality plus right inverses

**Theorem 22.** Over C,

    Functional Choice ⇔ Actuality + RInv.

Thus the LInv conjunct in Corollary 18.2 is redundant. All right-inverse instances used below have relational domain and codomain; input type e in Functional Choice is still covered through pair codes.

### Lemma 22.1: Actuality plus one right-inverse instance gives BE

Assume Actuality and RInv for operations tt→t. Fix w with `w∧∀p(p→w≤p)`. We prove □◇w. Suppose to the contrary that R:=¬◇w is possible. For H^(tt) define

    T(H) := (w∧◇(R∧H⊤)) ∨ (¬w∧H⊥).

This is actually surjective onto t. Fix an arbitrary actual proposition q. If q is true, take a two-slot H with H⊤=⊤ and H⊥=q. Since ◇R is actually true, Actuality gives w≤◇R; also w≤q. Therefore

    T(H)=(w∧◇R)∨(¬w∧q)=q

as an identity. If q is false, take H⊤=⊥ and H⊥=q. Now w≤¬q, so again T(H)=¬w∧q=q. The required two-slot H is the lambda term `(r=⊤∧b)∨(r≠⊤∧q)` for b=⊤ or ⊥; its two values are identities. This is pointwise existential case reasoning, not an illicit global truth-selecting operation.

A right inverse g:t→tt gives T(gq)=q for every actual q. At q=w, since w is actually true, its equation entails

    ◇(R∧(gw)⊤).

At q=⊥, the corresponding equation entails

    ¬◇(R∧(g⊥)⊤).

But C proves necessarily `R→w=⊥`, since R is ¬(w≠⊥). Leibniz therefore gives the necessary equivalence

    R∧(gw)⊤ ↔ R∧(g⊥)⊤.

Their possibilities are the same, a contradiction. Thus ¬◇¬◇w, i.e. □◇w. Together with the chosen actuality property this is Persistent Actuality, which is equivalent over C to BE by the independent root proof. In particular ND follows. Every modal step above either uses a displayed identity or a theorem of C; no premise is illicitly necessitated.

### Lemma 22.2: BE plus RInv gives Functional Choice

Let U^(στt) be any actual serial relation, with τ relational. Fix actual x₀,y₀ with Ux₀y₀. Put A=στt and D=tA. As in Theorem 18 let H_(x,y) be the pair haecceity, let w be an actual-world proposition and E a bivalent evaluator. Define

    Valid(k) := ∃x,y(Uxy∧k=H_(x,y)),
    D_x(u,v) := w∧u=x,
    RangeD(b) := ∃x(b=D_x),
    V(k)(u,v) := w∧∃x,y(Uxy∧k=H_(x,y)∧u=x).

For every actual valid pair code H_(x,y), necessary pair-code injectivity and w≤Uxy give the identity V(H_(x,y))=D_x. Distinct x give distinct D_x because w is true. No D_x is ⊥_A. The pair haecceities are also nonbottom, so ⊥_A is not a valid pair code.

Using E to turn Valid and RangeD into literal ⊤/⊥ coefficients, define an operation π:D→A with the following actual identities:

    π(H) = V(H⊤),     if Valid(H⊤);
    π(H) = H⊥,         if ¬Valid(H⊤) and ¬RangeD(H⊥);
    π(H) = D_(x₀),     otherwise.

This notation is an abbreviation for the pointwise Boolean lambda expression with coefficients E(Valid(H⊤)) and E(RangeD(H⊥)); it does not assume Plenitude or an individual-valued conditional. Its output A is relational.

π is actually surjective. To hit D_x, choose any y with Uxy and take an H with H⊤=H_(x,y); its other slot is immaterial. To hit a b outside RangeD, take H⊤=⊥_A and H⊥=b. Two-slot coding at relational A is a lambda term. Thus every actual target is hit.

RInv gives s:A→D with π(sb)=b. Fix actual x≠x₀, and put k=(s(D_x))⊤ and b=(s(D_x))⊥. If k were invalid, then either b lay outside RangeD and π(sD_x)=b could not equal D_x, or b lay in RangeD and π(sD_x)=D_(x₀), also impossible. Hence k is a valid H_(a,y), and V(k)=D_a=D_x forces a=x. Therefore Uxy and k=H_(x,y).

Decode the selected y by

    d(x)[z̄] := ∃y(k_x(x,y)∧y[z̄]),
    k_x := (s(D_x))⊤.

For x≠x₀ the identity k_x=H_(x,y) implies d(x)=y by the C lambda/Intensionality argument from Theorem 18. At x=x₀ use the fixed y₀ instead, with the bivalent coefficient E(x=x₀) to define one operation h:σ→τ combining y₀ and d(x). Then U(x,h(x)) for every actual x. This is Functional Choice, including σ=e; all constructed function codomains remain relational.

Theorem 22 follows: FC supplies Actuality through Plenitude and supplies RInv by selecting preimages. Conversely Actuality+RInv gives BE by Lemma 22.1 and FC by Lemma 22.2.

**Corollary 22.3: the positive benchmark has a two-part structural presentation.** Let SRInv mean that every actually surjective operation between relational types has a strong right inverse, `□∀b f(gb)=b`, equivalently the operation identity f∘g=id. Then

    C+□FC = C+□Actuality+SRInv.

Forward: □FC supplies □Actuality, and FC supplies ordinary sections; C5/BF boxes their inverse equations. Reverse: SRInv gives RInv, so with Actuality it gives FC by Theorem 22 and hence ND. SRInv also gives PS, hence BF_t by Theorem 17. Thus ND_t+BF_t gives C5. With □Actuality, Theorem 18 and □LInv give □Plenitude. Finally ordinary RInv gives □FC over that package, as in Theorem 9. Equivalently one may use the pure No Pure Contingency theorem now available. The completely boxed pointwise formulation is also exact:

    □FC ⇔ □(Actuality ∧ RInv).

The shorter-looking `□Actuality + RInv` is weaker: the full two-object retract has □Actuality and FC (hence RInv), but refutes C5 and therefore □FC. The difference between pointwise and strong sections is material.

**Corollary 22.4 (the first higher-domain obstruction is genuine).** Actuality plus the right-inverse instance for operations `tt→t` implies BE, by Lemma 22.1. Actuality plus even the *strong* right-inverse instance for `t→t` does not imply BE. In the singleton-individual full two-object chain of §14, every actually surjective operation t→t is a bijection on the four root propositions. Its terminal map is surjective by BF and hence a bijection on the two terminal propositions. The argument for PB_rel⇔BI supplies a strong inverse. Thus the strong t→t splitting instance holds at the root and, trivially, terminally; Actuality holds, whereas ND and BE fail. The explicit nonsplitting surjection tt→t displayed in §14 shows precisely where this finite countermodel ceases to satisfy right-inverse existence. No claim of absolute type-order minimality beyond this contrast is made.

## 16. Actuality is essential in the right-inverse decomposition

**Theorem 23 (algebraic consistency separator).** In ZFC, let B be any nontrivial complete atomless Boolean algebra. Form the full Boolean-valued typed hierarchy of §13, with crisp equality, all set functions at the admitted function types, and quantifiers interpreted by arbitrary meets and joins. Every axiom of C, C5, BF, SLInv and SRInv has Boolean value 1_B, while Actuality, BE and the switching instance of Plenitude/Functional Choice have Boolean value 0_B. The schema of strong inverse axioms may itself be boxed without changing its value. Thus

    C + □SLInv + □SRInv + ¬Actuality

is consistent relative to this ZFC construction. In particular RInv does not entail Actuality or Functional Choice. This is initially an algebraic consistency witness, not a claim that an arbitrary ultrafilter is an ordinary evaluation point.

**Proof.** The verification of C is exactly the Boolean-value verification in the existing write-up `full-boolean-valued-atom-and-atomless.md`, §2, before its separate use of a complete designated projection. Every H-theorem has value 1; all its inference rules preserve value 1. Universal instantiation, generalization and their existential duals use the meet/join universal properties. Equality is crisp and respects substitution; beta and eta are literal equalities of functions. An H-provable equivalence has equal Boolean values under all assignments, so its lambda abstractions are identical functions, validating Logical Equivalence with its original theoremhood restriction. No designated atom is needed for these verifications.

C5 and BF have value 1 by the same crisp-identity and complete-meet calculations as in that write-up. For an actual set function f, its injectivity and surjectivity formulas have crisp values. If it is injective, inverse on its range extended by a fixed default gives a left inverse in the full admitted function domain; if it is surjective, ZFC choice gives a right inverse. Every inverse equation is crisp and has value 1, as does its box. If the corresponding antecedent is false, the implication has value 1. Taking all the quantifier meets therefore gives value 1 to every closed splitting instance and to its box. Only inverse maps with relational outputs are asserted, exactly as in our definitions.

By Theorem 19, the values of Actuality, BE and the switching Plenitude/FC instance equal the join of the atoms of B, here 0. Hence ¬Actuality has value 1. Soundness under value 1 rules out a derivation of contradiction from these premises. This does not assume that a nonprincipal ultrafilter preserves arbitrary meets, and does not treat the atomless component as a previously available classical world.

**Corollary 23.1.** The two conjuncts in FC⇔Actuality+RInv are independently needed. Actuality without RInv is witnessed by the singleton full two-object chain; RInv without Actuality has the algebraic witness above. The analogous necessary-Actuality clause in □FC⇔□Actuality+SRInv is also essential, even if the splitting clause and C5 are both necessary.

**Optional ordinary Henkin realization (separate construction).** An ordinary pointed model can be obtained without claiming that an arbitrary ultrafilter is complete. Regard the full atomless Boolean hierarchy as a many-sorted *algebraic* first-order structure: include application, Boolean operations, the typed quantifier operations, crisp identity operations, and the denotation operation for each syntactic lambda template. There are countably many sorts and symbols. Take a countable elementary substructure M. For each relation F∈D_(σt)^M, let q=∃_σ F in its Boolean sort. The set of nonzero b satisfying

    b≤¬q, or b≤F(x) for some x∈D_σ^M

is dense in the nonzero Boolean sort of M. This assertion is first order in the algebraic structure and holds in the original complete algebra: any nonzero piece below q meets some F(x) nontrivially. It therefore holds in M. Choose a proper ultrafilter G meeting all these countably many dense sets, by the usual descending-sequence construction; also meet the countably many sets deciding each Boolean element. If q∈G, meeting its dense set forces F(x)∈G for some x; conversely any such F(x) puts q in G. Thus the typed existential operators have their ordinary Tarskian meaning under designated truth b∈G; universal operators follow by negation. Closure under the lambda-template operations gives the required lambda denotations. Crisp equality gives literal domain equality.

The resulting countable Henkin structure satisfies precisely the relevant C axioms and closed value-1 assertions above, while Actuality remains false because its denotation is 0. The elementary-substructure step is essential: G need preserve only the quantifier joins represented in the countable algebra, not every external subset of its Boolean sort. This construction uses ordinary downward Löwenheim–Skolem and countably many dense-set choices in ZFC; it does not require a countable transitive model of ZFC or a complete two-valued homomorphism from the original atomless algebra.

## 17. A concrete finite-support obstruction to splitting surjections

**Theorem 24.** The recorded finite-support permutation model on N refutes RInv, already for operations `t(et)→et`, despite satisfying C5, BF, □Relational Choice and Transversal Choice.

Let η_a=λx^e(x=a) be the haecceity of individual a. Put A=et and D=tA. Define Pair(k) to mean `∃a,b(a≠b∧k=η_a∨η_b)`. Define Ordered(H) to mean `∃a,b(a≠b∧H⊤=η_a∧H⊥=η_b)`. In this group model identity is necessary, and these structural predicates are invariant under every permutation; they are literal top/bottom propositions. Consequently the following piecewise prescription abbreviates an admitted Boolean lambda term π:D→A:

    π(H)=H⊤∨H⊥, if Ordered(H);
    π(H)=H⊤,    if ¬Ordered(H) and ¬Pair(H⊤);
    π(H)=⊥_A,   otherwise.

π is actually surjective. A pair η_a∨η_b is hit by the two-slot H with outputs η_a and η_b. A nonpair k is hit by H⊤=k,H⊥=⊥_A: this H is not Ordered, because no haecceity is bottom.

Suppose g:A→D is a right inverse. For any distinct a,b, set k=η_a∨η_b. Since π(gk)=k is a pair, neither escape branch can have been used. Thus (gk)⊤ is either η_a or η_b. The finite-support construction pins g by some finite S⊂N. If a,b lie outside S, their transposition h fixes g as an intension: for every arrow u, u∘h and u agree on S, so the pinned profiles are equal. It also fixes k, and fixes ⊤. Naturality of application therefore makes h fix (gk)⊤. But h interchanges η_a and η_b, contradicting the preceding alternative. Hence π has no right inverse.

This is operation-valued choice of an orientation of every unordered pair. It does not contradict the model's extensionally full relational choice: an extensionally chosen orientation need not have a single finitely pinned operation representing its values as intensions.

## 18. The inverse schemata can be reduced to one mirrored type pattern

Define the following *type fragments*, not abbreviations for the full inverse schemata:

    LInv_fam: every injective f:τ→tτ has a pointwise left inverse (τ relational);
    RInv_fam: every surjective f:tτ→τ has a pointwise right inverse (τ relational).

Use SLInv_fam and SRInv_fam when the respective inverse equations are necessary. The notation tτ means the type of proposition-indexed families of τ-entities. These are natural restrictions of the full splitting schemata; no equivalence to their unrestricted forms over bare C is assumed.

**Theorem 25.** Over C,

    Plenitude ⇔ Actuality + LInv_fam;
    Functional Choice ⇔ Actuality + RInv_fam;
    C5 ⇔ SLInv_fam;
    □Functional Choice ⇔ □Actuality + SRInv_fam.

For the first statement, inspect Theorem 18. Its ND argument uses t→tt, the τ=t instance. Its coding injection has type A→tA with A=στt, again exactly the displayed pattern. Thus its entire reverse proof uses only LInv_fam. The forward implication follows from unrestricted LInv.

For the second, Lemma 22.1 uses tt→t, the τ=t instance. Lemma 22.2 uses tA→A with A=στt. Thus no other right-inverse shape is needed. Functional Choice supplies the full schema and therefore the fragment.

For the third, C5 supplies unrestricted strong left inverses. Conversely the τ=t instance gives ND. For the BF_t part of Theorem 13, take its actually injective mask F:tt→tt and replace it by

    J_F:tt→t(tt),     J_F(H)=λp^t.F(H).

This is actually injective. Its strong left inverse forces F necessarily injective: equality of F-images gives equality of their constant families, and the necessary left-inverse equations then give equality of the arguments. The original mask argument now gives BF_t, hence C5. Only τ=t and τ=tt are used.

For the last statement, the forward implication is immediate. Conversely SRInv_fam gives RInv_fam and hence FC using Actuality. It also gives strong sections for every actually surjective endomorphism F:τ→τ: apply the fragment to

    T_F:tτ→τ,        T_F(H)=F(H⊤),

which is actually surjective whenever F is, and from a strong section s of T_F obtain the strong section `x↦(sx)⊤` of F. In particular the mask endomorphism of Theorem 17 remains surjective, giving BF_t. FC gives ND, hence C5. Together with □Actuality this gives □Plenitude. Theorem 9 and the already obtained FC/RInv give □FC. This proves the necessary benchmark using only the mirrored type fragment.

**A useful strong/pointwise identity.** For the unrestricted schemata,

    SRInv ⇔ RInv + BF_rel,
    SLInv ⇔ LInv + BF_rel ⇔ C5.

The nontrivial forward BF_rel implication for SRInv is PS⇒BF_rel (Theorem 17). In the reverse direction NI makes each pointwise inverse equation necessary, and BF at the relational target of the quantified inverse equation boxes the universal statement. The same BF argument applies to left inverses; the remaining equivalence is Theorem 13. Thus the strong-section wording adds precisely relational Barcan to ordinary sections, before any Actuality assumption is made.

## 19. Categorical language: epimorphisms are necessarily surjective

Work with relational types as objects and operation intensions as arrows, with literal operation identity and lambda composition. Base individuals e are excluded as objects because the fixed language does not supply general arrows with codomain e. This is a type-indexed category description, not an internal quantification over types.

For f:A→B, categorical Mono(f) means left cancellation against every admitted pair g,h:C→A. Categorical Epi(f) means right cancellation against every admitted pair g,h:B→C. Inverse equations in these categorical definitions are identities of operations, hence the *strong* inverse equations of this report. Ordinary pointwise inverses must not be substituted silently.

**Theorem 26.** Over C,

    Epi(f) ⇔ □Surj(f).

It is enough to test right cancellation using only codomain t. Conversely Mono(f) implies ordinary actual Inj(f), but does not imply □Inj(f). Under BF_rel one has

    Mono(f) ⇔ Inj(f),      Epi(f) ⇔ Surj(f).

**Proof for epimorphisms.** Let I_f:B→t be the image predicate `I_f(b):=∃a(fa=b)`, and let 1:B→t be constant truth. The compositions I_f∘f and 1∘f are identical by the logical theorem `∀a∃a'(fa'=fa)`. Thus even cancellation tested only at codomain t forces I_f=1. Modalized Functionality/Intensionality makes this exactly `□∀b∃a(fa=b)`. Conversely suppose this necessary surjectivity and g∘f=h∘f. The latter identity gives `□∀a(g(fa)=h(fa))`; inside the box the witnesses for surjectivity give `∀b(gb=hb)`. Intensionality gives g=h. No BF or choice is used.

**Proof for monomorphisms.** Given fa=fb, use constant arrows t→A with values a,b. Their composites with f are identical, so cancellation makes the constant arrows identical and hence a=b. Conversely, under BF_rel, ordinary injectivity and a composite identity first give `∀c(gc=hc)` pointwise; BF_rel/Functionality then gives g=h. The full two-object chain has BF but distinct propositions can coalesce. The gate injection j_p of Theorem 11 for its actual-world proposition p is therefore categorical monic while not necessarily injective. Thus categorical monic and necessary injectivity are genuinely different concepts here.

**Theorem 27 (Barcan as the cancellation laws).** Each of the following complete schemata is equivalent over C to BF_rel:

    every actually surjective operation between relational types is categorical epic;
    every actually injective operation between relational types is categorical monic.

The first is PS⇔BF_rel by Theorem 26 and Theorem 17. BF_rel gives the second by Functionality, as just shown. For the converse fix a relational σ and P:σ→t with `∀q□Pq`. On A=tσ use the mask endomorphism F of Theorem 17, which is actually pointwise the identity and hence injective. Write H(q,s) for the two-slot family with bottom value q and top value s. Define arrows g,h:σ→A by

    g(q)=H(q,(¬Pq)·⊤_σ),      h(q)=H(q,⊥_σ).

Here the scalar product with ⊤_σ means the constant σ-entity with value ¬Pq. The Boolean mask identity gives `F∘g=F∘h` literally: their top values are `(¬Pq)∧Pq=⊥`, and their bottom values are q. The assumed monic cancellation for this actually injective F gives g=h. Necessary evaluation at the top slot yields `□∀q((¬Pq)·⊤_σ=⊥_σ)`, hence `□∀q Pq`. This is BF_σ. All types used in the cancellation test are relational. There is no appeal to actual Functionality in this reverse direction.

**Interpretive consequences.** The familiar identification of injections with monomorphisms and surjections with epimorphisms already incorporates precisely the relational Barcan schema. With BF_rel explicitly present, “every monomorphism splits” is equivalent to C5, while “every epimorphism splits” is SRInv, equivalently ordinary RInv+BF_rel. Consequently

    □FC ⇔ □Actuality + BF_rel + every categorical epimorphism splits.

The right-to-left implication uses Epi⇔Surj under BF_rel and Corollary 22.3. This is a genuinely categorical restatement only because its inverse identities are strong. It does not establish that categorical epimorphism splitting alone entails BF_rel, ND, Actuality, or FC; those implications have not been proved here.

## 20. Categorical monomorphism splitting is strictly weaker than C5

**Theorem 28.** At W₀, the recorded full two-object retract model satisfies “every categorical monomorphism between relational types has a strong left inverse.” It also satisfies □Actuality, but fails C5. Thus adding even necessary Actuality to this genuinely categorical splitting axiom does not recover C5. This is a new root verdict on the specified existing construction; no boxed verdict for categorical splitting is asserted.

**Operation category at W₀.** Write i:W₀→W₁, r:W₁→W₀, with ri=1₀ and ir=k≠1₁. Each relational type A gives a split-set diagram

    A₀ --i_A--> A₁ --r_A--> A₀,    r_A i_A=id.

An operation based at W₀ is exactly a natural map of these diagrams, with components f₀,f₁ commuting with i and r. One direction is the model's application/transport law. Conversely, given a natural pair of set maps into a relational output type, take at each object its ordinary extension on the trailing relation arguments. These two extensions form a full-model intension. Naturality ensures that application has exactly the prescribed output intensions at both objects. Thus fullness gives every natural map, not merely the term-defined ones. Operation identity means equality of both components, and strong inverse equations mean inverse equations at both components.

**Detecting monomorphisms.** A categorical mono has f₀ injective by constant arrows. Suppose f₁(a)=f₁(a') for distinct a,a'∈A₁. Applying r and injectivity of f₀ shows r_A(a)=r_A(a')=:a₀. The proposition diagram has T₀=2² and T₁=2³, with

    i_T(x,y)=(x,y,y),      r_T(x,y,z)=(x,z).

Every r_T-fiber therefore has a distinguished point i_T(b) and one other point. Define two natural maps g,h:T→A: both root components are constant a₀; on each distinguished fiber point their future components are i_A(a₀); on each other point put respectively a and a'. They commute with i and r. Their f-composites agree at both objects while g≠h, contradicting categorical monicity. Hence f₁ is injective too. Conversely componentwise injections are plainly monic.

**Splitting every mono.** Let f be componentwise injective, and choose a default a_*∈A₀. Put

    g₀(b)=the f₀-preimage of b if b∈im(f₀), and a_* otherwise.

For b₁∈B₁ put g₁(b₁)=the f₁-preimage when b₁∈im(f₁), and otherwise put

    g₁(b₁)=i_A(g₀(r_B(b₁))).

These maps commute with r. They also commute with i: if b₀∈im(f₀), then i_B(b₀)∈im(f₁) with the required distinguished preimage; if b₀∉im(f₀), then i_B(b₀)∉im(f₁), by applying r. Thus g is an admitted natural operation and gf=id at both objects. This proves the strong retraction claim.

**Categorical epimorphism splitting fails in the same model.** This also exhibits why ordinary FC at W₀ does not imply strong categorical choice. For a relational type X=σ₁…σₙt, put N_i=∏_j|D_(σ_j)(W_i)|. Full intensions have root cardinal `2^(N₀+N₁)` and every r_X-fiber has cardinal `2^N₁`, with its distinguished point i_X(x). Choose B=tt and A=t(tt). Their root cardinals are respectively 2¹² and 2⁸⁰; their fibers have cardinal respectively 2⁸ and 2⁶⁴.

Choose a root surjection f₀:A₀→B₀ such that every target has at least two preimages, and label the preimages over each b₀ by 0 or 1 with both labels present. Split the future fiber over b₀ into two proper subsets S₀,S₁, each containing the distinguished point, with S₀∪S₁ the whole fiber. For instance omit one nondistinguished point from S₀ and take S₁ to consist of that point and the distinguished point. Map each source fiber over a₀ surjectively onto S_label(a₀), sending its distinguished point to the distinguished point. The displayed finite cardinal bounds permit this. The resulting f₁ commutes with i,r, and is surjective. Thus f is necessarily surjective and therefore categorical epic by Theorem 26.

It cannot have a natural section. A section's root value g₀(b₀)=a₀ determines one source fiber into which its entire future target fiber must map, by naturality with r. But f₁ of that source fiber is only the proper subset S_label(a₀), so fg cannot be identity on the target fiber. Hence this categorical epimorphism has no strong section, although ordinary pointwise right inverses exist by FC at W₀.

**Limits of the present classification.** C5 implies categorical mono splitting, but its converse fails by Theorem 28, even with □Actuality. The latter conjunction does not imply FC either: any recorded C+□Plenitude+¬Relational Choice model already has C5 and hence categorical mono splitting. For categorical epi splitting, BF_rel reduces it to the already classified SRInv. Whether Actuality or □Actuality alone suffices to recover the omitted BF_rel premise has not been proved here.

**Syntax clarification for §§19–20.** Epi is expressible by the single codomain-t cancellation formula in Theorem 26. Unrestricted categorical Mono, by contrast, is presently a metalinguistic condition testing all admitted source types; we have not reduced that universal type test to one native formula over bare C. Thus the unrestricted categorical-mono splitting statements above are structural semantic assertions unless such a reduction or a language extension is specified. Theorem 28 proves the stronger, completely native schema

    ∀f^(AB)(Mono_t(f)→∃g^(BA)[g∘f=id_A]),
    Mono_t(f):=∀u,v^(tA)(f∘u=f∘v→u=v),

at W₀ of the retract model. Indeed its proof tested collisions using only source t. This schema is sufficient for categorical-mono splitting and is implied by C5, because Mono_t(f) implies ordinary injectivity by constant tests. The same countermodel therefore establishes strict weakness without introducing a type quantifier. No claim that Mono_t and unrestricted Mono are definitionally equivalent over C is made.

**Canonical retraction lemma (bare C; sharpening the earlier proof).** The stable factorization argument in `quotient-abstraction-lane.md`, §9, gives, for each fixed f:A→B with relational A,

    ∃g:B→A [g∘f=id_A]  ⇔  □Inj(f).

The reverse implication has the canonical witness

    g(b)[ū] := ∀a^A(b=fa→a[ū]).

At f(a₀), the necessarily injective hypothesis makes every preimage identical to a₀; a₀ itself is a preimage. Thus the displayed universal intersection has exactly the same values as a₀ at every accessible point, giving the operation identity by Intensionality. Outside the image it simply gives top. The forward implication follows by cancellation with g inside the necessary inverse equation. No BF, Actuality, Plenitude or choice is used. This replaces the more elaborate C5→SLInv proof in §6; the proof of the converse schema SLInv→C5 is unchanged.

Consequently the exact categorical hierarchy is

    strong split mono ⇔ necessarily injective ⇒ categorical mono ⇒ actually injective.

Both one-way steps can be strict. The full chain's gate map is monic but not necessarily injective. The retract model's mask from a BF failure is actually injective but not necessarily injective; by its categorical-mono classification in Theorem 28 it is not monic. Dually,

    strong split epi ⇒ categorical epi ⇔ necessarily surjective ⇒ actually surjective.

The retract-model epimorphism in §20 separates the first implication; its BF failure and the mask of Theorem 17 separate the last. These are comparisons of individual maps, not merely implications between large schemata.

## 21. Two compact definition proposals

These are proposed equivalent presentations, not additional axioms to count as independent strengthenings.

**Actuality as a single truth fiber.** The following particularly small formula is equivalent over C to Actuality:

    ∃f^(tt)∀p^t [p ↔ f(p)=f(⊤)].

Given an actual-world proposition w, use f(p)=w∧p. A true p gives w≤p, hence f(p)=w=f(⊤); a false p gives f(p)=⊥, distinct from w. Conversely let f satisfy the displayed formula and put

    v := ∀p(f(p)=f(⊤)→p).

This v is true. If q is true, f(q)=f(⊤); NI makes that equation necessary. The necessarily valid quantifier instance from v then gives □(v→q). Hence v entails every truth and witnesses Actuality. Equivalently one can demand that the kernel of f be precisely actual propositional equivalence, `f(p)=f(q)↔(p↔q)`. This is the low-type extraction of the persistent-truth-predicate/quotient argument in the independent structural report, §§1–2, not a separate claim of literature novelty. The same reverse proof works for an operation into any relational output type and a designated output value.

**Functional Choice as extension-respecting Hilbert choice.** At each relational τ, demand an operation ε:(τt)→τ satisfying

    (∃x Fx) → F(εF),
    [∀x(Fx↔Gx)] → εF=εG.

The all-type schema is equivalent over C to Functional Choice. The first clause alone already gives FC by `h(x)=ε(λy.Uxy)` for an arbitrary serial U. Conversely FC gives an ordinary Hilbert chooser ε₀ by choosing from `Fy∨¬∃zFz`. Its Actuality consequence supplies w. Put K(F)=λx(w∧Fx) and ε(F)=ε₀(K(F)). The cut K preserves actual extensions and sends coextensive F,G to identical properties by Actuality, so the two clauses follow. Empty properties also receive one common default because their cut is literally bottom. Thus requiring choices to depend only on the current extension adds no strength to Functional Choice, although that coherence is a genuine additional issue for relation-valued choice without Plenitude.

One may further require contraction consistency without strengthening the all-type principle:

    [∀x(Fx→Gx) ∧ F(εG)] → εF=εG.

The proved-only database closure gives FC→Well-Ordering (via Actuality→Transversal and Relational Choice→Transversal Choice→Zorn). Choose a well-order on τ and use Plenitude to represent its least-element function, with one default for empty properties. Its least-element definition gives contraction consistency and coextension respect. Conversely its selection clause still gives FC. This is an orderly-choice presentation of the same axiom, not a claim of an extra implication among the database's existing principles.

Modal scope remains crucial: □FC gives a possibly different such operator at every world. Requiring one ε to satisfy its ordinary selection clause necessarily for *all* properties is the collapsing Modal Functional Choice principle of §1; restricting the necessary clause to rigid properties yields the noncollapsing benchmark characterization of §4.

## 22. Closing the ordinary-retraction interval

The uncertainty noted in §§7–9 about the lower endpoint can now be removed using an existing proved countermodel and Theorem 18:

    ND < LInv < C5.

Both inequalities are strict as implications over C. The recorded `finite-support-sections-and-projection` model satisfies ND and □Actuality but refutes Plenitude (its explicit graph witness is recorded on 16 October). If it satisfied LInv, Theorem 18, Actuality+LInv⇒Plenitude, would contradict that verdict. Hence it refutes LInv. This separates ND from LInv even with Gallin comprehension and necessary Actuality present. The full two-object retract has Plenitude and hence LInv, while failing C5, proving the other strictness. C5⇒LInv and LInv⇒ND were proved above.

This is a new derived model verdict based on a new theorem, not a new construction or a claim that the source independently proved failure of LInv. It requires no additional premise in the background. The proved-only Engine query on 22 October returned the finite-support-sections-and-projection separator for GC versus Plenitude; its own explicit arguments establish □Actuality and ¬Plenitude, and ND follows from its recorded retraction geometry.

The strong identity remains exact: SLInv⇔C5. The statement RInv⇒ND over bare C remains unproved here, and is not implied by this strict interval.
