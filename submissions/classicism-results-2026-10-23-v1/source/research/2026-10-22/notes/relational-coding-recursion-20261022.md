# Well-founded recursion and relational coding over Classicism

Research scratch, 22 October 2026. Original arguments in this note are by the current OpenAI Codex research agent. They are not attributed to a paper and have not been independently checked by a named person. No Lean work and no database edits were performed. This note gives mathematical arguments, not novelty claims. For any eventual record of these arguments the direct source is `misc`.

## 1. Fixed framework and recorded inputs

The fixed theory is C in the relational type system: types e,t and σ→τ only when τ≠e. All schema type variables are metalinguistic. Ordinary object variables are closed before boxing. In particular no operation e→e is used below.

The exact positive background of interest is C+□Plenitude, equivalently C+□ND+Atomicity, and the stronger C+□Functional Choice. Unboxed ND+Atomicity is not substituted for it.

Local files read include `background.md`, the Plenitude, Functional Choice, Transversal Choice and Strong Possibility principle records, `groups/coalesced-sums.yaml`, and the singleton and constant-indexed coalesced-root records. Source construction locators: Bacon and Dorr, Classicism, draft 16 May 2023, Appendix E, Definition E.2, pp. 80–83; full action models §3.5, pp. 58–61. This note relies on those recorded construction theorems; it does not claim to reprove soundness of C's action-model semantics.

A proved-only Engine query with optional assumptions in the queried premise set confirmed:

- □Plenitude entails □ND, Atomicity, Boolean Completeness, Rigid Comprehension, □BF and No Pure Contingency.
- Functional Choice entails Plenitude and Transversal Choice. The latter recorded chain is Functional Choice ⇒ Relational Choice; Functional Choice ⇒ Plenitude ⇒ Actuality ⇒ Transversal; Transversal + Relational Choice ⇒ Transversal Choice.
- □Plenitude excludes Pure Maximalism, by Plenitude ⇒ ND and the recorded incompatibility of Maximalism with ND.

The proofs below use these recorded facts only where stated. In particular Theorem 1 does not need Boolean Completeness, BF, Rigid Comprehension, Extensionality, or choice. Theorem 2 uses the recorded Functional Choice ⇒ Transversal Choice chain.

## 2. The precise recursion schemas

Fix any input type σ and any relational output type τ≠e. Write F=σ→τ for the admitted operation type. A dependency relation is R:σ→σ→t. Write R(y,x) for its left-nested application.

We require **strict well-foundedness**:

WF(R) :≡ ∀X:σ→t [(∃x Xx) → ∃x (Xx ∧ ∀y (Xy → ¬R(y,x)))].

This differs intentionally from the background's non-strict-order minimality convention. A self-loop is prohibited by this definition. No transitivity, linearity or well-ordering is required.

A specification is U:σ→F→τ→t, with U(x,f,y) meaning that y is an admissible output at x given the history f. Define

Agree_R(x,f,g) :≡ ∀z [R(z,x) → fz=gz].

Local_R(U) :≡ ∀x f g [Agree_R(x,f,g) → ∀y (U(x,f,y) ↔ U(x,g,y))].

Thus a rule may inspect only the values at R-predecessors of x, even though its syntactic input is a total operation. The locality clause uses equality of output entities, not mere coextension.

Serial(U) :≡ ∀x f ∃y U(x,f,y).

Deterministic(U) :≡ ∀x f ∃y [U(x,f,y) ∧ ∀z (U(x,f,z)→z=y)].

Sol(U,f) :≡ ∀x U(x,f,fx).

**Deterministic well-founded recursion (DWR):**

WF(R) ∧ Local_R(U) ∧ Deterministic(U) →
∃f [Sol(U,f) ∧ ∀g (Sol(U,g)→∀x fx=gx)].

The uniqueness is deliberately pointwise. In C, two operations can be pointwise equal at the evaluation point without being identical. No stronger equality is silently inserted.

**Well-founded dependent choice (WFDC):**

WF(R) ∧ Local_R(U) ∧ Serial(U) → ∃f Sol(U,f).

Each is a type schema in σ and τ≠e, with R and U universally closed. Its boxed form boxes those closed instances.

## 3. Theorem 1: Plenitude is equivalent to DWR over C

### 3.1. DWR implies Plenitude

Given a total single-valued V:σ→τ→t, take R empty and U(x,f,y):≡V(x,y). Empty R is strictly well-founded; U is local because it ignores f. DWR supplies f with V(x,fx) for every x. This is precisely Plenitude. The uniqueness part of DWR is not needed in this direction.

### 3.2. Plenitude supplies total patches

We use two instances of Plenitude below to turn explicitly total single-valued graphs into operations. Since τ≠e, a default d=⊥_τ exists. Conditional output graphs are written using material cases, such as

(x=c ∧ y=a) ∨ (x≠c ∧ y=fx).

These are total and single-valued by ordinary classical reasoning and identity elimination. We do **not** silently replace this graph by a pointwise Boolean conditional term at τ: in C the truth of its condition need not make that condition identical to ⊤.

### 3.3. Compatible partial solutions

Call X:σ→t downward closed when

Down(X) :≡ ∀x y [(Xx ∧ R(y,x))→Xy].

A partial solution is a pair (X,f), where f:F is total as an operation but its equations are required only on X:

Good(X,f) :≡ Down(X) ∧ ∀x [Xx→U(x,f,fx)].

The empty property together with λx.d is a partial solution.

**Compatibility lemma.** If Good(X,f) and Good(Y,g), then ∀x [(Xx∧Yx)→fx=gx].

Proof. If disagreement occurs, form the property Zx :≡ Xx∧Yx∧fx≠gx by λ-abstraction. Strict WF gives an R-minimal c in Z. Every predecessor z of c belongs to X and Y by downward closure and cannot belong to Z by minimality. Thus fz=gz for every predecessor z. Locality implies U(c,f,y)↔U(c,g,y) for all y. Both fc and gc satisfy the same total single-valued output rule, so fc=gc, contradicting Zc. This argument uses no equality between f and g as operations. □

### 3.4. The union domain and its operation

Define

Ax :≡ ∃X f [Good(X,f)∧Xx].

Then A is downward closed. Define the graph V by

V(x,y) :≡
[Ax ∧ ∃X f (Good(X,f)∧Xx∧y=fx)]
∨ [¬Ax ∧ y=d].

Every x has an output. On A, any two outputs are equal by the compatibility lemma; off A the only output is d. Plenitude supplies F:F with V(x,Fx) for every x.

For x∈A choose Good(X,f) with Xx. The construction and compatibility give Fx=fx. If R(z,x), downward closure gives Xz and hence Fz=fz. Locality transfers U(x,f,fx) to U(x,F,Fx). Therefore Good(A,F).

### 3.5. There can be no missing point

Suppose ¬A is inhabited. Strict WF gives c∉A with every R-predecessor of c in A. Choose y satisfying U(c,F,y); determinism gives uniqueness, though only existence is needed in this extension step.

By Plenitude realize the patch graph to obtain G with Gc=y and Gx=Fx whenever x≠c. Put Bx :≡ Ax∨x=c. Then B is downward closed: this is immediate on A, and all predecessors of c are in A.

For x∈A, no predecessor z of x equals c, since A is downward closed and c∉A. Hence G and F agree on all predecessors of x, and Gx=Fx. Locality and Good(A,F) give U(x,G,Gx).

For x=c, strict WF implies ¬R(c,c), and every predecessor z is in A, so z≠c. Thus G and F agree on all predecessors of c. Locality carries U(c,F,y) to U(c,G,y), and Gc=y.

Consequently Good(B,G), which by the definition of A yields Ac, a contradiction. Therefore A is universal and F solves U everywhere.

### 3.6. Pointwise uniqueness

If f and g are total solutions, the compatibility lemma applies with X=Y=⊤. It gives ∀x fx=gx. This completes DWR and Theorem 1. □

### 3.7. Boxed equivalence and exact operation identity

Each direction above is a theorem of C from finitely many relevant schema instances. Discharge premises before necessitation. Necessitation and K then give

C+□Plenitude = C+□DWR.

No optional premise was necessitated while still undischarged.

In C5, BF and NI imply that actual pointwise equality ∀x fx=gx yields □∀x fx=gx; Modalized Functionality then yields f=g. Thus under □Plenitude one may strengthen DWR's uniqueness conclusion to equality of the operation itself. The equivalence in Theorem 1 remains stated with pointwise uniqueness, because that is the form proved from unboxed Plenitude without unrecorded extra assumptions.

## 4. Theorem 2: Functional Choice is equivalent to WFDC over C

### 4.1. WFDC implies Functional Choice

Given a serial relation V:σ→τ→t, take empty R and U(x,f,y):≡V(x,y). The same reduction as §3.1 produces a selecting operation. Thus WFDC implies Functional Choice.

### 4.2. Why simply choosing an output for each history is insufficient

Functional Choice directly gives some K with U(x,f,K(x,f)). But two histories f,g agreeing on the relevant predecessors might be assigned different permitted outputs by K. Such a K need not be local. Applying deterministic recursion to it would therefore be invalid.

The next construction chooses per **equivalence class of relevant histories**, with actual equality of the selected class representatives. This is the substantive step.

### 4.3. Code pairs and take a transversal

Let κ=σ→F→t, an admitted relational type, and define the pair haecceity

H(x,f) :≡ λu:σ v:F. (u=x ∧ v=f).

C proves H(x,f)=H(x',g) iff x=x' and f=g, by the background's tuple-haecceity coding lemma.

On κ define the relation

E(c,d) :≡ c=d ∨ ∃x f g [c=H(x,f) ∧ d=H(x,g) ∧ Agree_R(x,f,g)].

This is an equivalence relation at the evaluation point. Reflexivity comes from c=d; symmetry and transitivity on codes come from agreement on predecessors and injectivity of H; noncodes form singleton classes. No extensional equality between cells is used.

Functional Choice entails Transversal Choice by the recorded proof chain in §1. Take a property T:κ→t selecting exactly one element from every E-class. The graph

Q(c,d) :≡ E(c,d)∧Td

is total and single-valued. Plenitude, which follows from Functional Choice, gives r:κ→κ with Q(c,rc). If E(c,d), the transversal's uniqueness gives rc=rd. In particular, whenever f,g agree on x's predecessors,

r(H(x,f)) = r(H(x,g)).

Every representative of a coded E-class is itself a code H(x,h) with the same x and h agreeing with the input history on x's predecessors.

### 4.4. Choose outputs on selected codes only

Write Code(c):≡∃x f c=H(x,f). Form the serial relation W:κ→τ→t:

W(c,y) :≡
[Tc ∧ ∃x f (c=H(x,f)∧U(x,f,y))]
∨ [(¬Tc∨¬Code(c))∧y=⊥_τ].

If c is a selected code, seriality of U gives a witness; otherwise the default works. The coding lemma makes its represented x,f unique, so any W-output at a selected code is an output permitted for its represented history.

Functional Choice gives k:κ→τ with W(c,kc) for every c. Define the operation

G :≡ λx:σ f:F. k(r(H(x,f))).

For an input (x,f), let its representative be H(x,h). Then h and f agree on the predecessors of x, and k(H(x,h)) is permitted by U(x,h,_). Locality gives

U(x,f,G(x,f)).

If f and g agree on the predecessors of x, their representative codes are identical, hence G(x,f)=G(x,g). Thus G is a deterministic local rule in the required pointwise sense.

### 4.5. Apply deterministic recursion

Define U_G(x,f,y):≡y=G(x,f). It is total single-valued and local. Functional Choice gives Plenitude, so Theorem 1 supplies an F with Fx=G(x,F) for all x. The displayed permission property then gives U(x,F,Fx) at each x. This proves WFDC. □

### 4.6. Boxed equivalence

Again these are uniform derivations from finitely many schema instances, so the boxed forms are equivalent:

C+□Functional Choice = C+□WFDC.

This is a new formulation of the favored theory, not a purported independent strengthening. It combines arbitrary strict well-founded dependency graphs with arbitrary serial local choices, and uses the actual relational type system. It can be stated without committing to a particular ordinal notation, arithmetic type, or individual-valued function type.

## 5. Scope and audit caveats for the recursion results

1. These are ordinary internal impredicative proofs. “All partial solutions” is a λ-defined property/graph at admitted types, not an external set of semantic objects or an external powerset assumption.
2. R need only be well-founded at the evaluation point for the unboxed theorem. Boxed premises give the theorem separately at every world; one does not assume an actual R remains well-founded elsewhere.
3. Strict WF is essential. Substituting the non-strict definition which allows the minimal element to be its own predecessor would allow circular dependence and invalidate the proof.
4. Output τ=e is excluded from operation-based recursion, because σ→e is not an admitted type. An individual-output graph recursion is a different statement and should not be conflated with these schemas.
5. Patches and the union are realized by Plenitude. Neither a material conditional at relation type nor coextension-as-identity is smuggled in.
6. WFDC's representative construction cannot be replaced by direct arbitrary choice on full histories. The transversal step repairs that genuine locality problem.
7. Over Pure Maximalism and hence Strong Possibility, the full DWR and WFDC schemas fail, because they imply Plenitude, which implies ND and is incompatible with Maximalism. This is a failure of some admitted schema instance, not a statement that every instance or every familiar recursion fails.
8. Full S5 models in ZFC satisfy □Functional Choice and hence all these recursion principles. This is model-backed consistency relative to the ordinary metatheory; no stronger consistency assertion is claimed.

## 6. General root transplant observation

This is a separate semantic observation, useful as a limitation on any unrestricted claim that Maximalism has no natural compatible mathematical strengthening.

Let φ be a pure modal-free sentence in the extensional second-order relational fragment over individuals: variables of type e and finite-arity individual relation types e^n→t, individual equality, relation application, ordinary connectives and quantifiers over these variables. Equality of relation variables is excluded, or written explicitly as current coextension. There is no application of a higher-order relation to an individual relation as an argument. Suppose φ has a standard full second-order model on a nonempty set D.

**Transplant assertion.** φ is satisfiable both with C+□Plenitude and with Pure Maximalist C.

For C+□Plenitude, use a full S5 model with constant individual set D (even one world suffices), and realize the ordinary relations as constant intensions. At any evaluation world all ordinary subsets of D^n occur as extensions, so the extensional-fragment truth lemma follows by induction.

For Pure Maximalism, take the recorded set of component action models complete for C and form a coalesced root. Set the root individual domain to D. For each component choose an individual d_i and let every root individual be transported to d_i by the distinguished arrow; later transports follow the component action. This is the same freedom in the root individual action used by the singleton and constant-indexed variants, specialized to constant maps from arbitrary D. Give root relational domains all free root extensions compatible with arbitrary component intensions, as in `groups/coalesced-sums.yaml`. Every subset of D^n is then the current extension of some root relation. The extensional-fragment truth lemma is again a direct induction, since duplicate intensions with one current extension cannot be distinguished in this fragment. Every C-consistent pure sentence is still true in some component, so Pure Maximalism holds at the root.

A categorical example is “there exist ordered-field operations on the individuals making them a Dedekind-complete ordered field”, with operations represented by ternary relations, a binary order, and individual parameters for zero and one. Standard R supplies the full second-order model. This axiom is compatible with both theories and fixes the external cardinality of the individual carrier to the continuum in full semantics.

This does not box the sentence in the maximalist model. Pure Maximalism makes individual plurality and its negation possible; the constant-map root transports distinct field elements into coincident component individuals. Under C+□Plenitude the pure sentence is necessary by the recorded No Pure Contingency theorem. Thus the difference is mathematical stability across worlds, not a blanket inability to have ordinary mathematics at the current maximalist root.

**Construction caveat.** The arbitrary-D coalescence is an elementary variation of the recorded construction, argued here from its free-root clauses. It is not an existing separate model record and has not been reverified from the original PDF. The second-order fragment restriction is essential: arbitrary intensional equality of predicates or arbitrary higher-order application is not covered by the truth lemma.

## 7. Restricted rigidity in the constant-map root

A further observation, to be checked independently before integration: the constant-map root in §6 appears to satisfy Rigid Comprehension for relations whose argument tuple consists only of individuals.

Given an actual subset E⊆D^n, let Y have root extension E. If E is empty, let Y be bottom in every component. If E is nonempty, let Y's component i be the haecceity of the tuple (d_i,...,d_i). These are admissible component relations and hence give a root relation.

Persistence at the root follows because every tuple in E transports to that same tuple; component haecceities are rigid. For weak inextensibility at the root, suppose H necessarily holds of every current instance of Y. If E is nonempty, fix one tuple a∈E. In component i the assumed necessity implies that H_i necessarily holds of the transported tuple (d_i,...,d_i); therefore the component haecceity entails H_i. At the root H includes E. Thus Y≤H componentwise. If E is empty the argument is trivial. At every component Y_i is a haecceity or bottom and is rigid, giving full rigidity of Y.

For the empty argument tuple (propositions), if the actual proposition is true, ⊤ is a rigid coextension; if false, ⊥ is one. The claim is restricted to e-tuples, not arbitrary higher-type arguments. It does not imply the full Rigid Comprehension schema which Maximalism excludes.

## 8. A general Strong Possibility reflection lemma

Let E be a closed pure sentence of the form ∃x_1...x_n θ, where θ is a finite Boolean combination of identity formulas between terms of admitted types. Then

C ⊢ E→□_≠E.

For each identity A=B, NI gives its ordinary necessity and hence its distinctness-preserving necessity. For a disequality A≠B, use the true witness q=(A≠B) in the definition □_≠p:=∃q(q∧□(◇q→p)); NI gives □(◇(A≠B)→A≠B). Put θ in disjunctive normal form; normality of □_≠ and elementary case reasoning give θ→□_≠θ. Existential introduction under the modality then gives E→□_≠E. All free variables are closed in the theorem.

Consequently, if Max(C)+¬E is consistent, Strong Possibility supplies ◇_≠¬E and the theorem yields ¬E. Strong Possibility therefore realizes only those existential equational patterns that are forced by Max(C). This recovers the recorded one-individual conclusion by taking E to say that two individuals are distinct.

This is a systematic search principle, not yet a contradiction proof or a countability bound. Maximalism already implies propositional infinity, so finite upper bounds on the entire propositional type cannot be supplied by this method. No unconditional at-most-countability consequence has been established here.

## 9. A modal Knaster–Tarski theorem already in C

This section gives a useful boundary on the preceding comparison. Canonical monotone fixed points do not require the full Boolean Completeness schema.

Fix a relational type τ=σ_1...σ_n t, allowing n=0. Let F:τ→τ and write

Mon(F) :≡ ∀p q [p≤_τ q → Fp≤_τ Fq],

Pref(F,p) :≡ Fp≤_τ p.

Define an actual term, without a choice principle,

μF :≡ λa_1...a_n. ∀p:τ [Pref(F,p) → p[a_1,...,a_n]].

For n=0 this is simply the displayed quantified proposition, without an outer λ. The complete μ operation is the λ-abstraction over F; its type is (τ→τ)→τ and is admitted.

**Theorem 3 (modal Tarski).** C proves

□Mon(F) → [F(μF)=μF ∧ ∀p(Pref(F,p)→μF≤_τ p)].

Thus every necessarily monotone operation has a least fixed point, and indeed a least prefixed point, explicitly given by μ. No BF, ND, Atomicity, Boolean Completeness or Plenitude is needed for this statement.

**Proof.** First, C proves the Park induction implication

(1) Pref(F,p) → μF≤p.

The premise is an algebraic identity, hence NI makes it necessary. Necessarily, the defining universal quantifier of μF can be instantiated at p; with the necessary prefix premise this gives the necessary pointwise implication from μF to p. By the equivalence between algebraic order and necessary pointwise entailment this is (1). No quantifier is moved past a box by BF.

Using (1), ordinary reasoning at the evaluation point gives the C theorem

(2) Mon(F) → ∀p [Pref(F,p) → F(μF)≤p].

For if Pref(F,p), then μF≤p; monotonicity gives F(μF)≤Fp≤p.

Necessitate this theorem, after universally closing its free object variable F. By universal instantiation under the box and K, □Mon(F) gives

(3) □∀p [Pref(F,p) → F(μF)≤p].

At any world covered by (3), if F(μF)[ā] holds, then for every local p with Pref(F,p), order gives p[ā]. Hence the defining universal formula μF[ā] holds. Because (3) is boxed, this inference yields the necessary universal pointwise implication, i.e.

(4) F(μF)≤μF.

This step is exactly where necessary rather than merely actual monotonicity is used. The p-quantifier in (3) is already inside the box; no BF is assumed.

By T we also have Mon(F) at the evaluation point. Applying it to (4) gives F(F(μF))≤F(μF), so F(μF) itself is prefixed. Apply (1) with p=F(μF) to obtain μF≤F(μF). Antisymmetry gives F(μF)=μF. The least-prefixed clause is (1); every fixed point is prefixed, so μF is also the least fixed point. □

Dually, define

νF :≡ λā. ∃p:τ [p≤Fp ∧ p[ā]].

The same argument with order reversed gives a greatest fixed point of every necessarily monotone F, and the greatest postfixed point. Again this is a theorem of C with the stated necessary-monotonicity hypothesis.

**C5 strengthening.** C5 makes every identity and disequality proposition rigid, and BF preserves rigidity under universal quantification, as in the existing C5/No Pure Contingency write-up's rigidity lemma. Consequently Mon(F), which is built from algebraic identities by connectives and quantifiers, is rigid: Mon(F)→□Mon(F). Therefore C5 alone proves ordinary Knaster–Tarski for every operation monotone at the evaluation point. Atomicity, and hence the extra strength of □Plenitude over C5, is not needed for this consequence.

**What is not claimed.** This does not show that all actual monotone operations have fixed points in bare C, nor that fixed-point principles imply Boolean Completeness. The explicit μ computes a meet for a canonically specified family of prefixed points under necessary monotonicity; it is not a greatest-lower-bound operator for arbitrary contingently specified properties. In particular it would be erroneous to use this theorem as a direct source of BC or as a new contradiction for Pure Maximalism.

## 10. Finite interpolation: a much smaller obstruction to Maximalism

Here is a simpler, mathematically familiar reformulation of ND. Fix any type σ and any relational type τ. For a positive integer n define the finite interpolation assertion

FI_{σ,τ,n} :≡ ∀x_1...x_n:σ ∀y_1...y_n:τ
[(∧_{i<j}x_i≠x_j) → ∃F:σ→τ (∧_{i=1}^n F x_i=y_i)].

This concerns prescribed **intensional output identities**. It is stronger than merely making predicates have desired truth values at the evaluation point.

**Theorem 4.** For every fixed σ and relational τ, the two-point instance FI_{σ,τ,2} is equivalent over C to ND at σ. ND at σ also yields every finite interpolation instance FI_{σ,τ,n}. In particular, the full finite interpolation schema is equivalent to ND, and its boxed version to C5.

**Two-point interpolation ⇒ ND.** Given x≠x', prescribe F x=⊤_τ and F x'=⊥_τ. If ◇(x=x'), NI makes both prescribed output identities necessary; at a world identifying x and x', substitution gives ⊤_τ=⊥_τ, impossible in C. Thus ¬◇(x=x'), i.e. □(x≠x'). The top and bottom relations are necessarily different at every admitted relational type.

**ND ⇒ finite interpolation.** Given the pairwise distinct input tuple, ND makes every off-diagonal disequality necessary. At each prescribed input x_j the propositions (x_j=x_i) are therefore ⊤ for i=j and ⊥ otherwise. Define F pointwise at τ=ρ_1...ρ_k t by

F z := λa_1...a_k. ∨_{i=1}^n [(z=x_i)∧y_i[a_1,...,a_k]].

With k=0, omit the inner λ and argument tuple. Substitution of the equalities to ⊤ or ⊥ and H's Boolean identities yields F x_j=y_j as an intensional identity. This step uses actual identities of the equality propositions with ⊤ or ⊥, supplied by NI and ND, rather than assuming that their current truth values determine their identities. □

At (σ,τ)=(t,t), an especially short equivalent is

∀p q [p≠q → ∃F:tt (Fp=⊤ ∧ Fq=⊥)].

The reverse direction needs only the haecceity operation F:=λr.(r=p). Fp=⊤ is a theorem, and ND gives Fq=⊥ for q≠p.

**One explicit pure failed interpolation instance under Maximalism.** Put

m := ∀x^e y^e. x=y.

The closed pure identity m=⊤ and its negation are both C-consistent: use one-world full models with one and with two individuals respectively. Pure Maximalism therefore gives

m≠⊤ and ◇(m=⊤).

There is no F:tt satisfying Fm=⊥ and F⊤=⊤. If there were, NI would preserve both output identities at a world where m=⊤, contradicting ⊤≠⊥.

This is a failure of a single two-input assignment, already at the propositional type, not merely the failure of some unspecified all-type choice instance. C+□Functional Choice, and already ND_t, admits all such assignments whenever the inputs are distinct.

**Qualification essential to interpretation.** Maximalism does not prevent the two propositions from being distinguished by current truth values of some property: the haecceity λr.(r=m) does that trivially. What fails is mapping them to the specifically prescribed intensions ⊥ and ⊤. Calling this an inability to distinguish propositions without this qualification would be misleading.

The mathematical hierarchy is consequently precise: finite intensional interpolation corresponds to ND; interpolation of arbitrary total single-valued relational specifications is Plenitude; interpolation of arbitrary serial specifications is Functional Choice. The well-founded formulations above express the same distinctions for recursive systems.

## 11. Hereditarily rigid parameters and full mathematical absoluteness

This extends the recorded closed No Pure Contingency proof, and complements the Frege lane's numerical-parameter theorem. It is an original parameter extension of that proof, not a claim of historical novelty. Its fixed background in this section is BP:=C+□Plenitude. The argument in fact uses C5, Atomicity at t, and the recorded atom-swap/conjugation machinery; Rigid Comprehension is needed for the representation consequence in §11.5, not for the conditional absoluteness proof itself.

### 11.1. The core predicates

Define a pure predicate Core_σ recursively on the syntax of the fixed relational types. At e put Core_e(x):=⊤. For every relational type τ=σ_1...σ_n t (n may be zero), put

Core_τ(Y) :≡ Rigid(Y) ∧
∀x_1...x_n [Y[x_1,...,x_n] → ∧_{i=1}^n Core_{σ_i}(x_i)].

For n=0 the support clause is vacuous, so Core_t(p):=Rigid(p), equivalent in C5 to p=⊤∨p=⊥. Every argument type σ_i has lower syntactic complexity than τ, making this an ordinary external recursion defining one pure formula at each fixed type; no object-language type quantification is introduced.

The support condition is only an actual current-extension condition. A stronger boxed-support version would also work, but is not needed in the theorem. Rigid(Y) is the background's global persistence-and-inextensibility predicate, unchanged.

### 11.2. Rigid relations have bivalent membership under ND

**Lemma.** Under ND at the argument types, if Y is rigid then for every tuple ā the proposition Y[ā] is identical either to ⊤ or to ⊥, according as it is true or false.

For a true instance, persistence gives □Y[ā]. For a false instance, let Z[x̄]:≡x̄≠ā. Every actual instance x̄ of Y differs from ā. Finite ND yields □(x̄≠ā), so ∀x̄(Y[x̄]→□Z[x̄]). Inextensibility, evaluated at the current world, gives Y≤Z. Hence necessarily Y[ā] implies ā≠ā, giving □¬Y[ā]. The definitions □p=(p=⊤), ◇p=(p≠⊥), together with Boolean identities, give the claimed identities with ⊤ or ⊥. The empty tuple case is the same argument with Z=⊥.

### 11.3. Core entities are fixed by every atom swap

Take distinct propositional atoms w,w′. Under the rigid hypothesis H:=Atom(w)∧Atom(w′)∧w≠w′, the recorded No Pure Contingency argument defines the atom-swapping involution F on propositions and its conjugations T_σ at every type. T_e is the metalinguistic identity substitution on individuals, not an ee term. At a relational type τ=σ_1...σ_n t, conjugation has the pointwise form

(T_τY)[ā] = F(Y[T_{σ_1}a_1,...,T_{σ_n}a_n]).

It is involutive, and fixes pure logical terms in the sense of the recorded equivariance theorem. BF gives Functionality, so equality of the displayed values at all actual tuples suffices to identify the operations.

**Core fixedness lemma.** Under H, Core_σ(x) implies T_σx=x for every type σ.

Proof by induction on the type syntax. At e this is the definition of T_e. At relational τ, let Core_τ(Y) and abbreviate the transformed argument tuple by T ā. If Y[ā] holds, the core support condition and induction hypothesis give T ā=ā. Conversely, if Y[T ā] holds, each T a_i belongs to its lower core and is therefore fixed by its conjugation. Involutivity gives a_i=T a_i. Consequently

Y[T ā] ↔ Y[ā]

at the current world, for every ā. Lemma 11.2 makes both membership propositions bivalent as intensions, so their current equivalence is equality of their ⊤/⊥ values. F fixes those values. The displayed conjugation equation therefore gives

(T_τY)[ā]=Y[ā]

for every actual tuple. Functionality, or BF plus NI and Modalized Functionality iterated over the tuple, gives T_τY=Y. This includes t with an empty tuple. □

### 11.4. Parameter absoluteness theorem

Let A(z_1,...,z_k) be any pure formula whose only free variables are the displayed ones, at fixed admitted types σ_i. A may contain modalities and quantify over arbitrary admitted intensional types; it is not restricted to the arithmetic fragment or to quantification over the core. Then BP proves

∀z_1...z_k [(∧_i Core_{σ_i}(z_i)) → (□A(z̄) ∨ □¬A(z̄))].

Equivalently, on those parameters both A→□A and ¬A→□¬A hold.

Proof. Fix core parameters and a pair of distinct atoms. The equivariance theorem for pure terms gives F(A(z̄))=A(Tz̄). Core fixedness gives Tz̄=z̄, hence F(A)=A. If A is true but not necessary, then A and ¬A are both nonbottom. Atomicity at t supplies w≤A and w′≤¬A; the atoms are distinct. The atom-swap equation exchanges their truth profiles, so F(A)=A yields w′≤A, contradicting w′≤¬A. Thus A→□A; apply the argument to ¬A for the converse direction. Optional assumptions are used only in this conditional proof, not inserted into Logical Equivalence's theoremhood side condition. □

Immediate cases:

- All pure formulas with arbitrary individual parameters are noncontingent, since every individual is in Core_e.
- The same holds with arbitrary rigid predicates or finite-arity relations on individuals as additional parameters.
- It continues through rigid sets of such predicates, rigid relations between them, and all finite levels of this hierarchy.
- The analogous hierarchy starting from the Frege lane's pointwise-fixed natural-number core gives arbitrary rigid real parameters, rigid sets of reals, and higher analysis parameters. Its proof is the same fixed-support induction; Frege number fixedness replaces T_e=id at the base.

The last conclusion is not merely necessity of parameter-free arithmetic sentences. It is a broad modal absoluteness result for arbitrary parameters representing ordinary typed mathematical objects.

### 11.5. Every actual extensional property on a core has a unique rigid representative

Let X be any admitted relation on a finite tuple of types, and form the property obtained by restricting its actual extension to tuples in the respective cores. Rigid Comprehension, supplied by BP, gives a rigid Y with that same current extension. By definition its actual support lies in the lower cores, so Core(Y).

If two rigid Y,Z have the same current extension, Lemma 11.2 makes their membership values identical at every tuple, and BF/Functionality gives Y=Z. Thus the representative is unique.

This is **internal** powerset/relational representation: it covers every property already admitted by C's domains. It is not a claim that arbitrary external subsets occur in every Henkin model. In full S5 models the representation is genuinely full: starting with individuals D, the cores recover the ordinary full typed hierarchy with two truth values, P(D), P(P(D)), and the corresponding finite-arity relations. Arbitrarily many worlds and the whole intensional hierarchy remain outside that ordinary core.

### 11.6. The hereditary support restriction is necessary

It would be false to assert absoluteness for arbitrary rigid parameters without the lower-core support restriction. In a full two-world S5 model take a contingent proposition p and its haecceity X:=λq.q=p. Haecceities are rigid, but X's instance p is not in Core_t. The pure formula

A(X):≡∃q (Xq∧q)

has the same truth value as p at every world, hence is contingent. Thus rigid properties of arbitrary intensions can encode contingency. The theorem isolates the ordinary mathematical hierarchy, not all rigid properties indiscriminately.

## 12. Monism makes every hereditary rigid core finite, already over C

The core predicates of §11 can also be studied without BP. The following facts are theorems of C and use no optional modal principles.

### 12.1. Rigid coextensions are identical

If Y,Z are rigid and ∀ā(Y[ā]↔Z[ā]) holds actually, then Y=Z. Every current Y-instance is a Z-instance and therefore necessarily a Z-instance by persistence of Z. Inextensibility of Y, evaluated at the current world, gives Y≤Z. The converse gives Z≤Y; Boolean antisymmetry gives equality.

This strengthens the uniqueness proof in §11.5: BF and ND are unnecessary for uniqueness of rigid representatives. They were used there only as a convenient stronger route.

### 12.2. Finite unions of tuple haecceities are rigid

For any finite list of tuples ā_1,...,ā_k at a fixed argument-type tuple, let

Y[x̄] :≡ ∨_{j=1}^k x̄=ā_j.

For k=0 this is bottom. C proves Rigid(Y).

Persistence follows from NI for each of the finitely many tuple identities. For inextensibility, reason at an arbitrary world and suppose ∀x̄(Y[x̄]→□Z[x̄]). Each displayed ā_j satisfies Y by reflexivity, so □Z[ā_j] holds for every j. Necessarily, an x̄ satisfying Y is equal to some ā_j, hence satisfies Z by identity elimination. Thus Y≤Z. This argument is a theorem with the tuple parameters free; universal closure and necessitation give the required global inextensibility clause. No optional local premise is necessitated.

This assertion concerns finite disjunctions of haecceities, not arbitrary unions or intersections of arbitrary rigid relations.

### 12.3. Exact finite-core spectrum

Suppose there are exactly m individuals, for a fixed standard positive integer m. Define ordinary finite integers c_σ recursively by

c_e=m,

c_{σ_1...σ_n t}=2^(c_{σ_1}⋯c_{σ_n}),

where the empty product is 1, so c_t=2.

Then, at every fixed admitted type σ, exactly c_σ entities satisfy Core_σ.

Proof by induction on types. At e this is the hypothesis. At relational τ, the possible tuples of lower-core instances form an actual finite set of size the displayed product. Every subset of that finite tuple set is the current extension of the finite union of its tuple haecceities, which is rigid by §12.2 and supported on the lower cores; hence it defines a Core_τ entity. Different subsets have different extensions and therefore different entities. Conversely every Core_τ entity has one of these subsets as its actual extension, and §12.1 identifies it with the corresponding finite haecceity union. There are therefore exactly the stated power-of-two many. All finite lists in this argument are external fixed schema lengths, so this is a family of ordinary finitary C proofs, not an infinitary comprehension assumption. □

### 12.4. Consequence for Strong Possibility

The recorded theorem gives individual monism from Strong Possibility (pure). Taking m=1 in §12.3, Strong Possibility forces

|Core_e|=1, |Core_t|=2, |Core_{et}|=2,
|Core_{(et)t}|=4, |Core_{((et)t)t}|=16,

and similarly a fixed finite size at every fixed finite type.

In contrast, Maximalism, which Strong Possibility entails, supplies arbitrarily many pairwise distinct propositions. The map p↦λā.p injects propositions into any relational type τ=āt: equality of the constant relations gives p=q after applying them to a tuple, using inhabitedness of the types. Thus every ambient relational type has arbitrarily many entities, while its ordinary hereditary rigid core is finite.

This is a structural sharpening of e-monism, not a contradiction. It exhibits a large gap between ordinary rigid mathematical objects and ambient intensional entities. In particular no fixed finite level of the hereditary rigid core over the singleton individuals contains a Dedekind-infinite domain or a complete ordered-field domain. Strong Possibility's infinitely many finite-cardinality intensions must exploit entities outside this finite ordinary core.

The statement does not identify the Frege-number domain with the core and does not silently declare the whole propositional type finite or countable. It also does not exclude encoding arithmetic using non-core intensional entities.

## 13. Exact finite interpolation criterion in C

The finite interpolation theorem of §10 has a precise compatibility form already provable in C. For any fixed positive integer n, admitted input type σ and relational output type τ,

∃F:σ→τ ∧_{i=1}^n(Fx_i=y_i)

is equivalent in C to

□∧_{i,j=1}^n(x_i=x_j → y_i=y_j).

**Necessity.** If F realizes the prescribed outputs, NI preserves each identity Fx_i=y_i at every accessible world. Whenever x_i=x_j there, congruence gives Fx_i=Fx_j and hence y_i=y_j. Universal closure of the pointwise modal argument gives the displayed compatibility condition.

**Sufficiency.** Write τ=ρ_1...ρ_k t and define

Fz := λā.∨_{i=1}^n[(z=x_i)∧y_i[ā]],

with the outer tuple abstraction omitted at t. At z=x_j its j-th disjunct is y_j[ā]. At every accessible world, each other disjunct has x_j=x_i as a conjunct, so boxed compatibility makes y_i=y_j there. Hence the whole disjunction is equivalent to y_j[ā] necessarily and at every argument tuple. Modalized Functionality / the necessary-pointwise characterization of the Boolean order gives Fx_j=y_j. □

Thus C already realizes every finite assignment whose prescribed outputs respect all possible identifications of its inputs. ND is exactly what removes the compatibility obstruction for actual distinct finite inputs. The explicit two-point Maximalist obstruction in §10 is an instance of this complete criterion: the prescribed output intensions never coincide, while the prescribed input intensions can coincide.

This also identifies precisely which equality notion is doing the work. Merely current consistency of finite data is insufficient in C; necessarily compatible finite data is sufficient without Plenitude.

## 14. A theoremhood-safe expansion of the finite-rigidity argument

This supplies the requested witness audit for §12.2. Fix once and for all a standard finite list length k and tuple arity n. These are metalinguistic finite indices. The tuples ā_j remain free object variables throughout the following C derivations; they are not existential witnesses moved under a box.

Put H_j(x̄):=(x̄=ā_j) and Y:=λx̄.∨_{j≤k}H_j(x̄). NI and finite propositional reasoning prove, with x̄ and the ā_j free,

    Y[x̄] → □Y[x̄].

Universal closure in x̄ and then necessitation of the discharged theorem, leaving the parameter notation as abbreviations for universally quantified variables, gives □∀x̄(Y[x̄]→□Y[x̄]). Equivalently one can universally close all variables, necessitate, then instantiate under □ by CBF. This is exactly persistence. The k=0 case is the theoremhood of bottom's persistence.

For inextensibility, let Z be an arbitrary same-type relation and temporarily assume A:=∀x̄(Y[x̄]→□Z[x̄]). Reflexivity and universal instantiation give A→□Z[ā_j] for each fixed j. The formula

    (∧_{j≤k} Z[ā_j]) → ∀x̄(Y[x̄]→Z[x̄])

is a theorem of pure predicate logic with identity; its proof uses the finite disjunction defining Y and substitution at each disjunct. Necessitate this theorem and use K with the finitely many consequences □Z[ā_j]. This proves

    A → □∀x̄(Y[x̄]→Z[x̄]),

or A→Y≤Z. Discharge A, universally close Z and all tuple parameters, and necessitate this THEOREM. Universal instantiation under the box now gives the required □∀Z(A→Y≤Z). Thus Rigid(Y) follows. Nothing in this derivation boxes the assertion that a chosen finite list enumerates a currently finite property. The enumeration is used only later, outside the box, to establish current coextension with the already rigid finite union.

For the empty tuple arity, H_j is ⊤, so the construction gives ⊥ for k=0 and ⊤ for k>0. Hence Rigid_t(p)↔(p=⊥∨p=⊤) already in C: if p is true, persistence makes it top; if false, inextensibility applied to ⊥ makes it bottom. This also justifies the c_t=2 base implicit in §12.

## 15. C5's ordinary extensional core

This section concerns C5=C+□ND, not BP unless explicitly stated. All interpretations use the SAME relational type system; they do not introduce operations with output e. The constructions provide a Henkin interpretation, not fullness with respect to all external subsets.

### 15.1. A simpler rigidity criterion

For Y of type σ̄t define

    Biv(Y) := ∀x̄ [Y[x̄]=⊤ ∨ Y[x̄]=⊥].

Then C5 proves Rigid(Y)↔Biv(Y). The forward implication is §11.2 and needs only ND at the argument types. For the converse, first observe that Biv(Y) is itself bivalent under C5: it is built entirely from identity propositions, Boolean connectives and quantifiers, so the identity/BF rigidity lemma applies.

At a world with BF and Biv(Y), suppose ∀x̄(Y[x̄]→□Z[x̄]). For each actual tuple x̄, either Y[x̄]=⊥, which makes □(Y[x̄]→Z[x̄]) immediate, or Y[x̄]=⊤, in which case the assumption gives □Z[x̄] and again □(Y[x̄]→Z[x̄]). BF gives □∀x̄(Y[x̄]→Z[x̄]), i.e. Y≤Z. Thus Y is weakly inextensible. Biv(Y) also makes every Y-instance necessary, so Y is weakly persistent.

This is a C derivation of the implication from the needed BF instances and Biv(Y) to weak rigidity. C5 supplies □BF, and Biv(Y) is necessary whenever true. Necessitate the discharged implication and apply K to obtain necessary weak rigidity, which is precisely the background's Rigid predicate. In particular the argument does not silently necessitate the optional Biv hypothesis.

Consequently, under C5 the source's rigidity and Gallin's condition Persistent(Y)∧Persistent(¬Y) coincide. One direction follows from Biv and its necessity. Conversely Gallin's condition makes each current membership either necessarily true or necessarily false, hence Biv.

### 15.2. The core predicates themselves are rigid

For every fixed σ, C5 proves

    ∀x^σ [Core_σ(x)=⊤ ∨ Core_σ(x)=⊥].

Induct on σ. The e-case is constant truth. At τ=σ̄t, the proposition Rigid(Y) is bivalent: persistence is an algebraic identity, and inextensibility is a boxed proposition, hence itself an identity with ⊤. If Rigid(Y) is false, Core_τ(Y) is bottom by Boolean identities. If it is true, §15.1 makes every Y[x̄] bivalent. The inductive hypothesis makes every lower Core_{σ_i}(x_i) bivalent. Therefore the support implication is bivalent pointwise; BF makes its universal closure bivalent. Conjunction with Rigid(Y) proves the result. This is pointwise reasoning with identities to ⊤ or ⊥, so no contingent support hypothesis is boxed.

Apply §15.1 to the relation Core_σ itself. It is rigid, and its support condition at type σt is tautological. Thus

    Core_{σt}(Core_σ).

This assertion is special to C5 and should not be inferred from the bare-C finite-core count. Under bare C, a current finite enumeration can have a rigid union of haecceities coextensive with the universal property even when that universal property is not rigid.

### 15.3. Application and abstraction within the core

If Core_{στ}(F) and Core_σ(a), then Core_τ(Fa). Writing τ=ρ̄t, pointwise bivalence of F gives bivalence of the slice Fa, so §15.1 makes it rigid. Its support lies in the lower ρ_i-cores by the support condition on F. This proves application closure.

For abstraction, suppose a typed construction B(x):τ is core-valued whenever x is in Core_σ, with its other parameters core-valued as stipulated by an inductive translation. Define its guarded abstraction by

    F := λx^σ z̄^ρ̄. Core_σ(x) ∧ B(x)[z̄].

At a non-core x the guard is the bottom proposition. At a core x, all membership values of B(x) are bivalent and its support is in the ρ̄-cores. Hence F has bivalent membership and the required hereditary support: Core_{στ}(F). At a core x, F x=B(x); this follows from equality of all pointwise values and C5's Functionality, or from rigid coextensionality once both slices are known rigid. All types displayed are admitted since τ≠e.

Equality is interpreted by ambient equality restricted to core objects. Boolean constants and quantifiers are guarded analogously; for example the quantifier on σ is represented by

    Q_σ(X) := Core_{σt}(X) ∧ ∀x^σ(Core_σ(x)→Xx).

The identity/BF and bivalence lemmas ensure this is core-valued on core arguments, and its guarded abstraction belongs to the appropriate core type. At σ=e the ordinary individual quantifier is recovered, since Core_e is universal.

Extensionality holds in the core. If F,G are core at στ and agree on every core input, then their values at all other inputs are bottom (pointwise, by hereditary support). Thus they are currently coextensive as full flattened relations. §12.1 identifies them. In particular every core proposition is exactly ⊤ or ⊥ and every core relation is determined by its extension on lower-core arguments.

These clauses give a translation of extensional classical Henkin higher-order logic, in the fixed relational types, into C5: quantifiers are restricted to the appropriate Core predicates and abstractions are guarded. This is an interpretation theorem, not a claim that all ambient functions or all external set-theoretic functions lie in the core.

### 15.4. Restricted mathematical absoluteness needs no Atomicity

Every formula in the just-described core interpretation, with core parameters, is bivalent already under C5. Atomic equality is bivalent by ND. Atomic relation application is bivalent by rigidity of its core relation. Boolean combinations preserve bivalence. Restricted quantifiers preserve it by §15.2 and BF. Structural induction proves A=⊤∨A=⊥ and hence A→□A together with ¬A→□¬A.

This differs from §11.4: there Atomicity is used to allow arbitrary ambient quantifiers and arbitrary pure formulas with core parameters. Here quantifiers and terms remain inside the interpreted core, so an elementary bivalence induction suffices. Neither result claims that C5 decides all those mathematical sentences; modal stability is not syntactic completeness.

### 15.5. BP's stronger representation property

BP already entails □RC by the proved record `c5-and-atomicity-imply-necessary-rigid-comprehension`; RC is not an additional hypothesis here. Consequently, for every admitted ambient relation X of type σ̄t, there is a unique core Y with

    ∀x̄ [Y[x̄] ↔ (X[x̄] ∧ ∧_i Core_{σ_i}(x_i))].

Apply RC to the displayed restricted property. Its rigid coextension has the required current support, hence is core; uniqueness is §12.1. Thus the core represents every admitted ambient subset of its lower-core tuples. It need not represent subsets absent from the ambient Henkin domains.

Plenitude then realizes this unique representative assignment by a local operation c_τ:τ→τ. It is idempotent and fixes every core relation. Moreover

    c_τX=c_τZ ↔ ∀x̄[(∧_i Core_{σ_i}(x_i))→(X[x̄]↔Z[x̄])].

This is a current coextension quotient with canonical core representatives. Its defining coextension condition is LOCAL: in a multiworld full S5 model an actual-world rigidification operation need not remain a rigidification for the changing extensions at other worlds. No inference of a single necessarily correct rigidification witness is intended. Boxed existence of an appropriate operation at every world is a different, valid consequence of BP.

## 16. A minimal individual collapse under Maximalism

Let E₁:=∀x^e y^e(x=y). A one-world full singleton model verifies its C-consistency. Max therefore entails ◇E₁. Normal modal logic and universal instantiation give

    Max ⊢ ∀x^e y^e ◇(x=y).

Consequently Max together with ND restricted just to e entails E₁. Equivalently, by §10, Max plus two-point prescribed interpolation for operations e→t entails E₁. Gallin comprehension restricted to unary individual properties also suffices: for distinct a,b, a Gallin-rigid coextension of the haecceity of a would make its membership at a necessarily true and at b necessarily false, preventing a and b from possibly coinciding. Thus it gives ND_e.

These are small local obstructions: Max plus any of the preceding individual principles is inconsistent with merely ∃x y(x≠y), and hence with individual Infinity. There is no inconsistency in the monist case, where ND_e and the two-point implication are vacuous. This statement is separate from Strong Possibility's unconditional monism.

More generally, if R on individual tuples is persistent, and □∀x¬R(x,x), then Max forces its actual binary extension empty. Any current edge R(a,b) would persist, whereas a and b can coincide at some accessible world, contradicting necessary irreflexivity. This illustrates why local relational presentations of an ordered field at a free maximalist root, as in §6, do not by themselves supply a necessarily irreflexive persistent ordering.

## 17. Graph recursion: the exact difference made by operation realization

The operation-valued recursion principles of §§2–4 should not be confused with recursion producing a functional relational graph. Graphs can have individual outputs. Their deterministic recursion theorem is already provable in C. This distinction is mathematically relevant: the earlier equivalence with Plenitude concerns actual realization by an admitted operation and intensional output identities.

### 17.1. The graph formulation

Fix any input and output types σ,τ, including τ=e, and set κ:=στt. Histories are graphs G:κ satisfying

    Fun(G):=∀x^σ∃!y^τ Gxy.

For a strict well-founded R:σσt use

    Agree_R(x,G,H):=∀z^σ[Rzx→∀y^τ(Gzy↔Hzy)].

Let U:σκτt. Its history-locality condition concerns functional histories only:

    ∀x G H [(Fun(G)∧Fun(H)∧Agree_R(x,G,H))
       →∀y(U[x,G,y]↔U[x,H,y])].

Assume also ∀xG(Fun(G)→∃!y U[x,G,y]). A solution is a functional graph F such that

    ∀xy(Fxy→U[x,F,y]).

**Graph recursion theorem (C).** Under strict WF(R), history-locality and this unique-output condition, a solution exists. Any two solutions are currently coextensive. Their intensional identity is not asserted.

### 17.2. Proof without Plenitude

Choose one default d:τ using inhabitedness of the type. This is a single existential elimination, not a choice function. A good partial solution is a pair (A,G), with A:σt downward closed under R, G functional on the whole type, and the displayed solution equation holding on A. The empty property and the constant-value graph λxy(y=d) provide one.

Two good partial solutions (A,G),(B,H) agree in their values on A∩B. Otherwise the property of x in A∩B at which their unique values differ has an R-minimal member c. Every predecessor z of c belongs to A∩B by downward closure, and minimality makes G,H coextensive at z. Thus Agree_R(c,G,H). The two chosen values at c satisfy U with the respective histories; locality puts them in the same U-output fiber, whose uniqueness makes them equal, a contradiction.

Let D(x):=∃A,G(Good(A,G)∧Ax). Define the graph F directly by abstraction:

    Fxy := [Dx∧∃A,G(Good(A,G)∧Ax∧Gxy)] ∨ [¬Dx∧y=d].

Compatibility proves this graph functional. D is downward closed. If Dx, choose a good (A,G) containing x. At every predecessor of x, both the union graph F and G have the compatible partial-solution value; hence their histories agree there. The equation for G at x and locality give the equation for F at x. Thus (D,F) is good.

If ¬D has an instance, choose an R-minimal c in it. Every predecessor of c belongs to D. Choose the unique v with U[c,F,v], and define the patched graph by the ordinary formula

    Gxy := [(x=c)∧(y=v)] ∨ [(x≠c)∧Fxy].

This graph is functional at the current point by ordinary equality reasoning; its construction requires no operation with output τ. The property D∪{c} is downward closed. For x∈D, c is not a predecessor of x, since downward closure would give Dc. Consequently G and F agree on all predecessors of every x∈D. They also agree on all predecessors of c, since those lie in D and c∉D. Locality preserves all old equations and supplies the new equation at c. Therefore (D∪{c},G) is good, contradicting ¬Dc. Thus D is universal and F is a solution.

The same least-disagreement argument applied to two full solutions proves current coextension. Every set and patched history in this proof is an admitted λ-defined relational graph. No optional premise is passed through Logical Equivalence to produce intensional identity, no graph is silently converted to an operation, and no operation with output e appears. □

### 17.3. Nondeterministic graph recursion: safe bounds

Replace the unique-output condition by ∀xG(Fun(G)→∃y U[x,G,y]), and ask only for a solution. Call the resulting schema GWFDC. Its empty-order case implies Relational Choice: for any serial V:στt put U[x,G,y]:=Vxy. A solution is precisely a total single-valued subrelation of V.

Transversal Choice implies GWFDC. Here are the details, since choosing independently for intensional history codes would not preserve locality. Code (x,G) by its tuple haecceity H(x,G):=λuv(u=x∧v=G), of type λ:=σκt. Let Code(c) mean c=H(x,G) for some functional G. On λ put

    E(c,d):=(c=d)∨∃xGH[Fun(G)∧Fun(H)∧c=H(x,G)
               ∧d=H(x,H)∧Agree_R(x,G,H)].

The haecceity injection and equivalence of predecessor agreement show E is an actual equivalence relation. Noncodes are singleton classes. Transversal Choice yields a predicate T meeting each E-class exactly once. Define Rep(c,d):=E(c,d)∧Td; it is a functional graph on codes, and equivalent inputs have the same representative as an entity.

Transversal Choice also implies Relational Choice by the recorded theorem. Apply the latter to the serial relation V(c,y) which, for a representative valid code c=H(x,G), permits exactly U[x,G,y], and otherwise permits y=d₀ for a fixed default d₀:τ. Seriality follows from that of U and uniqueness of the code's x,G. Obtain a functional selection graph K(c,y) below V.

Now define U′[x,G,y]:=∃d(Rep(H(x,G),d)∧Kdy). For functional G this has a unique output. Histories agreeing on predecessors have E-equivalent codes, hence the same representative and the same selected output. Thus U′ is local. The representative is itself a valid code H(x,H) whose history agrees with G on predecessors, so every U′ output is a U output by the original locality. The deterministic graph theorem supplies the required solution.

Therefore the safe implications are

    Transversal Choice ⇒ GWFDC ⇒ Relational Choice.

No claim is made that either reverse implication holds over bare C. In particular the database record Relational Choice⇒Transversal Choice is **conjectured**, with a known intensional-coextension gap; it is not used as evidence. With Plenitude added, Relational Choice gives Functional Choice, whose operation recursion theorem and conversion to graphs also imply GWFDC. The distinction between these bounds is left explicit rather than being collapsed into an unsupported equivalence.

## 18. One propositional evaluation sentence axiomatizes boxed Plenitude

This is a simplification of a schema to one closed pure sentence; it does not extend the language or change the base C. Let

    Eval(b) := ∀p^t[(p→bp=⊤)∧(¬p→bp=⊥)],  b:tt,
    BTR := ∃b^{tt} Eval(b).

Thus b represents the actual two-valued truth evaluation internally, with the outputs being the designated proposition intensions ⊤ and ⊥. The acronym is only a label in this note. The explicit formula, not the label, is the proposed perspicuous formulation.

### 18.1. Exact local strength

Over C,

    BTR ↔ (ND + Actuality).

On the right, ND can equally be replaced by its type-t instance, since the proved records give ND_t⇒5⇒B⇒ND at every admitted type.

**BTR⇒ND.** Fix a witness b. For any type σ and distinct x,y:σ, the admitted operation f:=λz^σ.b(z=x) satisfies fx=⊤ and fy=⊥. This follows from Eval(b) at the true proposition x=x and the false proposition y=x. The necessity of both output identities prevents x,y from possibly coinciding; equivalently use §10's two-point interpolation argument. Hence ND_σ. Since σ was an arbitrary fixed admitted type, one BTR sentence implies the whole ND schema.

**BTR⇒Actuality.** Put Zp:=¬bp∨p. If p is true, bp=⊤ and therefore Zp=p as an intensional identity, by the Boolean identities. If p is false, bp=⊥ and Zp=⊤. Consequently w:=∀p Zp is true. C's necessary universal-instantiation theorem gives w≤Zp for every p. For each currently true p, substitute the identity Zp=p to get w≤p. Thus w witnesses Actuality. No BF is used: only instantiation of the universal proposition w, not a passage from universally many necessary premises to a necessary universal conclusion.

**ND+Actuality⇒BTR.** Let w be true and entail every currently true proposition. Define bp:=(w≤p). Since w is true, w≤p implies p. Conversely every true p is entailed by w. Thus bp↔p holds currently. The proposition w≤p is an algebraic identity, namely w∨p=p. NI and ND make every such identity proposition equal to ⊤ if true and ⊥ if false. Hence Eval(b).

This proves the equivalence. It also proves that Eval(b) automatically makes b an idempotent Boolean homomorphism with image {⊥,⊤}: each equation b⊤=⊤, b⊥=⊥, b(bp)=bp, b(¬p)=¬bp and b(p∧q)=bp∧bq follows by splitting the finitely many current truth cases and substituting the designated output identities. These are algebraic identities, not merely material equivalences.

The local principle is strictly weaker than full Plenitude in the supplied model records. The proved-only Engine reports that `finite-support-sections-and-projection` satisfies ND and Actuality but violates Plenitude. Its direct P counterinstance has input e and output t; this note makes no separate claim about the model's type-(t,t) Plenitude instance. See the model's 16 October 2026 argument and its cited write-up. The source construction and this new equivalence are separate pieces of evidence.

### 18.2. Exact boxed strength

Over C,

    □BTR ↔ □Plenitude.

For the forward direction, necessitate the discharged finite proofs in §18.1. For every fixed σ, □BTR gives □ND_σ, and it gives □Actuality. Thus C5 and □Actuality hold. The recorded Proposition 2.6 consequence `c5-and-necessary-actuality-imply-atomicity` gives Atomicity, and `c5-and-atomicity-imply-necessary-plenitude` gives □Plenitude. All type instances used in each target derivation are finite; no object-language quantification over types or rule necessitating an optional premise is introduced.

Conversely the type-(t,t) Plenitude instance realizes the total single-valued graph

    U(p,q):=(p∧q=⊤)∨(¬p∧q=⊥),

and its realizing operation witnesses BTR. Necessitate that discharged C theorem and apply K. In particular **□Plenitude at input t and output t alone already implies the full boxed Plenitude schema** through BTR. This conclusion is about the boxed principle; the local separating model above prevents conflating BTR with full unboxed Plenitude.

Therefore BP can be presented by the single closed sentence

    □∃b^{tt}∀p^t[(p→bp=⊤)∧(¬p→bp=⊥)].

It says that every world has an internal operator representing its own truth evaluation in the two designated truth values. In full S5 models the witness at a world w sends a proposition intension p to the constant true proposition if w∈p and to the constant false proposition otherwise. The witnesses can differ between worlds.

### 18.3. Moving the existential across the box changes the theory exactly

Define UTR:=∃b^{tt}□Eval(b), where the same b must classify truth correctly throughout the modal range. Then

    C ⊢ UTR ↔ Fregean Axiom.

Suppose □Eval(b). If p is actually true, Eval(b) gives bp=⊤, and NI makes that identity necessary. At every accessible world the classifier clause ¬p→bp=⊥ therefore rules out ¬p. Thus □p and p=⊤. If p is actually false, the symmetric argument gives □¬p and p=⊥. Every proposition is thus one of the two designated truth values according to its current truth, and materially equivalent propositions are identical: the Fregean Axiom.

Conversely the recorded theorem `fregean-axiom-implies-necessary-fregean-axiom` supplies □Fregean Axiom. At each world the identity operation b:=λp.p then satisfies Eval(b), since every true proposition is ⊤ and every false proposition is ⊥. Equivalently necessitate the C theorem Fregean→Eval(id), and apply K. Hence □Eval(id), proving UTR.

This isolates the modal scope exactly. The single boxed-existence sentence in §18.2 retains arbitrary modal richness in its full S5 models. Requiring one chosen evaluator to be correct necessarily yields extensional collapse. No intuition about a fixed actual-world operator is substituted for the displayed quantifier order.

### 18.4. Recorded inputs and attribution

The BTR formulation and the arguments above are new deductions in this research note; no literature novelty is claimed. Recorded inputs are the definitions of Actuality, Plenitude and the Fregean Axiom; the C theorems NI, Modalized Functionality and normal modal logic; and the proved results `distinctness-necessary-t-implies-modal-five`, `modal-five-implies-modal-b`, `modal-b-implies-distinctness-necessary-r`, `c5-and-necessary-actuality-imply-atomicity`, `c5-and-atomicity-imply-necessary-plenitude`, and `fregean-axiom-implies-necessary-fregean-axiom`. Classicism locators for the middle implications are Proposition 2.2, p.22; Proposition 2.6, pp.25–26; and §2.3 concluding equivalences, p.33, in the 16 May 2023 draft. All proofs remain ordinary mathematical proofs, without a new Lean-verification claim.

## 19. Bare-C structure of hereditary rigidity

### 19.1. Finite joins and internally finite comprehension

C proves that a finite join of rigid relations is rigid. For a binary join Y∨Z, persistence follows from persistence of Y and Z and finite propositional reasoning. At any world, if every current instance of Y∨Z necessarily satisfies H, then every Y-instance and every Z-instance necessarily satisfies H. Their inextensibility gives Y≤H and Z≤H, hence Y∨Z≤H. The rigid hypotheses are necessary: persistence is an algebraic identity and hence obeys NI, while inextensibility carries a leading box and obeys 4. Necessitating the discharged local argument therefore gives the globally boxed inextensibility clause for the join. Bottom is rigid, so all fixed finite joins follow. The database already mentions finite joins of haecceities as rigid; the argument here makes the general binary closure explicit.

This gives **finite rigid comprehension in bare C, with genuine impredicative Frege finiteness**:

    Fin_σ(X) → ∃!Y^{σt}[Rigid(Y)∧∀x(Xx↔Yx)].

Here Fin_σ(X):=∃n(N_σn∧nX), not a schema of externally fixed finite sizes. Induct on n with the property W(n):=∀X[nX→∃Y(Rigid(Y)∧Coext(X,Y))]. If 0X, X is empty and bottom is the witness. If (Suc n)X, choose its displayed individual-or-relational witness a with Xa and n(X−a). By induction X−a has a rigid coextension Y. Then Y∨H_a is rigid by binary-join closure and is currently coextensive with X. This closes the induction. Uniqueness is §12.1. No uniform operation selecting these representatives is asserted; existence and uniqueness of a relational representative are the whole conclusion.

### 19.2. Core membership persists already in C

C proves Core_σ(x)→□Core_σ(x) for every fixed admitted type σ, and hence Persistent(Core_σ). This is weaker than the C5 result that the core predicate itself is rigid: in C the predicate may gain new instances.

Induct on the type syntax. Core_e is constantly true, hence persistent. Suppose all argument-core predicates are persistent, and set S[x̄]:=∧_i Core_{σ_i}(x_i). Finite conjunction preserves persistence. If Core_{σ̄t}(Y), then Y is rigid and currently supported on S. Every current Y-instance therefore satisfies S and, by its persistence, necessarily satisfies S. Inextensibility of Y gives Y≤S, which is exactly □∀x̄(Y[x̄]→S[x̄]). Rigidity of Y is itself necessary, as noted above. These two boxed conclusions give □Core_{σ̄t}(Y). The implication has been proved as a C theorem with Y free; universal closure and necessitation give the background's global persistence condition on Core_{σ̄t}.

Thus the actual-support definition in §11 is equivalent already in C to its boxed-support version, conditional on the displayed rigidity of Y. Earlier proofs used only the actual support clauses; they remain valid. The equivalence is now justified by inextensibility, not by simply assuming that current support may be necessitated.

This explains an exact distinction between the base and C5 pictures. Under bare C a core object remains in the core at all accessible worlds, but further core objects may appear. Under C5 persistence implies rigidity, and §15 identifies the core's membership as settled in both directions. Strong Possibility's finite current cores therefore do not imply that the accessible worlds have the same finite cores.

### 19.3. Union of a rigid family of rigid relations

Let F have type (σ̄t)t. Assume Rigid(F) and ∀Y(FY→Rigid(Y)). Define

    U[x̄]:=∃Y(FY∧Y[x̄]).

Then C proves Rigid(U).

First the support condition on F is necessary. The predicate Rigid(Y) is persistent in C. So each current F-instance necessarily satisfies it, and inextensibility of F gives F≤Rigid. At every world, therefore, every F-instance is rigid. Persistence of U follows by retaining its witness Y and using persistence of F and Y.

For inextensibility, reason at an arbitrary world and assume every U-instance necessarily satisfies Z. For each FY, every Y-instance then necessarily satisfies Z, and inextensibility of Y gives Y≤Z. The predicate Q(Y):=(Y≤Z) is persistent, being an algebraic identity. Thus each current F-instance necessarily satisfies Q. Inextensibility of F gives F≤Q. At every accessible world, an instance of U has a witness Y with FY and Y[x̄]; F≤Q gives Y≤Z, and hence Z[x̄]. Therefore U≤Z. Discharging and necessitating gives the required global inextensibility, with all source hypotheses available necessarily as just shown.

If F is in Core_{(σ̄t)t}, then its members are core relations and the same union U is in Core_{σ̄t}: support on the lower cores follows immediately from the chosen member relation's support. Thus hereditary rigid cores have this union closure already in C. This does not assert closure under arbitrary intersections or complements in C.

### 19.4. The smallest intersection obstruction is exactly ND

For each fixed σ let

    SIC_σ := ∀a,b^σ Rigid(λx^σ.(x=a∧x=b)).

Then C proves SIC_σ↔ND_σ. If a=b, the displayed intersection is a haecceity and rigid. If a≠b and ND_σ holds, □(a≠b) makes the intersection necessarily empty, hence identical to bottom and rigid. Conversely, for actually distinct a,b the intersection is currently empty. SIC makes it rigid, so rigid coextensionality with bottom (§12.1) makes it bottom as an intension. If a and b could coincide, that intersection could have an instance, contradicting its identity with bottom. Hence □(a≠b).

At σ=t this is a single closed sentence and, by the recorded ND_t⇒ND equivalence, it is equivalent to the full ND schema. Its boxed version is equivalent to C5. Full binary-intersection closure of arbitrary rigid relations is stronger than this singleton-intersection condition; C5 proves it because under C5 persistence alone implies rigidity and conjunction preserves persistence. This note does not identify the exact unboxed strength of that larger closure principle.

Max supplies a concrete failure of singleton-intersection closure. Let m:=∀x^e y^e(x=y), as in §10. Then m≠⊤ but ◇(m=⊤). The rigid haecceities H_m and H_⊤ have an actually empty intersection which is possibly inhabited. Their intersection is therefore not rigid. The failure concerns rigid sets of possibly coinciding proposition intensions; it does not show that the hereditary core's finite current set algebra under monism is inconsistent.

## 20. A worked analysis consequence: core Dedekind completeness

This makes the extensional-core interpretation concrete without identifying Henkin comprehension with external fullness. Work in C5. Let Q:σt be core and let <:σσt be core, and suppose their current restrictions make Q a dense strict linear order without endpoints. The following cut construction uses only the same admitted relational types. Its completeness proof in fact does not need density; density and absence of endpoints are the usual hypotheses when treating these cuts as an order completion.

Let Cut(X), for X:σt, be the conjunction of:

1. Core_{σt}(X), and ∀x(Xx→Qx);
2. ∃xXx, and ∃x(Qx∧¬Xx);
3. ∀xy[(Qx∧Qy∧x<y∧Xy)→Xx];
4. ∀x[Xx→∃y(Xy∧x<y)].

Thus X is a nonempty proper lower cut with no greatest member. Cut is itself a core predicate of type (σt)t. For a noncore X its first conjunct is settled false. For a core X, every membership in X,Q and < is settled; the Boolean/BF induction of §15 makes all four clauses settled. The predicate is therefore pointwise bivalent and supported on Core_{σt}, so §15.1 makes it core.

**Core least-upper-bound theorem.** Let F:(σt)t be core, nonempty, supported on Cut, and have an upper bound Y satisfying Cut(Y), where upper bound means

    ∀X(FX→∀x(Xx→Yx)).

Then there is a unique cut U which is the least upper bound of F under current inclusion. It is explicitly

    Ux := ∃X(FX∧Xx).

Core membership of U follows from the bare-C rigid-family union theorem §19.3. A witness X∈F and an element of X make U nonempty. Since U⊆Y and Y is proper in Q, U is proper in Q. Every U-instance comes from a member cut, giving support on Q, downward closure, and a strictly larger member of the same cut; hence no greatest member. Thus Cut(U). Each X∈F is included in U by existential introduction. If Z is any other upper bound, then every witnessing X is included in Z, so U⊆Z. Uniqueness follows from mutual inclusion and rigid coextensionality (§12.1).

All of this is ordinary current relational reasoning except the explicitly identified rigidity proof. No Choice, Atomicity, Boolean Completeness, or Plenitude is used. Because the quantifiers and parameters in the resulting ordered-cut structure are core-restricted, its pure mathematical formulas are also modally stable by §15.4.

Under BP, the conclusion additionally applies to **every admitted ambient family** F of core cuts, whether F itself is core: first use §15.5 to take its unique core coextension, then apply the union construction. In full S5 models the core domains are externally full, so this is the ordinary full cut completion. In an arbitrary Henkin model, completeness quantifies over the family properties admitted by the indicated interpretation; no external completeness or standardness claim is made.

The independently audited Frege/core bridge in the companion Frege note, §16.1, shows that C5 transfers genuine Infinity_e exactly to its extensional core, with a bijection of number domains when Infinity_e holds. Together with the core interpretation, this supplies the standard arena for arithmetic and the cut construction. It does not assert Infinity_e without that optional axiom, and does not identify the propositional Infinity axiom with individual infinity.

## 21. Rigidity of the universe and of the singleton collection

For any admitted σ define h_x:=λz^σ(z=x) and

    Sng_σ(Y):=∃x^σ(Y=h_x),  Y:σt.

Then, already in C,

    Rigid(Sng_σ) ↔ Rigid(⊤_{σt}) ↔ □BF_σ.

The second equivalence is a direct expansion of the official definition. The universal property is persistent in C. Its inextensibility says exactly

    □∀X^{σt}[(∀x^σ□Xx)→□∀x^σXx],

which is □BF_σ. This equivalence is also used in the existing finite-support-model write-ups; it is not claimed as a new recorded implication.

Every Sng_σ-instance is a rigid haecceity, by the C theorem. Its union in the sense of §19.3 is ⊤_{σt}: every x belongs to h_x, and every haecceity-instance is an individual-or-relational entity of type σ. The equality of this union with ⊤ follows from H-provable equivalence, without optional hypotheses. Thus Rigid(Sng_σ) and rigid-family union imply Rigid(⊤_{σt}).

Conversely suppose □BF_σ. Sng_σ is persistent in C: any witness to Y=h_x remains a witness by NI. For inextensibility reason at an arbitrary world and suppose ∀Y(Sng_σ(Y)→□ZY). In particular ∀x□Z(h_x). BF_σ gives □∀x Z(h_x). The C theorem ∀x Z(h_x)→∀Y(Sng_σ(Y)→ZY), necessitated and combined with K, gives Sng_σ≤Z. Since BF_σ holds throughout the modal range, the discharged argument supplies globally boxed inextensibility. Thus Sng_σ is rigid. No BF at the higher type σt is needed.

This formulation identifies an exact set-like reading of □BF: the universal domain, equivalently the collection of all its singletons, is rigid. The bare-C universe is always persistent; its inextensibility is the additional content.

### 21.1. Consequence for ordinary Maximalism

For every fixed σ, ¬BF_σ is consistent with C. At e the recorded finite-support sections-and-projection model supplies failure directly. At t its later proved argument `barcan-t` supplies failure. For a general relational σ, C proves BF_σ→BF_t: choose a tuple of arguments ā for σ=ρ̄t, set i(p):=λz̄.p and r(Y):=Y[ā], and note r(i(p))=p. Given ∀p□Xp, universally many Y satisfy □X(rY); BF_σ yields □∀Y X(rY), which implies □∀pXp by instantiation at i(p). All types are inhabited, and the empty tuple handles σ=t. Thus the same BF_t countermodel refutes BF_σ for every relational σ.

The pure modal-free-or-modal sentence ¬BF_σ is therefore C-consistent at each fixed σ, so Max gives ◇¬BF_σ. Hence it refutes □BF_σ, and by the equivalence above

    Max ⊢ ¬Rigid(⊤_{σt}) ∧ ¬Rigid(Sng_σ).

This is a family of fixed-type consequences, not object-language type quantification. It does not assert ¬BF_σ itself from ordinary Max. The parent lane's stronger unboxed failures under Strong Possibility have separate proofs.

In particular Core_e is the universal individual property and so is not rigid under ordinary Max, although it is persistent by §19.2. This gives an exact counterexample to transferring the C5 claim that every core predicate is rigid down to bare C or Max.

## 22. Rigid comprehension as arbitrary-family union

Fix a relational type τ=σ̄t, including the nullary case. For F:τt write FamRig(F):=∀Y(FY→Rigid(Y)). Consider the following principle:

    RU_τ: ∀F [FamRig(F) → ∃U^τ(Rigid(U) ∧
                ∀x̄(U[x̄]↔∃Y(FY∧Y[x̄]))))].

It says that every admitted family of rigid relations has a rigid current union. F need not itself be rigid. Over C, RU_τ is equivalent to Rigid Comprehension at τ.

RC⇒RU is immediate by applying RC to the ordinary λ-union of F. Conversely, for arbitrary X:τ define the tuple haecceity H_ā:=λx̄(x̄=ā), and set

    F_X(Y):=∃ā(X[ā]∧Y=H_ā).

Every member of F_X is rigid, by the C theorem on tuple haecceities. Its current union is coextensive with X: an X-instance x̄ has witness H_x̄, and a union-instance has a witness ā with X[ā] and x̄=ā. RU therefore supplies a rigid coextension of X. For the empty tuple, take H_():=⊤ and F_X(Y):=X∧Y=⊤; the same argument applies. It is already sufficient to require RU only for families consisting of haecceities.

The supplied U is unique by rigid coextensionality (§12.1). Moreover U is the least upper bound, in Boolean entailment order, of the currently selected members of F. If FY, current inclusion Y⊆U and persistence of U give ∀x̄(Y[x̄]→□U[x̄]); inextensibility of Y gives Y≤U. If every current F-member entails Z, then every current U-instance has a witness Y with Y[x̄] and Y≤Z. Persistence of Y, together with NI for Y≤Z, gives □Z[x̄]. Inextensibility of U yields U≤Z. Thus no current-family rigidity hypothesis is needed for this least-upper-bound conclusion once a rigid current union has been supplied. The converse, that an arbitrary algebraic least upper bound must have precisely the current union extension, is not asserted.

This sharpens §19.3 without conflating its two formulations. Bare C proves that the literal λ-union of a **rigid family** of rigid relations is rigid. RC says that an **arbitrary admitted family** of rigid relations has some rigid relation with its current union extension. The two candidate union relations can be distinct intensions.

### 22.1. Requiring the literal union to be rigid collapses the theory

Let LRU_τ instead require Rigid(λx̄.∃Y(FY∧Y[x̄])) for every F satisfying FamRig(F). At any fixed relational type τ, this stronger principle is equivalent over C to the Fregean Axiom.

For the family F_X above, the literal λ-union is **identical** to X, not merely currently coextensive. Indeed the equivalence

    ∃Y ā(X[ā]∧Y=H_ā∧Y[x̄]) ↔ X[x̄]

is a theorem of H with X and x̄ free; universal closure, necessitation, and Modalized Functionality give the identity of the corresponding relation terms. Hence LRU_τ makes every X:τ rigid.

Take X to be the constant relation λx̄.p. All argument types are inhabited. If p is true, persistence of X gives □p, and hence p=⊤. If p is false, X is currently empty, so rigid coextensionality with bottom gives X=⊥_τ, and evaluation gives p=⊥. Thus every proposition is ⊤ or ⊥ according to its current truth, which is the Fregean Axiom. The nullary case is identical without dummy arguments.

Conversely the Fregean Axiom implies its necessary form and Extensionality, by the recorded C theorems. Every proposition is then settled. Each relation is persistent, and the local inextensibility implication follows because its antecedent gives current inclusion, which the Fregean Axiom turns into necessary inclusion. Necessitating the discharged argument using the necessary Fregean Axiom supplies the official global rigidity clauses. Thus every relation, in particular every literal union, is rigid.

Accordingly the modest phrase “has a rigid current union” is mathematically essential. Replacing it by “its union intension is rigid” changes RC into extensional collapse. No choice or operation selecting the rigid representative is part of RU.

## 23. Exact identity versus value uniqueness in recursion

The uniqueness clauses distinguish three different theories. Let DWR^= be §2's operation recursion principle with conclusion ∃!f Sol(U,f), where uniqueness means identity of the operation. Let GDWR^= be §17's graph recursion principle with identity of the graph, rather than uniqueness up to current coextension.

### 23.1. Operation identity uniqueness

Over C, as full admitted-type schemas,

    DWR^= ↔ Plenitude + Functionality.

The forward implication to Plenitude is the same empty-dependency reduction as §3.1. To obtain Functionality, fix arbitrary operations f,g:στ with ∀x fx=gx. Use empty R and U(x,h,y):=(y=fx), ignoring the history h. Both f and g are solutions; identity uniqueness gives f=g. Conversely Plenitude gives a solution and pointwise uniqueness by §3. Functionality converts the latter into identity uniqueness. No equality of histories is required for locality, which continues to mean equality of values on predecessors.

Since BF and Functionality are equivalent by the recorded theorems, one may equally write Plenitude+BF. On boxing the closed instances, the added boxed Functionality follows already from □Plenitude, so □DWR^= is equivalent simply to □Plenitude. This boxed equivalence does not permit dropping Functionality from the displayed unboxed equivalence.

### 23.2. Graph identity uniqueness

Over C,

    GDWR^= ↔ Extensionality ↔ Fregean Axiom.

Extensionality converts the coextension uniqueness in the C graph-recursion theorem §17 into graph identity. For the converse, remarkably the empty-dependency instance with input e and output t already suffices. Given materially equivalent propositions p,q, define functional graphs

    G_p(x,r):=(p∧r=⊤)∨(¬p∧r=⊥),
    G_q(x,r):=(q∧r=⊤)∨(¬q∧r=⊥).

Each is a total single-valued graph currently, and p↔q makes them currently coextensive. Let U(x,H,r):=G_p(x,r), independent of the graph history H, and take empty R. Both G_p and G_q are solutions in §17's graph sense, so GDWR^= gives G_p=G_q. Choose any individual a. Applying both graphs at (a,⊤) gives p=q, because C proves the intensional identities G_p(a,⊤)=p and G_q(a,⊤)=q by Boolean identities and ⊤≠⊥. This is the Fregean Axiom. Its implication to full Extensionality is the recorded theorem `fregean-axiom-implies-extensionality-r`.

Thus the hierarchy of recursion statements is exact:

* deterministic graph recursion, with graph uniqueness up to current coextension, is already a theorem of C;
* deterministic operation recursion, with uniqueness of all values, is equivalent to Plenitude;
* identity uniqueness of those operations adds precisely Functionality;
* identity uniqueness of the graph witnesses entails extensional collapse, already in one very small instance.

These are not competing proofs of one ambiguous “unique recursion” claim. They specify different equality notions in a setting where current agreement and identity are distinct. In full S5 models with several worlds, □Plenitude validates identity uniqueness of operation solutions, while graph solutions can be different intensions with the same current graph, so GDWR^= fails.

## 24. Relative cores and strict rigid-power towers

The primitive core in §§11–15 is not the only ordinary mathematical domain available inside the theory. The same construction can start from a rigid inhabited property of any admitted ambient type. This matters when the individuals are monistic but the propositional domain is infinite.

### 24.1. A relative extensional interpretation under C5

Work in C5. Fix an admitted ambient type α and a rigid nonempty property K:αt. Interpret a new base sort by the K-members, with actual identity inherited from α. Translate the relational type language recursively by sending its base individual type to α, its proposition type to t, and its relational arrows to the corresponding admitted ambient relational arrows. There is no new ambient operation with output e.

Define relative-core domain predicates L_s at each translated type by

    L_e(x):=Kx,
    L_{s₁…s_nt}(Y):=Rigid(Y) ∧
        ∀x̄(Y[x̄]→∧ᵢ L_{sᵢ}(xᵢ)).

The empty-tuple clause gives L_t={⊥,⊤}. The proof of §15 applies verbatim with the bivalent predicate K in place of the constantly true primitive individual core. At each step, the lower domain predicates are bivalent; rigidity and support are settled by the identity/BF argument; hence every L_s is itself rigid. Application preserves the domains, guarded abstraction produces admitted relative-core relations, restricted quantifiers have relative-core representatives, and current coextensionality of relative-core relations is identity. The result is an internal interpretation of the same ordinary extensional relational Henkin higher-order logic with base domain K. It is not an external full-powerset assertion.

More explicitly, a translated abstraction with a bound base variable x is guarded by Kx, and a translated abstraction with a higher variable x:s is guarded by L_s(x). Thus values at arguments outside the interpreted domain are bottom. On interpreted arguments every atomic membership and identity proposition is bivalent. Boolean operations and quantifiers preserve this property under BF, proving by formula induction that every formula of the interpreted language is settled for interpreted parameters. The assumption Rigid(K) is part of the displayed domain specification, not an unproved conclusion for an arbitrary ambient property.

### 24.2. The numerical base

Let ν_σ=(σt)t and K=N_σ, the admitted property of Frege finite cardinalities. C proves persistence of N_σ, and C5 makes it rigid. It is inhabited by zero. Consequently §24.1 supplies a relative extensional core based on N_σ already in C5.

Add Infinity_σ. The audited companion Frege note, §20, proves in C5 that this is equivalent to I*_σ, successor injectivity, and realization of every numerical cardinality. The base N_σ therefore has the Peano successor structure with zero, injective successor, zero not a successor, and induction for every admitted property, hence for every relative-core property. The successor graph restricted to N_σ is itself relative-core: its membership is a conjunction of settled numberhood and the settled identity m=Suc(n). Ordinary graph recursion and arithmetic constructions can be carried out within the interpreted extensional higher-order logic. Its usual impredicative set constructions, including the cut completion in §20, then apply to this numerical base. This is ordinary internal Henkin mathematics; full external standardness is asserted only in the full models below.

Under BP there is a stronger parameter theorem. Every N_σ-member is fixed by every atom-swap conjugation, by the zero/successor induction in the companion Frege note, §2. If all members of a base property K are fixed by a given conjugation, then every rigid relation supported on K (or on finite products of already fixed relative-core domains) is fixed as in §11: support makes any relevant transformed argument fixed, rigid membership is bivalent, the Boolean swap fixes both designated values, and Functionality identifies the transformed relation. Induction on translated type therefore fixes every relative-core object based on N_σ. The atom-swap proof consequently makes **arbitrary pure ambient formulas**, including unrestricted ambient higher quantifiers, absolute when all their free parameters belong to this numerical relative core. This last extension uses BP; §24.1's core-restricted formula stability needs only C5.

### 24.3. Cantor's argument for rigid powers, with exact comprehension strength

For any admitted property K:αt, not initially assumed rigid, define its rigid power by

    RP_K(Y):=Rigid(Y)∧∀x(Yx→Kx),  Y:αt.

C proves that x↦H_x gives an injective graph from K into RP_K. If Kx, then H_x is rigid and supported on K; the haecceity coding lemma gives injectivity. Bottom is always an RP_K-member.

Assume RC at αt. There is no admitted total functional graph R from K onto RP_K. For suppose R were one, and form

    D(x):=Kx∧∃Y(RP_K(Y)∧R(x,Y)∧¬Yx).

RC supplies a rigid E currently coextensive with D. Since D⊆K, E belongs to RP_K. Surjectivity gives a∈K with R(a,E). At a, functionality identifies every R-output in RP_K with E, and hence

    Ea ↔ Da ↔ ¬Ea,

a contradiction. No selection operation is introduced, and neither Choice nor Plenitude is needed. C+RC is sufficient for this conclusion about arbitrary admitted graph maps; C5 and Atomicity are not used in this diagonal step.

There is also no admitted injective graph J from RP_K into K. If such a graph existed, define its inverse on its range and give every remaining K-element the default value bottom:

    S(x,Y):=Kx∧RP_K(Y)∧
      [J(Y,x) ∨ (¬∃Z(RP_K(Z)∧J(Z,x)) ∧ Y=⊥_{αt})].

Injectivity of J makes S functional, its totality on RP_K makes S surjective onto RP_K, and the default clause makes S total on K. This contradicts the preceding diagonal. The argument is purely relational and does not invoke Cantor–Bernstein, Choice, or a forbidden individual-valued operation.

Under C5 alone, the same conclusions hold for **rigid graph maps** whenever K is rigid. Then RP_K is rigid by the relative-core proof. If R is rigid, every factor defining D is settled: K and RP_K memberships are settled, R-membership is settled, and the RP_K guard makes Yx settled whenever relevant. BF handles the existential quantifier. Thus D itself is rigid and may be used as E, without RC. Similarly the inverse/default graph S of a rigid J is rigid, by bivalence of the displayed factors and BF. The singleton injection graph is also rigid. These are the Cantor statements inside the relative extensional interpretation; they must not be promoted to arbitrary ambient graphs without the RC step.

### 24.4. A strict hierarchy based on numbers

Put α₀:=ν_σ, K₀:=N_σ, αᵢ₊₁:=αᵢt, and Kᵢ₊₁:=RP_{Kᵢ}, for each externally fixed finite i. C5 makes every Kᵢ rigid. At each successive level there is a canonical rigid singleton injection Kᵢ→Kᵢ₊₁, no rigid surjection Kᵢ→Kᵢ₊₁, and no rigid injection in the reverse direction. BP already entails □RC, so BP alone upgrades the two impossibility claims to arbitrary admitted graph maps. Thus BP supplies a strict internal relational cardinal hierarchy above its numerical domain. These are graph comparison statements at specified admitted types, not an object-language quantification over all types and not an assertion that an arbitrary Henkin model has full external powersets.

If Infinity_σ holds, the base carries the infinite Peano structure just described. In a full S5 model, the numerical domain is the standard natural numbers, and its rigid powers are the full ordinary powersets; the external cardinalities of these levels are consequently ℵ₀, 2^ℵ₀, 2^(2^ℵ₀), and so on. This external cardinal description is confined to that full-model verification.

### 24.5. Monism is compatible with the positive package's numerical analysis

Take the full S5 construction in ZFC with the individual domain D={d} and any infinite world set W. It satisfies □Functional Choice. Its proposition domain P(W) is infinite, so Infinity_t holds; its individual domain remains monistic, so Infinity_e fails. The primitive hereditary e-core of §§11–15 has finite domains at every fixed type. Nevertheless the **numerical** relative core based on N_t is infinite and externally full at its successive powers, as just shown. Thus the same model contains the ordinary full arithmetic and analysis based on this relative core.

This is an exact consistency example for □Functional Choice + individual monism + Infinity_t + numerical-core richness. It is not a Strong Possibility model: BP already contradicts Max, and therefore SP. It does show why primitive individual monism, or finiteness of the primitive e-core, cannot by itself establish that no ordinary infinite mathematics can be interpreted. The relevant additional obstruction under Max is the failure of stable collection and comprehension principles, not monism alone.

For the numerical base specifically, the companion Frege note §12 identifies local weak inextensibility of N_σ with Numerical Collection. Since persistence of N_σ is a C theorem, its official rigidity is equivalently the boxed local Numerical Collection condition. The companion note's Maximalist failure of Numerical Collection therefore prevents treating N_σ as a rigid base under Max. This last comparison uses that separately established arithmetic theorem, not a new claim that every persistent base is rigid in C.

The C5 rigidity of these power domains is consistent with, and at a single step is an instance of, the existing result `c5-implies-necessary-rigid-power`. When K is rigid, the actual support condition Y⊆K for a rigid Y is equivalent in C to Y≤K by §19.2's inextensibility argument. Thus RP_K agrees with the recorded Rigid Power construction. The new material here is the relative interpretation, its numerical starting domain, and the explicitly separated Cantor comparisons; the previously recorded Rigid Power implication is not being claimed as a new discovery.

## 25. Rigidity of equality, inequality, and complements

These exact equivalences give a set-theoretic reading of C5 without changing its logical strength. All displayed ND_σ and BF_σ are the standard fixed-type instances, and all boxes apply to their universal closures.

### 25.1. Equality is rigid exactly when boxed BF holds

For I_σ(x,y):=(x=y), C proves

    Rigid(I_σ) ↔ □BF_σ.

Persistence of I_σ is NI and is a C theorem. Its local weak-inextensibility condition is

    ∀Z^{σσt}[(∀xy(x=y→□Z(x,y)))→□∀xy(x=y→Z(x,y))].

BF_σ implies this: the premise gives ∀x□Z(x,x), BF gives □∀x Z(x,x), and necessary identity substitution gives the conclusion. Conversely, instantiate Z(x,y):=Px for arbitrary P:σt. The premise follows from ∀x□Px, while the conclusion entails □∀xPx by setting y=x. Thus weak inextensibility of I_σ is equivalent to BF_σ. Necessitate the two discharged implications and use persistence to obtain the displayed boxed equivalence. No BF over the pair type or higher predicate type is used.

Combining §21 gives, in C,

    Rigid(I_σ) ↔ Rigid(⊤_{σt}) ↔ Rigid(Sng_σ) ↔ □BF_σ.

Necessary identities alone therefore do not make the equality relation rigid: its inextensibility is precisely the separate collection principle BF.

### 25.2. Complement closure at a fixed type

Define

    CompRig_σ := ∀X^{σt}(Rigid(X)→Rigid(¬X)).

Then C proves

    CompRig_σ ↔ (□ND_σ ∧ □BF_σ).

For the forward implication, bottom is rigid and its complement is the universal property. So CompRig_σ gives Rigid(⊤_{σt}), equivalently □BF_σ. Each haecceity H_a is rigid; hence its complement λx(x≠a) is rigid and therefore persistent. Thus

    ∀a □∀x(x≠a→□(x≠a)).

The now available BF_σ moves the outer ∀a through the box and gives □ND_σ. This use of BF is explicit; mere pointwise persistence of all complements has not silently been universally boxed.

For the converse, the C argument in §11.2 shows that ND_σ makes every membership of a rigid X either ⊤ or ⊥. Its complement is likewise pointwise bivalent. At a world with BF_σ, any pointwise bivalent property is weakly rigid by §15.1's local argument: true instances are necessary, and the inextensibility antecedent makes every pointwise implication necessary, so BF yields necessary universal inclusion. This proves a discharged C implication

    ND_σ ∧ BF_σ ∧ Rigid(X) → WeaklyRigid(¬X).

The hypotheses □ND_σ and □BF_σ make the first two conjuncts necessary; Rigid(X) is itself necessary in C. Necessitate the discharged implication and apply K to obtain □WeaklyRigid(¬X), which is exactly Rigid(¬X). Hence CompRig_σ.

At σ=t, the recorded ND_t⇒ND schema and its necessitated forms make □ND_t equivalent to full C5. C5 already supplies □BF_t. Therefore the **single closed sentence**

    ∀X^{tt}(Rigid(X)→Rigid(¬X))

is equivalent over C to full C5. In words, complements of rigid sets of propositions are rigid. This is an alternative formulation, not an additional strengthening of C5.

### 25.3. A single concrete inequality relation

Let D_σ(x,y):=(x≠y). When C proves that σ has at least two necessarily distinct entities—as it does for every relational σ via its top and bottom—then

    Rigid(D_σ) ↔ (□ND_σ ∧ □BF_σ).

Persistence of D_σ is literally □ND_σ. To extract □BF_σ from its inextensibility, reason first locally. Given ∀x□Px, put Z(x,y):=Px. Weak inextensibility of D_σ yields □∀xy(x≠y→Px). C proves ∀x∃y(x≠y), using the two fixed necessarily distinct entities. The necessitated implication therefore yields □∀xPx. This proves weak inextensibility⇒BF_σ; boxing the discharged implication gives the required □BF_σ.

Conversely □ND_σ makes every inequality membership settled throughout the modal range. Applying BF_σ twice handles the two argument quantifiers in the local weak-inextensibility proof. Since □BF_σ is assumed, this holds throughout the range, proving rigidity. At σ=t we conclude

    C5 ↔ Persistent(≠_t) ↔ Rigid(≠_t) ↔ CompRig_t.

The first equivalence merely spells out □ND_t and the recorded all-type reduction; the additional rigidity and complement formulations expose its structural content. The assertion for σ=e requires the explicit two-entity assumption for the implication from inequality rigidity to BF_e; if e is monistic and its inequality relation is bottom, that implication cannot be inferred by this proof.

### 25.4. Full ambient membership has a different strength

For any admitted σ, let M_σ(X,x):=Xx, with X:σt. Then

    Persistent(M_σ) ↔ Rigid(M_σ) ↔ Fregean Axiom.

Persistence of full membership makes every true proposition necessary: for any p choose the constant predicate X:=λx.p and any a:σ, and apply persistence to M_σ(X,a). Thus p→□p for every p. Applying the same reasoning to ¬p shows every false p is bottom, so the Fregean Axiom follows. Conversely the Fregean Axiom and its necessary form make every relation rigid, as in §22.1.

This is why the relative-core membership guards in §§15 and 24 matter. The positive non-Fregean theory supplies stable membership for rigid/core sets and ordinary extensional structures on their domains. Requiring the single universal ambient membership relation to be persistent would instead force all propositions to collapse to two values.

## 26. Comprehension as graph recursion with rigid solutions

There is a complementary exact formulation using the graph recursion of §17. Use its evident finite-input-tuple form, proved by precisely the same partial-graph argument with x replaced by x̄ throughout. The output type may be e; all graphs still have relational type. The empty input tuple causes no difficulty and is unnecessary for the nontrivial implications below.

Let RGDWR say that every deterministic local rule over a strictly well-founded dependency relation has a **rigid** total functional solution graph. Uniqueness remains only current coextension. Let NRGDWR add that the solution graph is necessarily total and functional.

Then, over C as admitted-type schemas,

    RGDWR ↔ Rigid Comprehension,
    NRGDWR ↔ C5 + Rigid Comprehension
            ↔ Plenitude + Functionality.

The middle equivalence is local, not a claim that C5+RC already gives Atomicity or □Plenitude. Boxed RGDWR corresponds to □RC; C5 together with □RGDWR is equivalent to BP by the recorded RC+ND⇒Plenitude implication and its necessitation.

### 26.1. A rigid Boolean-valued graph has rigid truth columns

Suppose G(x̄,p), with p:t, is rigid and currently has outputs only ⊤ and ⊥. Its range support is necessary. Indeed every current G-instance satisfies p=⊤∨p=⊥, and this finite disjunction of identities is persistent in C; inextensibility of G gives

    G ≤ λx̄ p.(p=⊤∨p=⊥).

Put Y[x̄]:=G(x̄,⊤). Persistence of Y follows from persistence of G. To prove inextensibility, reason at any world, where G is rigid and the range support holds. Assume ∀x̄(Y[x̄]→□Z[x̄]). For every G-instance (ā,p), there are two cases. If p=⊤, the assumption gives □Z[ā]. If p=⊥, NI and ⊤≠⊥ give □(p≠⊤). Thus every current G-instance necessarily satisfies

    T(x̄,p):=(p≠⊤∨Z[x̄]).

Inextensibility of G gives G≤T. Restricting the necessary inclusion to p=⊤ gives Y≤Z. Since G's rigidity and its proved range support are necessary, the discharged argument proves global inextensibility of Y. Hence Y is rigid. No ND or BF is used: the relevant output alternatives are the two fixed necessarily distinct Boolean values, not an arbitrary possibly coalescing pair.

### 26.2. Rigid graph recursion and RC

Assume RC. The C theorem §17 first supplies an ordinary total functional solution graph F. RC supplies a rigid graph G currently coextensive with F. Current totality and functionality transfer immediately. G and F agree as histories on every predecessor set, so locality transfers the rule's output permission from F to G. Thus G is a solution, proving RGDWR. Uniqueness up to current coextension is already the C theorem.

Conversely, given arbitrary X:σ̄t, use the empty dependency relation and the history-independent rule with prescribed graph

    V_X(x̄,p):=(X[x̄]∧p=⊤)∨(¬X[x̄]∧p=⊥).

RGDWR supplies a rigid functional solution G. Since the rule is deterministic and G is total, G is currently coextensive with V_X. Its outputs are therefore Boolean. Section 26.1 gives a rigid Y[x̄]:=G(x̄,⊤), and this is currently coextensive with X. Hence RC at the displayed type. At nullary t, RC is already a C theorem by the current truth split between ⊤ and ⊥.

### 26.3. Necessary functionality adds precisely C5

Assume C5+RC. The preceding argument gives a rigid current solution G. Under C5 every membership of G is bivalent, and all identity propositions are bivalent. The statement that G is total and single-valued is built from these memberships, identities, Boolean connectives and quantifiers. BF makes that whole statement bivalent. Since it is true, it is necessary. Thus the same G witnesses NRGDWR, including when its output type is e.

Conversely NRGDWR gives RC by §26.2. Two small instances give C5.

First, any rigid graph G on input t that is necessarily total yields □BF_t. At an arbitrary world suppose ∀p□Xp. Every G-instance (p,y) then necessarily satisfies Xp. Inextensibility of G yields G≤λp y.Xp. Necessary totality of G gives □∀pXp. The argument holds at every world because both rigidity and totality of this G are necessary. Hence □BF_t. Such a G is supplied even by the empty-dependency constant-output rule.

Second, take distinct p,q:t. Use the empty-dependency rule whose current graph sends p to ⊤ and every input different from p to ⊥. Its rigid solution G satisfies G(p,⊤) and G(q,⊥), and these memberships persist. If p and q could coincide, necessary functionality of G would identify ⊤ with ⊥ there, an impossibility. Thus ND_t holds. The combination ND_t+BF_t gives □ND_t: for each p,q, split on their current equality. Equality persists by NI; inequality persists by ND_t and 4. In either case □((p≠q)→□(p≠q)); applying BF_t twice to p,q gives □ND_t. The recorded type-t reduction then gives full C5.

Finally C5+RC is equivalent to Plenitude+Functionality using the proved records. C5 gives ND and Functionality; RC gives Weak Rigid Comprehension, and WRC+ND gives Plenitude. Conversely Plenitude gives ND and Actuality; Functionality gives BF; ND+BF yields C5; C5+Actuality gives RC. Each step is an unboxed implication at the displayed premise set. None infers Atomicity from C5+Actuality.

This supplies an exact answer to a further potential ambiguity in “rigid recursive solution.” Requiring a rigid graph coextensive with the current recursion solution expresses RC. Requiring that graph to remain a function throughout the modal range adds C5. Requiring identity uniqueness of all current graph solutions instead forces the much stronger Fregean collapse of §23.2.

## 27. Exact internal finiteness of the primitive hereditary core in bare C

This strengthens the externally fixed finite-size calculation in §§12–14 to genuine impredicative Frege finiteness. Write Fin_α(A):=∃n(N_αn∧nA). The claim concerns the property Core_τ inside the ambient τ-domain; it does not assert finiteness of that entire ambient domain.

**Theorem.** For every fixed admitted type τ:

* if e does not occur in τ, C proves Fin_τ(Core_τ);
* if e occurs in τ, C proves

      Fin_τ(Core_τ) ↔ Fin_e(⊤_e).

No C5, BF, ND, Choice or global RC is required. In particular the corresponding infinitude of any fixed primitive core containing e is equivalent to individual infinitude. This contrasts with the ambient relational-domain dichotomy under BF, where Infinity_t is an independent source of infinitude.

### 27.1. Finite truth-pattern separation

Let A:αt be finite, H:βt any admitted family, and E:αβt any relation. Suppose

    ∀u,v[(Hu∧Hv∧∀x(Ax→(E(x,u)↔E(x,v))))→u=v].

Then H is finite in C.

Induct on a cardinality counting A, universally over H. If A is empty, the separating condition makes H at most singleton. At a successor choose a∈A and put B=A−{a}. Partition H into

    H₁(u):=Hu∧E(a,u),   H₀(u):=Hu∧¬E(a,u).

Within either part, two members agreeing on B also agree at a, and therefore on all A; they are identical. The induction hypothesis makes each part finite. Their finite union is H. This uses only current truth patterns and identity of the separated entities, not pointwise Boolean output identities and not construction of all possible assignments.

### 27.2. Finite products of argument domains

If each A_i:σ_i t is finite, the property of tuple-haecceity codes

    T(c):=∃x̄[(∧ᵢ A_i(x_i))∧c=H_x̄],  c:σ̄t,

is finite in C. Apply the finite-indexed-union lemma repeatedly: for a fixed full tuple the singleton {H_x̄} is finite; union over the finite last coordinate remains finite, then over the previous coordinate, and so on. This is a finite metalinguistic iteration of the internal finite-fiber theorem. It selects no representatives and introduces no tuple objects of type e. The empty tuple has the single code ⊤.

### 27.3. The finite direction

Induct on the type expression. Core_e is the individual universe. Core_t consists exactly of ⊥ and ⊤ by §14 and is finite in C. Let τ=σ̄t and suppose all argument cores are finite. Form their finite code property T as in §27.2, and put

    E(c,Y):=∃x̄(c=H_x̄∧Y[x̄]).

Take H to be Core_τ. If two H-members agree on E at every T-code, then they agree on every tuple of core arguments, by the tuple-code injectivity theorem. At every other tuple both are false by their core support conditions. They are therefore currently coextensive. Since both are rigid, §12.1 identifies them. The finite separation lemma §27.1 now makes Core_τ finite.

Starting from finite e proves this for every type. If the type contains no e, the induction starts only from the finite proposition core and proves finiteness outright. This proof deliberately does not claim that partially applying a rigid relation at an arbitrary argument leaves a rigid relation in bare C; that claim can fail without the later C5 conditions. Encoding the whole finite tuple avoids the issue.

### 27.4. The reverse direction

Every core domain is inhabited in C: the individual domain is inhabited, and bottom belongs to every relational core. For τ=σ̄t and any coordinate j, choose fixed core arguments in the other finitely many coordinates. The admitted map

    a ↦ H_(c₁,…,c_(j−1),a,c_(j+1),…,c_n)

injects Core_{σ_j} into Core_τ. Its image is rigid as a tuple haecceity and is supported on the required cores. The coding lemma makes it injective. If Core_τ is finite, the finite-image/inverse-graph lemma therefore makes Core_{σ_j} finite. No operation with output e is used.

If e occurs in τ, follow an occurrence down the finite type expression. Repeated application of the preceding implication reaches finiteness of Core_e, which is finiteness of the individual universe. This proves the reverse direction and the theorem.

### 27.5. Scope for Strong Possibility and relative numerical cores

Strong Possibility's e-monism gives Fin_e(⊤_e), so every fixed primitive Core_τ is genuinely Frege-finite already by C. The earlier explicit standard cardinal counts under monism remain valid and are stronger when a particular fixed type is displayed. Meanwhile Max supplies infinitude of ambient relational types and of its numerical domain. Those ambient entities cannot all fit into the primitive hereditary core at the corresponding type.

This does not contradict §24's infinite numerical relative cores under C5+Infinity_t. Their base sort is N_t, not the primitive individual sort. Under C5 the companion Frege note §20 makes N_t rigid, so the relative-core interpretation is available; under Max the companion numerical-collection theorem obstructs that rigid-base premise. Thus the distinction is mathematically exact rather than an ambiguity in the word “core.”

## 28. Two choice-free closure operations on rigid relations

The preceding proofs use finite unions of rigid relations. Two further useful closures hold already in C and help delimit the role of C5.

**Projection.** If R(x̄,ȳ) is rigid, then U[ȳ]:=∃x̄ R(x̄,ȳ) is rigid. Persistence retains a witnessing tuple and uses persistence of R. At any world, suppose ∀ȳ(U[ȳ]→□Z[ȳ]). Every current R-instance then necessarily satisfies the relation T(x̄,ȳ):=Z[ȳ]. Inextensibility of R yields R≤T, which entails U≤Z by necessary existential elimination. Since R's rigidity is necessary, the same local argument holds throughout the modal range and proves global inextensibility. No BF is needed: the witness is eliminated inside an already necessary inclusion.

**Products on separate variables.** If A[x̄] and B[ȳ] are rigid, their tensor

    P[x̄,ȳ]:=A[x̄]∧B[ȳ]

is rigid. Persistence is immediate. For local inextensibility assume every P-instance necessarily satisfies Z[x̄,ȳ]. Fix a current A-instance ā. Every B-instance necessarily satisfies Z[ā,ȳ], so inextensibility of B gives B≤λȳ.Z[ā,ȳ]. This inequality is an algebraic identity and hence necessary. Inextensibility of A, applied to the predicate Q[x̄]:=(B≤λȳ.Z[x̄,ȳ]), now gives A≤Q. Together these necessary inclusions give P≤Z. The source rigidities are necessary, so discharge and necessitate to get the global clause.

These facts do not imply that intersections on a shared variable preserve rigidity. The intersection is obtained by identifying the two product coordinates, and that identification can introduce new instances when currently distinct entities coalesce. Section 19.4 gives the exact singleton obstruction ND. Nor does projection closure make an actually total rigid graph necessarily total: its projection can be a rigid **current coextension** of the universe without being the universal intension. Requiring necessary totality is what produced BF in §26.3.

## 29. Current mathematics by definable quotients: an essential scope qualification

The rigid-core results should not be read as saying that C5 is needed for every interpretation of ordinary mathematics. There is a weaker, purely current interpretation that uses definable equivalence relations instead of identity of ambient representatives. It works in C and, with arithmetic noncollapse I_σ, interprets full impredicative second-order arithmetic and the fixed finite-order extensional relational language. This is not the recorded Gallin axiom, not an assertion of ambient Extensionality, and not a modal-stability theorem.

### 29.1. Full second-order arithmetic at the current point

Fix σ and assume I_σ, equivalently I*_σ. Let ν=ν_σ. Interpret natural numbers by N_σ⊆ν, with actual ambient identity as numerical equality, zero by 0_σ, and successor by its admitted graph or explicit Frege successor term. Addition and multiplication are interpreted by their total unique Frege graphs. Eliminate numerical function terms through these graphs when necessary; no Plenitude is used to manufacture operations representing arbitrary unique graphs.

Interpret a second-order set variable by an arbitrary ambient predicate X:νt, with membership Xn on numbers. Set equality is the definable equivalence relation

    X ≈ Y := ∀n(N_σn→(Xn↔Yn)).

All number quantifiers are restricted to N_σ. Second-order set quantifiers range over all admitted ν-predicates; values outside N_σ are immaterial. A structural induction on translated formulas shows that replacing X by an ≈-equivalent predicate preserves truth. For atomic membership this is the definition; for set equality it is equivalence-relation reasoning; Boolean operations and both kinds of quantifier preserve the induction hypothesis. Thus the equality and substitution axioms for source sets are satisfied. Duplicate ambient representatives cause no defect in this definable-quotient interpretation.

For every source comprehension instance, including those with arbitrary second-order quantifiers, the ambient abstract

    λn^ν.(N_σn∧φ*(n))

is an admitted set representative and satisfies the required equivalence for all numerical n. Parameters remain available, and λ-comprehension allows the translated quantifiers in φ*. No predicative restriction has been introduced.

The full second-order induction axiom follows directly from impredicative numberhood. Given X0 and successor closure on numbers, instantiate N's induction with W(n):=N_σn∧Xn. W contains zero and is closed under successor, so every number satisfies X. The same reasoning applies to a set defined by any translated formula, with its parameters. The Peano and arithmetic graph axioms are the C+I_σ theorems used in the companion Frege note. Hence the full Z₂ axiom schemes are interpreted currently.

The argument does not identify coextensive **numerical entities**: number equality remains literal identity at ν. In particular the interpretation does not merge distinct empty numerical intensions in a Maximalist model. Only the source set sort is quotiented by membership on those numbers.

### 29.2. Finite-order extensional relational types

More generally fix any inhabited base property K:αt. For source types in the fixed relational language, translate the base type to α and t to t. Define a validity predicate V_s and equivalence E_s recursively:

    V_e(x):=Kx,                 E_e(x,y):=(x=y);
    V_t(p):=⊤,                 E_t(p,q):=(p↔q);

    V_{ab}(F):=
      [∀x(V_a(x)→V_b(Fx))] ∧
      [∀xy((V_a(x)∧V_a(y)∧E_a(x,y))→E_b(Fx,Fy))],

    E_{ab}(F,G):=∀x(V_a(x)→E_b(Fx,Gx)).

The arrow case is used only for source-admitted relational output types b. All displayed ambient operation types are therefore admitted. Interpret source quantifiers with V guards and source equality by E. At each type E is an equivalence relation on valid entities, by induction on type. Each valid operation takes valid arguments to valid results and respects input equivalence by definition.

Application respects equivalence: if F E G and x E y with all four objects valid, then Fx E Gx by pointwise function equivalence, and Gx E Gy by validity of G; transitivity gives Fx E Gy. Simultaneous induction on terms and formulas then proves both validity of translated terms and invariance under equivalence of free parameters. In the abstraction step λx.B*(x) is an actual admitted ambient term; the induction hypotheses prove its output validity on valid x and its required input congruence. Thus it is valid. In the quantifier step the valid domain is fixed by the type, and the formula induction hypothesis gives invariance pointwise, so guarded universal and existential quantifiers preserve it.

The logical operations have valid representatives. For example the source universal quantifier at a is represented by

    Q_a(P):=∀x(V_a(x)→Px).

Pointwise equivalence of valid predicates makes these universal propositions materially equivalent, so Q_a has the required congruence. The source equality relation is represented by E_a itself, which is congruent on valid inputs by symmetry and transitivity. Valid domains are inhabited: use any chosen K-element at the base, a proposition at t, and constant valid functions inductively. Only finitely many such witnesses occur in a fixed interpreted type.

Consequently current extensionality, λ-comprehension and the ordinary extensional relational higher-order logic hold in this interpretation. It is a Henkin interpretation through definable quotients, not an external full-function-space claim. Taking K=N_σ and using the relational arithmetic graphs gives finite-order extensional relational arithmetic. The ordinary current analysis constructions available from those axioms do not require rigidity of N_σ.

### 29.3. What the interpretation does and does not establish

There is no assertion that an arbitrary total unique numerical graph has an ambient operation representing it. Numerical equality is literal identity, so one cannot solve that issue by pooling coextensive numerical outputs. The interpretation does not add a description operator, unique-choice axiom, Hilbert-choice operator, or full choice scheme. Source numerical function symbols may be eliminated in favor of their total unique graphs; the fixed relational language suffices for the claims above.

Likewise this is a **current** interpretation. Its equivalence at t is material equivalence, so its two truth-value classes do not identify the underlying proposition intensions. Interpreting an ambient modal operator through this quotient would change its meaning and is not part of the theorem. No statement of ambient Gallin rigidity, ambient Extensionality, No Pure Contingency or numerical collection has been inferred.

Max supplies I_σ, and Strong Possibility implies Max. Subject to the recorded consistency claims for those theories, they therefore support this current arithmetic interpretation too. The finite primitive-core theorem in §27 consequently cannot establish that they lack all ordinary arithmetic or analysis. The stronger contribution of the C5 rigid-core interpretation is actual identity of rigid representatives, closure in a stable domain, and modal stability of core-restricted mathematics; BP additionally gives the stronger unrestricted-quantifier parameter absoluteness and RC representatives detailed earlier. The distinction is between these exact strengths, not between mathematical existence and its wholesale absence.

## 30. The e-free primitive core is already canonically finite and stable in C

There is a further qualification to the C5 comparison. At a fixed type with no occurrence of e, the primitive core has a finite list of **closed pure canonical terms** already in C. The list can be constructed uniformly in the external finite type expression.

At t the list is ⊥,⊤. Suppose lists have been constructed for all arguments σ_i of τ=σ̄t. For every subset S of the finite product of those lists, let c_S be the finite union of the tuple haecceities indexed by S. Each c_S is rigid in C by §14 and supported on the lower cores, so C proves Core_τ(c_S).

For arbitrary Y with Core_τ(Y), its current memberships on the finitely many listed tuples determine one subset S by a finite classical case split. Outside that product it has no instances, by core support and the lower exhaustive enumerations. It is therefore currently coextensive with c_S. Both are rigid, so §12.1 gives Y=c_S. If S≠T, choose a tuple in their symmetric difference. The lower canonical terms are necessarily distinct, by induction; evaluation at that tuple therefore makes one of c_S,c_T true and the other false. Thus C proves c_S≠c_T, and necessitation proves their necessary distinctness. The induction starts from the C theorem ⊥≠⊤.

Consequently C proves an exhaustive enumeration

    ∀Y^τ[Core_τ(Y) ↔ ∨_{S}(Y=c_S)]

by pairwise necessarily distinct closed pure terms. The list has length c_t=2 at t and c_τ=2^(∏ᵢ c_{σ_i}) at a relational type. Because the enumeration is a C theorem, it can be necessitated; Modalized Functionality identifies the Core_τ predicate itself with this finite union of haecceities. Hence Core_τ is rigid already in C, and belongs to Core_{τt}. This conclusion is special to e-free types; it does not apply to the primitive individual universe in a Maximalist model.

The canonical lists also make the e-free core an actual finite extensional structure in C. Application on listed arguments reduces to the corresponding finite table, and guarded abstractions reduce to finite unions of listed haecceities. Every formula whose variables, parameters and quantifiers stay inside these e-free core domains reduces to a finite Boolean combination of canonical identities and applications. Its truth is settled already in C, by finite reasoning. No BF is needed for those quantifiers because each guarded quantifier has a C-provable finite enumeration.

Two restrictions matter. First, Core_τ(x) for an arbitrary **noncore** ambient x need not be bivalent in C: x can later coincide with a canonical value. Rigidity of a finite haecceity union does not by itself give ND for outsiders. Second, an unrestricted ambient pure quantifier can still make a formula contingent, even with canonical core parameters; the ambient assertion of individual monism is an immediate example under Max. The result concerns the finite e-free core structure and its restricted quantifiers, not full ambient pure-formula absoluteness.

## 31. A canonical comparison between current quotients and rigid representatives

The two interpretations in §§24 and 29 are connected exactly, but not by simply including core objects into the validity domains. For example the core relation H_⊤:tt is true at ⊤ and false at a currently true contingent proposition p. Hence it is not a valid function for §29's input equivalence E_t=(↔): p E_t ⊤ while H_⊤p and H_⊤⊤ differ currently. An extension to all equivalent ambient representatives is required.

Work in C5+Actuality, equivalently Plenitude+Functionality by §26.3 and its recorded implications. Fix the same rigid inhabited base K:αt for both interpretations. Let L_a be the relative rigid-core domains of §24, and let V_a,E_a be the current validity/equivalence definitions of §29.

There are type-recursive translations q_a from valid representatives to core objects, and i_a from core objects to valid representatives, satisfying:

1. V_a(x) implies L_a(q_a x), and L_a(u) implies V_a(i_a u);
2. q_a(i_a u)=u for core u;
3. E_a(i_a(q_a x),x) for valid x;
4. for valid x,y, q_a x=q_a y iff E_a(x,y).

Thus q identifies exactly the current equivalence classes and supplies actual rigid representatives; i supplies equivalence-respecting extensions of core functions. At a base type translated to e, q_e and i_e are **metalinguistic identity substitutions**, never operation terms of type e→e. At all relational translated types the displayed translations are admitted operations. For the numerical base all translated types are relational, but the same convention is harmless.

### 31.1. Construction

At the base put q_e(x)=x and i_e(x)=x. At t let q_t=b be a truth evaluator satisfying Eval(b) from §18.1, and let i_t be the identity. C5+Actuality supplies ND+Actuality and hence such a b. Its kernel is material equivalence and its values are exactly the matching Boolean constants, so the four clauses hold at t.

Suppose q_a,i_a,q_b,i_b have been constructed, with b a source relational output type. For a core function G define

    i_{ab}(G) := λy. i_b(G(q_a y)).

For a valid function F define q_{ab}(F) by the guarded abstraction whose value on a core x is

    q_b(F(i_a x)),

and whose flattened relation is bottom at noncore x. Explicitly, if b=ρ̄t in the translated relative-core language, write

    q_{ab}(F)[x,z̄] := L_a(x) ∧ q_b(F(i_a x))[z̄].

These are ordinary admitted λ terms, using already chosen lower-type translations. The definitions are total as ambient operations; their stated correctness is restricted to the valid or core input domains.

The base K is a property at an arbitrary ambient type α. It is not required to be the primitive individual universe, nor is its membership condition dropped when α is itself relational. The source base is translated to α as one indivisible sort. In particular an occurrence of α inside a translated argument is not flattened into α's ambient internal arguments. Flattening the displayed output b means flattening the source relational type b and then translating its argument sorts.

### 31.2. Validity and core membership

If F is valid and x is core, i_a x is valid, so F(i_a x) is valid and q_b sends it into the b-core. The guarded-abstraction theorem of §15, equally valid in the relative core, therefore makes q_{ab}(F) core.

Here the guard is essential twice. C5 makes each L_a(x) a bivalent proposition, even for an arbitrary ambient x. At a core x it is therefore literally ⊤, so the guarded operation value is identical to q_b(F(i_a x)), not merely currently coextensive with it. At a noncore x the guard is literally ⊥, giving the required core support and bivalent membership. These facts justify the operation identities used below. A merely true, potentially contingent guard would not suffice.

If G is core and y is valid, q_a y is core, G(q_a y) is core, and i_b sends it to a valid output. If y E_a z, the lower kernel property gives q_a y=q_a z. The two displayed outputs are consequently identical, hence E_b-equivalent. Thus i_{ab}(G) is valid. This proves clause 1 without treating an arbitrary core function as already valid on all ambient representatives.

### 31.3. The two retraction identities

For core G and core x, the definitions and lower-type identities give

    q_{ab}(i_{ab}G)(x)
      = q_b(i_b(G(q_a(i_a x))))
      = Gx.

Both outer relations are core and supported on the same core arguments. The core extensionality theorem therefore gives q_{ab}(i_{ab}G)=G, proving clause 2.

For valid F and valid y, lower-type clauses give

    i_{ab}(q_{ab}F)(y)
      = i_b(q_b(F(i_a(q_a y))))
      E_b F(i_a(q_a y))
      E_b Fy.

The last step uses validity of F and i_a(q_a y) E_a y. Thus the two operations are E_{ab}-equivalent, proving clause 3.

### 31.4. Exact kernel and compatibility with application

If F E_{ab} H, then at every core x the valid argument i_a x gives F(i_a x) E_b H(i_a x). The lower kernel property identifies their q_b-values. Core extensionality gives q_{ab}F=q_{ab}H.

Conversely suppose those core images are identical. For any valid y let x:=q_a y. Evaluation at this core x, followed by the lower kernel property, gives F(i_a x) E_b H(i_a x). Since i_a x E_a y and both F,H are valid, this yields Fy E_b Hy. Hence F E_{ab} H, proving clause 4.

In particular application commutes after passage to the core:

    q_b(Fy) = (q_{ab}F)(q_a y)

for valid F,y. Indeed the right side is q_b(F(i_a(q_a y))), and validity of F plus the lower retraction and kernel properties identifies it with q_b(Fy). Boolean operations and guarded quantifiers commute in the same sense: every valid argument is equivalent to the extension of a core representative, and source formulas respect E. A formula induction therefore proves equality of the current mathematical truth values in the two interpretations, with parameters related by q and i.

### 31.5. Modal scope and mathematical consequence

The construction chooses a local truth evaluator b. Its correctness, and the correctness of the recursively defined q,i, are asserted at the current point. The proof does not put that same b under a necessary correctness clause; §18.3 shows why that would force the Fregean Axiom. C5+Actuality is sufficient for the local comparison, but does not by this argument imply □Actuality, Atomicity or BP.

BP supplies the needed premises separately at every world and hence a comparison at every world, with potentially different evaluators. Under the suitable pure/invariant parameter restrictions already proved in §§11 and 24, the rigid structures also give the stated modal absoluteness. This is the precise sense in which the stronger theory converts the current quotient mathematics available in C into mathematics with actual rigid representatives. It does not claim that the weaker theory lacks the current quotient interpretation.

## 32. Nonstandard numbers, Henkin closure and the arithmetic-potentialism obstruction

### 32.1. Every admitted modal formula is subject to numerical induction

For any formula φ(n,ā) of C, including formulas with arbitrarily nested modalities and higher-order quantifiers, λn.(N_σn∧φ(n,ā)) is an admitted predicate. The defining induction property of N_σ consequently gives the induction instance for φ on numbers. This uses no NC, C5, Plenitude or choice. Under I_σ it is induction on an ordinary Peano number domain by the arithmetic interpretation in §29.

In particular, in a model whose numerical domain is externally nonstandard, no admitted predicate can have as its current extension exactly the external standard cut {0,Suc 0,Suc²0,…}. That cut contains zero, is closed under successor and omits a number; admitting it would contradict N-induction. This observation also applies to a predicate defined by a modal formula: lambda closure prevents one from withholding a definable predicate merely by restricting the higher-order Henkin domains.

### 32.2. The precise obstruction from the full arithmetic-extension frame

Hamkins, *The modal logic of arithmetic potentialism and the universal algorithm*, arXiv:1801.04599v5, Theorem 5, p.9, identifies the external standard cut in the full frame of models of a fixed consistent c.e. PA extension PA⁺, ordered by end-extension or by extension. Its defining formula is □Con(PA⁺_k), with the corresponding extension necessity. Thus modal induction fails at every nonstandard arithmetic world of that frame. The formula already belongs to the partial potentialist language; unrestricted nesting of number quantifiers and modalities is unnecessary for this obstruction. Primary source: https://arxiv.org/pdf/1801.04599, Theorem 5, p.9. This paragraph reports the source theorem; the following application to C is our argument.

Suppose an intended C interpretation preserved the ordinary arithmetic at such a nonstandard world and interpreted its box exactly as necessity over that full extension frame. The translated formula θ(k):=□Con(PA⁺_k) would then define the external standard cut. C requires the abstract λk.(N_σk∧θ(k)), contrary to §32.1. Merely reducing the admitted second-order predicates therefore cannot repair this particular construction while leaving its arithmetic and extension modality unchanged. Any successful alternative must change another relevant ingredient: for example the accessible class of extensions, the arithmetic interpretation in the worlds, or the claimed identification of the modalities. This is an obstruction to a proposed semantic realization, not a contradiction in C, Max or Strong Possibility.

### 32.3. Explicit nonstandard Henkin models satisfying boxed Functional Choice

In ZFC take the recorded full ordinary Henkin model M with infinite individual domain, two truth values, and all admitted function spaces. It satisfies C, Fregean, Functional Choice and Infinity_e; box is identity, so it satisfies their boxed forms. Form its sortwise ultrapower M^ω/U using a nonprincipal ultrafilter U on ω.

Here is enough detail to avoid hiding the higher-order closure issue. Regard M as a many-sorted first-order applicative structure, with one sort for each admitted type and application symbols at every admitted arrow. Include its logical constants and, if desired, a symbol for each lambda term with its finitely many free variables as parameters. The ordinary lambda evaluation equations and all quantified sentences are first-order sentences of this many-sorted structure. Take all sorts and symbols coordinatewise modulo U. Łoś's induction applies to this many-sorted language: the existential step selects witnesses coordinatewise on a U-large set, using choice in the metatheory. In particular every lambda evaluation equation survives, so the ultrapower is a Henkin interpretation, not merely an application structure missing comprehension. Equivalently, coordinatewise interpretations of a lambda term give its required ultraproduct representative, and Łoś verifies evaluation on arbitrary ultraproduct arguments.

Every C theorem and each fixed instance of Functional Choice, its boxed form, and Infinity_e transfers. The ultrapower of the finite truth-value sort is still {0,1}; therefore modality remains trivial in this example. The domain defined by N_e is, by Łoś applied to its fixed definition, the ultraproduct of the standard numeral domains of M. The entity c=[Suc^n 0]_U belongs to N_e and differs from every standard numeral Suc^k0, because the equality holds only on the singleton index n=k. Thus the model has nonstandard numbers despite satisfying C+□Functional Choice+Infinity_e. Its numerical predicates necessarily omit the external standard cut by §32.1. Its arithmetic theory is nevertheless the full true first-order arithmetic of the original model, by Łoś; nonstandardness is not the same as arithmetic error.

Nontrivial modality can be retained as well. Start instead with the full constant-domain S5 model with infinite individuals and a fixed finite world set W of size at least two. Present all of its intensional domains and application/logical operations as above, together with one truth predicate T_w on propositions for each w∈W. The proposition sort is the finite set P(W), so its ultrapower is canonically P(W). Each world's satisfaction relation obeys Łoś. Quantifier and lambda evaluation laws, C, □Functional Choice and Infinity_e therefore survive. The two-world proposition true at just one world remains contingent, while c=[Suc^n0]_U is again nonstandard. The resulting domains are Henkin domains, not full external function spaces. The frame is still the same finite S5 frame, and no full arithmetic-extension semantics is claimed.

These constructions depend on a nonprincipal ultrafilter in the metatheory. They are explicit relative model arguments in ZFC, not choice-free internal consequences of C.

### 32.4. What transfers for Max, and what remains conditional for Strong Possibility

The same sortwise ultrapower argument preserves every externally specified sentence of any fixed schema. In particular, if one begins with a semantic C model satisfying pure Max and having standard numerical domain at the designated root, the ultrapower still satisfies every pure Max instance while acquiring c=[Suc^n0]_U. This uses the original schema with its original C-consistency side condition, unchanged by the construction; the added name for c does not turn pure Max into signature Max. The ultrapower has the same first-order arithmetic theory at that root as the original standard-root model. No conclusion of numerical categoricity follows from arithmetic soundness of such a root.

For Strong Possibility only a conditional statement is warranted here: given a model of C+SP, its numerical domain is infinite by the recorded SP⇒Max⇒I_σ consequences. A nonprincipal ultrapower yields a nonstandard numerical element (use a sequence of standard numerals) and preserves all existing SP instances. Thus consistency of SP cannot by itself force external standardness of its Henkin numerical domain. This is not a construction of an initial SP model and does not settle SP's consistency.

## 33. An internal S5 construction and the exact common arithmetic shadow

This section supplies the all-counting-type extension of the current quotient transfer in the companion Frege note §35. It concerns ordinary first-order arithmetic, not modal consequences and not Functional Choice. The preliminary construction and arithmetic bridge were independently checked in the parallel Frege lane; this is an informal mathematical audit, not named-person verification or Lean verification.

**Theorem.** For any admitted counting type σ and ordinary first-order arithmetic sentence A, the following are equivalent:

1. C+I_σ proves A in its σ-Frege interpretation;
2. C+Infinity_σ proves that interpretation of A;
3. C5+Infinity_σ proves that interpretation of A;
4. C+□Plenitude+Infinity_σ proves that interpretation of A;
5. C+□Plenitude plus the schema Infinity_ρ at every admitted ρ proves that interpretation of A.

Moreover the arithmetic shadows do not depend on σ: the corresponding first item for any two counting types has the same ordinary arithmetic consequences. All schemata retain their original type scope. The assertion concerns the finitary Henkin proof systems, not full external higher-order semantics. No analogous claim about adding □Functional Choice is established.

The easy inclusions follow from Infinity_σ⇒I_σ and from the nesting of the displayed premise sets. For the substantive converse we construct, from the current arithmetic of any C+I_σ model, a Henkin S5 model of item 5 with exactly that arithmetic at every counting type. The construction also gives a definable interpretation: all domains, quotients, applications and quantifiers below are given at each finite type by fixed formulas and lambda terms. Consequently one can phrase the converse as a proof interpretation rather than relying on a stronger full-semantics completeness claim.

### 33.1. The extensional arithmetic input

Apply §29's current quotient construction with base K=N_σ. Its result E is an extensional two-valued Henkin structure in the same relational type language. Its base domain B is M's current N_σ, with inherited zero, successor, addition and multiplication represented by graphs where an e-output function symbol is inadmissible. Under I_σ it is a Peano structure. Induction holds with every admitted E-predicate and with parameters from every E-type, because each such predicate pulls back to an admitted predicate on N_σ in M. All subsequent inductions on B use precisely this full typed-parameter induction.

The structure E contains all relations defined by its own higher-order formulas and lambda abstractions, though it need not contain every external subset or function. Its current arithmetic is the original arithmetic of M by construction. The finite-cardinality arguments used below take place in E, where equality of relational objects is extensional identity.

### 33.2. Use the number base as a world domain

Let the S5 world set be W:=B, with every world accessible from every world. Translate C's types into E-types by

    h(e)=e,       h(t)=et,       h(ab)=h(a)h(b).

Since b is always relational in an admitted arrow, h(b) is relational, so every translated type is admitted. If τ=ρ₁…ρ_k t, then h(τ)=h(ρ₁)…h(ρ_k)et: the final e argument is the world coordinate. Define the domain of C-type a to be the E-domain at h(a), constantly over all worlds.

A proposition p is thus an admitted E-predicate of worlds. It is true at w exactly when E satisfies p(w). Application is ordinary E-application. Boolean connectives act pointwise on the final world argument. Quantification at C-type a is interpreted by

    (∀^a P)(w) := ∀x^{h(a)} P(x)(w).

Identity at a is the constant-world proposition

    Eq_a(x,y)(w) := (x=y in E).

Because E is extensional, Eq_t(p,⊤) holds just when ∀v∈B p(v). Hence C's defined box is exactly universal S5 necessity over W, with its value the corresponding constant proposition. All domains are constant and all identities are settled.

Closure under C lambda abstraction follows by directly translating each term into E: h respects application and the admitted arrow formation, and the translated Boolean and quantifier operations have just been given by admitted E terms. The H axioms hold at each world by their usual interpretation; H-equivalent bodies agree at every world and tuple, so extensionality in E identifies their translated lambda abstractions. This validates Logical Equivalence and hence C. The argument checks Henkin closure explicitly and does not presume full external function spaces.

### 33.3. Boxed Plenitude by an explicit unique-output construction

Fix a world w and a current total unique graph U^{a b t}, with b relational. Write b=ρ̄t. Its E translation is U(x,y,w). Define an operation f at the C type ab by the E lambda expression

    f(x)[z̄,v] := ∃y^{h(b)} [U(x,y,w) ∧ y[z̄,v]].

For each fixed x, let y₀ be its unique U-output at w. Then the displayed relation is coextensive, on every z̄ and every world v, with y₀. Extensionality in E gives the actual entity identity f(x)=y₀. Thus U(x,f(x),w). The same argument works when b=t, with z̄ empty; no e-valued operation has been introduced. Existence of y₀ is used locally in the proof for a fixed x, so no choice principle is needed.

This works for every w and every admitted U, with w simply an E parameter in the displayed lambda term. Hence the new S5 model satisfies □Plenitude at every type. One does not need a single C operation evaluating arbitrary world parameters; the construction is performed in the ambient E structure, and its result is an admitted operation at the required translated type. Functional Choice does not follow from this unique-output pooling argument.

### 33.4. Canonical injections from the number base

For every C-type a there is an E-definable injective graph from B into the new a-domain. For a=e use identity as a graph, not an e→e term. For a=t use

    j_t(n)(v) := (v=n).

Thus different numbers give different singleton-world propositions. At a relational arrow ab put j_ab(n):=λx.j_b(n), ignoring its argument. Every input domain is inhabited, so this is injective whenever j_b is. These are admitted E operations whenever the output is relational; the only base case requiring graph notation was e.

For every n∈B and a, the image under j_a of the strict initial segment [0,n) is an admitted E-predicate of h(a), definable by ∃k<n (x=j_a(k)). Its constant-world intension is an admitted C predicate at a. This supplies n-element witnesses at every type, including nonstandard internal n; all finite reasoning here is induction inside E rather than an external standard-size assertion.

### 33.5. The arithmetic bridge at every counting type

Fix a C counting type a. Define an E operation

    q_a(n)(X)(w) := “the E-extension {x:X(x)(w)} admits a bijection with [0,n)”.

The bijection is an admitted E binary relation, quantified at the fixed type h(a)et, with the usual graph clauses. The defining formula contains only E-quantifiers and parameters. Therefore q_a belongs to E's type e h(ν_a), which is exactly the translation of the admitted C operation type eν_a. This typing point makes the image predicate used below an actual C predicate. No operation with output e is required.

The ordinary finite-cardinal deletion and adjunction proofs in E show

    q_a(0)=0_a,
    q_a(Sn)=Suc_a(q_a(n)).

These are equalities of the complete intensions: for each X and w, a bijection with [0,Sn) can be restricted after removing the unique preimage of n; conversely a bijection after deleting one element extends by sending that element to n. The restrictions and extensions are relations defined by lambda comprehension. Equality at every X,w becomes actual identity by E extensionality. Successor on the left may be read through its inherited unique graph if one avoids numeric function notation entirely.

Now use E induction on n, with the formula saying at a chosen world w that N_a(q_a(n)). Zero and successor closure give this for every n. Since w was arbitrary, every q_a(n) is a C-number at every world.

Conversely the C predicate

    P(y) := ∃n^e (y=q_a(n))

contains 0_a and is closed under C successor, by the two displayed identities. Frege N-induction in C therefore implies that every C-number belongs to P. Thus q_a maps B onto the C-number domain at every world. Here an admitted C image predicate is used; an external set of numerical values is not substituted into induction.

To prove injectivity, use §33.4's image of [0,n) under j_a as a witnessing C property X_n. Then q_a(n)(X_n) holds. If q_a(n)=q_a(m), the same X_n is in bijection with both initial segments [0,n) and [0,m). Composing the two graph bijections gives an admitted bijection of the segments. Finite-ordinal pigeonhole, proved by E induction, gives n=m. This argument applies to all internal n,m, not just standard numerals.

The bijection q_a preserves zero and successor, so it preserves addition and multiplication by their recursive graph clauses and uniqueness, using induction. It therefore preserves every ordinary first-order arithmetic sentence. The new model's arithmetic at every counting type a is exactly the inherited arithmetic on B, which was the original current arithmetic on N_σ in M.

Finally the whole a-domain cannot be in bijection with [0,n) for any n: composing such a bijection with j_a would inject B into a finite initial segment, contradicting finite pigeonhole on its first n+1 members. Since q_a exhausts the numerical domain, no Frege number counts the universal a-property. Hence Infinity_a holds for every admitted a. The same argument is uniform in the chosen world, so these Infinity statements are also necessary in this particular model.

### 33.6. Conservativity and exact limits

If M satisfies C+I_σ and falsifies an arithmetic sentence A in its σ-interpretation, the construction gives a C+□Plenitude+all-type-Infinity model falsifying A at every counting type. This proves the required countermodel transfer. Equivalently, compose the definable quotient interpretation with the displayed internal S5 translation: each target axiom translates to a theorem over C+I_σ, and the arithmetic bridge makes the translation of A equivalent to the original A. Thus the theorem applies to the finitary proof systems without assuming external categorical semantics for arithmetic.

Applying the same transfer with different source and target counting types shows that the C+I_σ arithmetic shadows coincide. Intermediate theories between the indicated lower and upper theories have the same shadow as well, giving items 2–4.

The theorem gives structural/modal regularity without additional first-order arithmetic consequences beyond the common current Peano hierarchy. It does not identify the modal theories, establish conservation for arbitrary finite-order sentences, or give a Functional Choice model from an arbitrary source. It also does not compare this effective arithmetic theory with the non-effective additional arithmetic consequences of Max. In particular, the result cannot be used to infer that Max is inconsistent or arithmetically weaker than boxed Plenitude.

## 34. A canonical arithmetic graph in C, and its operational failure under Max

The following gives a direct internal counterpart of the arithmetic bridges used in §33. Its definition does not use Plenitude, choice, rigidity or external numerical categoricity. Throughout, S_σ means the explicit Frege successor term, and ν_σ is the σ-number type.

### 34.1. The least synchronized-successor relation

For counting types σ,ρ define the admitted relation

    J_{σ,ρ}(x,y) :=
      ∀Z^{νσ νρ t} [PairInd(Z)→Z(x,y)],

    PairInd(Z) := Z(0_σ,0_ρ) ∧
      ∀u v [Z(u,v)→Z(S_σu,S_ρv)].

C proves that J contains (0_σ,0_ρ), is closed under synchronized successor, and is contained in N_σ×N_ρ: the latter product itself is PairInd. It also proves the exact unfolding

    J(x,y) ↔ [(x=0_σ∧y=0_ρ) ∨
      ∃u v(J(u,v)∧x=S_σu∧y=S_ρv)].

For the nontrivial direction define T to be the displayed right-hand side. Zero and successor closure of J give T⊆J. Consequently T is PairInd: it contains the zero pair, and T(u,v) implies J(u,v), which gives T(S_σu,S_ρv). The defining universal property of J gives J⊆T. All inclusions here are current implications; no actual coextension has been promoted to intensional identity.

### 34.2. Exact functional and bijective conclusions

Assume I_σ. Induction on N_σ proves that every x has a unique J-output. At zero, unfolding excludes the successor case because zero is not a successor. Suppose x has the unique output y. Closure supplies output S_ρy at S_σx. For any other output z, unfolding gives predecessors u,v with J(u,v), S_σu=S_σx and z=S_ρv. Since u,x are numbers, successor injectivity under I_σ gives u=x, and uniqueness at x gives v=y. Hence z=S_ρy. This proves totality and single-valuedness as a graph, without constructing an operation.

The image property Q(y):=∃x J(x,y) contains 0_ρ and is successor closed. N_ρ-induction gives every ρ-number in the image. Therefore C+I_σ proves that J is a surjective functional graph N_σ→N_ρ even when I_ρ is not assumed. The target may be a finite numerical system with an absorbing overflow value.

If I_ρ also holds, the symmetric argument proves unique input. Thus

    C+I_σ+I_ρ proves J_{σ,ρ}:N_σ ≅ N_ρ

as a relational bijection preserving zero and successor. Any other supported graph preserving zero and successor is PairInd and contains J. If it is a function graph on N_σ, totality of J then makes the two graphs currently coextensive. This is the unique arithmetic graph isomorphism in that current sense. Preservation of addition and multiplication follows from their recursive graph equations and numerical induction. Consequently ordinary first-order arithmetic agrees across the two counting bases already inside the original model.

This conclusion does not identify the graphs as intensional relation objects, does not give an operation realizing J, and does not assert necessary arithmetic agreement from the unboxed I hypotheses. Under Max all I_σ hold, so the current graph comparison applies at every pair of counting types.

### 34.3. Pure Max forbids even two values of a cross-base arithmetic operation

Write k_σ:=S_σ^k0_σ for a fixed standard numeral. Pure Max proves

    ¬∃f^{ν_e ν_t} [f(2_e)=2_t ∧ f(3_e)=3_t],

and also

    ¬∃g^{ν_t ν_e} [g(3_t)=3_e ∧ g(4_t)=4_e].

For the first statement take the pure sentence A saying Fregean and exactly one individual. The full one-world singleton Henkin model verifies its C-consistency, so pure Max gives ◇A. In C+A the individual cardinalities overflow at 2, while the proposition domain has exactly two entities. Consequently 2_e=3_e=⊥_{ν_e}, whereas 2_t≠3_t: 2_t counts the universal proposition property and 3_t is empty. If the displayed f existed at the current point, NI would make each of its two value identities necessary. At the possible A-world, equality of the two inputs would force equality of the two outputs, contradicting 2_t≠3_t.

For the second statement use the C-consistent pure sentence B saying Fregean and exactly four individuals, witnessed by the corresponding full one-world finite Henkin model. In C+B there are exactly two propositions, so 3_t=4_t=⊥_{ν_t}. But 3_e≠4_e, since the universal individual property has cardinality 4 and not 3. NI applied to the two assumed g-value identities gives the same contradiction at the possible B-world.

All output types here are relational, so the operation types are admitted. No e→e term occurs. Only finitely many numeral values are required, and only the ordinary pure Max schema is used. There is no hidden parameterized-possibility or Strong Possibility assumption.

Any operation implementing the canonical graph J_{e,t} would have the first two forbidden values; any operation implementing J_{t,e} would have the second pair. The comma distinguishes these pairs of counting bases from the single predicate type et. Thus Max has canonical current arithmetic bijections between the number domains while denying operations that implement them in either direction. This is a concrete arithmetic instance of failed unique-output functionalization. Under Plenitude the canonical graph, completed by a fixed default outside its numerical source domain, does yield an operation. Its existence under Plenitude does not require Functionality; only any claim of identity between all such operations would need the further extensionality principle.

## 35. Necessary injections induce canonical arithmetic operations in the reverse direction

Unlike §34's general comparison graphs, some numerical comparison maps are operations already in C. This gives a precise asymmetry under Max.

Let j:ρ→σ be an admitted operation and assume □Inj(j), where Inj(j):=∀x z(jx=jz→x=z). Thus σ is relational in this formulation. For X:ρt define its image predicate

    j_*X := λy^σ.∃x^ρ(Xx∧y=jx),

and define the admitted operation F_j:ν_σ→ν_ρ by

    F_j(n) := λX^{ρt}. n(j_*X).

Then C+□Inj(j) proves, as actual identities of numerical intensions,

    F_j(0_σ)=0_ρ,
    ∀n^{νσ} [F_j(S_σn)=S_ρ(F_jn)].

The successor equation holds for all n, not just numbers. The zero equation follows from emptiness of an image being equivalent to emptiness of its source. For successor, necessary injectivity gives the crucial identity

    j_*(X−x) = (j_*X)−jx.

Indeed the two sides are necessarily coextensive: at every possible point, an image witness z≠x has jz≠jx, and conversely an image element different from jx has a preimage different from x. C's necessary-coextension-to-identity consequence of Modalized Fregean and Modalized Functionality gives the displayed identity. This is the step that allows applying an arbitrary numerical predicate n to the two properties; current coextension alone would not suffice.

Now F_j(S_σn)(X) says that some image element y belongs to j_*X and n holds of (j_*X)−y. Replace its image witness by y=jx with Xx, and use the deletion identity. The resulting formula is exactly S_ρ(F_jn)(X). Since the derivation is valid throughout the modal range under the necessary injection premise, the two numerical intensions are necessarily coextensive and hence identical. Formally, discharge the premise to obtain a C theorem, necessitate that theorem, and use persistence of □Inj(j); no BF step is used to box a merely current universal assertion.

N_σ-induction therefore proves that F_j maps N_σ into N_ρ and preserves zero and successor. If I_σ and I_ρ hold, §34's uniqueness theorem identifies its current graph on numbers with the canonical arithmetic bijection J_{σ,ρ}. F_j is then a current bijection of the numerical domains, despite having been defined on all numerical-type entities.

Two concrete necessary injections are C theorems:

- H:e→et, H(x)=λz(z=x), the haecceity map;
- K:t→et, K(p)=λz p, the constant-predicate map.

Both are injective by evaluation; for K use the inhabited individual domain. Their injectivity sentences are pure C theorems and can therefore be necessitated. Consequently C has the explicit numerical operations

    F_H:ν_et→ν_e,        F_K:ν_et→ν_t.

Under Max they restrict to arithmetic bijections. Nevertheless neither has an arithmetic inverse represented by an operation. For a putative ν_e→ν_et inverse, its standard values at 2_e,3_e would be 2_et,3_et. Pure Max supplies the possible Fregean singleton-individual world, where 2_e=3_e but et has exactly two entities and hence 2_et≠3_et. NI gives the contradiction exactly as in §34. For a putative ν_t→ν_et inverse, use the possible Fregean world with exactly two individuals: t has two entities, so 3_t=4_t, whereas et has four entities, so 3_et≠4_et.

Thus Max can have an explicitly definable operation that is currently bijective between its numerical domains while its inverse is represented only by a total unique graph. This asymmetry is not a failure of current arithmetic isomorphism and not a need for ordinary set-theoretic choice. It is failure of Plenitude's passage from a unique graph to an intensional operation.

There is also an immediate upward preservation principle: C+□Inj(j)+I_ρ implies I_σ. Otherwise the companion Frege theorem gives a numerical absorbing bottom at σ. Its F_j-image would be a ρ-number fixed by successor, contradicting I_ρ. This statement is about noncollapse I, not an unqualified replacement of I by actual Infinity in bare C.

## 36. Fixed finite individuals, boxed Plenitude and unrestricted arithmetic shadow

The arithmetic conservation result has a useful finite-individual variant. Fix an externally standard m≥1 and any relational counting type ρ. Then

    C+□Plenitude+Exactly_m(e)+{Infinity_a : a relational}

has the same ordinary first-order arithmetic consequences at ρ as the common theory in §33. In particular the result holds with individual monism. This statement does not include I_e or Infinity_e: the target's e-number system is finite with overflow. It concerns arithmetic counted at relational types.

We give the adjustment to §33's construction. Start with the same extensional Henkin Peano structure E, whose number base is B, and use W=B as the S5 world domain. Put A={n∈B:n<m}. Retain the type translation h(e)=e, h(t)=et and h(ab)=h(a)h(b), but restrict the target e-domain to A. Since E function spaces are based on the larger domain B, one must quotient irrelevant values outside the valid target domains rather than silently retaining duplicate functions.

Define valid representatives V and equivalences E_a within the ordinary extensional source E by

    V_e(x):=x<m,             E_e(x,y):=(x=y),
    V_t(p):=⊤,              E_t(p,q):=(p=q in source E),

and use the recursive arrow clauses of §29.2: a valid function takes valid inputs to valid outputs and respects the lower equivalences; its equivalence is pointwise lower equivalence on valid inputs. The target domain at a is V_a/E_a. Notice the crucial distinction at t: its representatives are source world predicates, and E_t is their actual extensional identity in E, not their truth agreement at the current world. Hence target propositions still have genuine S5 variation.

Application descends to these quotients. At world w the truth of a proposition class is p(w), well-defined because E_t is source equality. Boolean operations are pointwise, and target quantifiers range over valid representatives with guards; repeated representatives have no effect. Target identity is the constant-world proposition expressing E_a. The standard formula-invariance and lambda-closure induction from §29 applies with this different truth-sort equivalence. For Logical Equivalence, H-equivalent bodies agree at all valid argument tuples and every w; source extensionality at the truth-predicate level therefore gives E_t, and recursive pointwise equivalence gives equality of the target function classes. Thus this is a C Henkin model with exactly m individuals and full S5 necessity over B.

Plenitude is proved by the same pooling construction as §33.3, with existential quantification guarded by V_b. A unique output means a unique E_b-class. Every selected valid output agrees with a chosen representative on all valid flattened arguments and all worlds. Hence the pooled function belongs to that class; the resulting operation is valid and supplies the target witness. This works at each world and uses only unique fibers, giving □Plenitude without Functional Choice.

For every relational target a the source number base B still injects into its domain: first send n to the world singleton λw(w=n) at t, and then use constant functions at higher relational types. These functions are valid and their target classes are distinct. Every input domain is inhabited because m≥1. Thus images of [0,n) give the finite-cardinality witnesses needed at every relational a.

Define q_a(n) as before, but interpret its bijection clause correctly on quotient domains. A graph R(x,k) between valid a-representatives and k<n must be invariant under E_a; it must assign each valid representative in the selected X-extension exactly one k, attain every k<n, and satisfy R(x,k)∧R(y,k)⇒E_a(x,y). These are fixed E formulas. They say exactly that the quotient extension of X is bijective with [0,n). Therefore q_a(n) is a valid representative at ν_a and respects equivalence of X. The finite deletion/adjunction proofs are unchanged, with deletion of an entity meaning deletion of its whole E_a-class.

There is one typing change from §33.5. The external source index n ranges over all B, while target individuals range only over A. Thus q_a is generally an admitted source E operation, not a target operation with individual input. Nevertheless the target image predicate is admitted: its source definition is

    P(y)(w):=∃n∈B E_{ν_a}(y,q_a(n)).

This is a valid representative at target ν_a t by E comprehension and equivalence invariance. Target N-induction can therefore be applied to P. Together with E induction on n it proves that q_a bijects B with the target number domain. Finite-ordinal pigeonhole proves injectivity, zero and successor are preserved, and hence all first-order arithmetic is preserved. The same injection B→a rules out a finite cardinality of the whole a-domain, so Infinity_a holds for each relational a.

The target's individual domain is the displayed m-element set, independently of this arithmetic bridge. The model transfer preserves arbitrary source arithmetic counterexamples, proving the conservation statement. For m=1 it gives a precise positive comparison with the earlier finite primitive-core result: boxed Plenitude and individual monism coexist with the full common first-order arithmetic shadow at t and all higher relational counting types. The construction makes no Strong Possibility claim; its boxed Plenitude is already incompatible with Max.

## 37. Finite-proof algebra audit for the proposed exact Maximalist arithmetic shadow

This section audits one component of the parent/Frege lane's proposed theorem identifying the arithmetic shadow of Max. It does not itself supply the separate same-ω finite-set-theory interpretation. The construction below avoids assuming an action-model completeness theorem inside that set theory.

### 37.1. A direct completeness source, with its actual version identified

The author-hosted Bacon–Dorr PDF at https://andrew-bacon.github.io/papers/Classicism.pdf is the draft dated **1 July 2022**, not the map's 16 May 2023 draft. In that version §3.1, Theorem 3.2, pp.44–45, gives countable BBK completeness for H; the following paragraph extends it to H-theories. Footnote 64 uses a complete witnessed term theory. Thus it applies directly to C+φ and does not require action-model representation. The 2023 PhilPapers copy was inaccessible during this audit. The ensuing coding and bounded-rank analysis is our explicit application of the elementary completeness method, with the fixed current C framework retained.

### 37.2. Use the original proof predicate, not an unproved FO translation equivalence

There is no need to posit that C is equivalent to a vaguely specified first-order algebra theory. Define a certificate-based proof predicate for the original typed calculus itself. The underlying H axioms and rules have syntactic checks. On a Logical Equivalence line, include a finite H-proof of the required equivalence. For a beta/eta conversion condition, include a finite sequence of permitted local conversions rather than relying on an unanalysed normalization bound. With those certificates attached, checking a finite derivation is primitive recursive. A c.e. enumeration of C axioms suffices as well if enumeration-stage witnesses are included in proofs.

Crucially, C+φ means the H-theory generated by the fixed C axioms and φ. It is **not** the closure under Equivalence of φ-dependent theorems. Logical Equivalence keeps its H-theoremhood side condition. The latter mistaken strengthening would alter the consistency notion appearing in pure Max and invalidate this use of Con(C+φ).

For a fixed pure sentence φ, Con(C+φ), expressed using this original proof predicate, is an ordinary Π₁ arithmetic sentence. When C+φ is externally consistent, it is standard-true. Thus a nonstandard set-theoretic structure with all standard-true Π₁ arithmetic sentences satisfies this particular internal consistency statement. No semantic completeness assertion is inserted into the arithmetic consistency sentence.

### 37.3. Internal countable components need only low-rank coded data

Work inside the supplied set-theoretic structure S, with its own ω, Separation and Replacement, and assume its Con(C+φ). Carry out the typed Henkin completion using a countable stock of fresh constants at every type. At each stage add a fresh witness implication for the next existential formula and decide the next sentence in the direction that preserves consistency. The fresh-constant witness lemma is proved in H by the ordinary quantifier rules. The consistency tests concern the fixed proof predicate with a finite list of extra sentences and are arithmetical. Separation forms the relevant sets of codes; definable recursion on ω forms the sequence of finite decisions. Its union is a complete witnessed theory Γ. No branch through a tree of higher-rank objects and no full hierarchy of powersets is required.

One can keep the resulting model literally countable in S without forming sets of equivalence classes as new domain elements. For every closed typed term code a, let r(a) be the least code b of that type with the identity a=b in Γ. Such a least code exists because a itself qualifies. Let D_s be the codes fixed by r at type s. The relation r and the type-indexed collection of all D_s are subsets of finite Cartesian powers of ω, hence can be coded by subsets of ω. Application is

    app(r(a),r(b)) := r(code(a b)),

well-defined by equality substitution. The truth set consists of those proposition representatives whose formula belongs to Γ. Interpretation of a term with parameters is obtained by simultaneous capture-free substitution of representative closed-term codes, followed by r. Its universal coded graph is again arithmetically definable from Γ; no evaluation by external full function spaces is involved.

The witnessed truth lemma gives the required quantifier clauses, the identity classes give actual identity, and the beta/eta certificates in the theory give the conversion clauses. Fixed C axioms belong to Γ, so this component satisfies C+φ in the BBK sense. Its standard-type domains and standard-formula evaluations therefore form an actual external BBK model when the construction is viewed from outside S, even if S's ω and its term codes are nonstandard. The external verification is ordinary structural induction on each standard formula; it does not require S's internal syntax to be externally well founded.

All component data can be coded by a finite tuple of subsets of ω. This is substantially less set-theoretic resource than the subsequent root construction, which requires actual internal powersets at the finitely many types used by the chosen proof. For finitely many φ_i, repeat the construction finitely many times. Least representatives also provide canonical nonempty component individuals for constant root maps; no additional infinite family of arbitrary choices is needed.

### 37.4. A root can be attached directly to BBK components

Let M_i, i<k, be the resulting components. Put D_e^r=ω^S and choose constant maps π_i^e:D_e^r→D_e^{M_i}. For each relational type τ=σ₁…σ_l t used in the finite proof, define recursively

    D_τ^r := P^S(D_{σ₁}^r×…×D_{σ_l}^r) × ∏_{i<k}D_τ^{M_i}.

For l=0, the first factor is the two-element set of truth values. The displayed powerset is S's powerset, not the external powerset of the possibly nonstandard model. A root entity therefore has an arbitrary admitted current extension and one component entity at each i. The projection π_i selects that component coordinate.

Partial application is not arbitrary. If F has type aτ, apply it to x by taking the current-extension slice at x and the component applications app_i(π_i F,π_i x). This definition guarantees hereditary compatibility of all projections with application. A component may be nonfunctional as a BBK model; no pointwise extensionality for its entities is required.

Interpret each logical constant by its usual root truth condition and by its given component interpretations. In particular root identity is genuine equality of root pairs, while its component coordinates are the components' identity predicates. Interpret a lambda term by its root extension under varying current arguments and by its component lambda interpretations with projected parameters.

The beta equation holds as equality of root pairs: current slices match the substituted body's current extension, and each component beta equation matches its second coordinates. Eta is checked in the same way. All H truth and quantifier clauses hold at the root by their definitions. If an LE certificate proves two bodies H-equivalent, root H-validity makes their root extensions agree, while C-validity in each component identifies their component lambda entities. The root lambda entities are therefore identical. This validates each needed C instance directly, without replacing a BBK component by an action model and without assuming Functionality.

For a pure φ_i true in component i, the i-coordinate of its root proposition is not the component bottom. Consequently its root proposition differs from root bottom. Since ◇φ_i is defined by that distinctness, the root satisfies ◇φ_i. This argument uses only pure closed terms and preservation of component interpretation; it supplies the ordinary Max instances required by the selected finite proof, not Strong Possibility.

### 37.5. Why finitely many powersets suffice for a finite proof

A fixed proof contains finitely many types. Enlarge that set by all subtypes and by the finitely many types occurring in every displayed H-proof or conversion certificate for its C axiom lines. Include also the fixed finite arithmetic-correctness derivations invoked to identify Peano arithmetic and the Sum/Prod graphs in §37.6, and expand the definitions of N_e and its induction. The resulting finite set is closed under every construction actually needed to interpret the proof and its arithmetic bridge. The recursion in §37.4 is then finite. At each step, a finite product, one powerset and a finite product with countable component domains increase a crude finite power/rank bound by only a fixed finite amount. Thus sufficiently many iterated powersets of ω suffice, with a bound depending on this enlarged finite proof.

One does not assert that this bounded set theory supplies the root domains at every possible C type simultaneously. It supplies a structure for every sort and term used in the fixed proof, including the certificates validating its axioms. That is exactly what the finite soundness argument requires. Component models at all coded types are cheap because they are countably coded; the root's internally full current extensions are the part that consumes the finitely many powersets.

### 37.6. The root's e-arithmetic and the remaining dependency

For arithmetic counted at e, no extra component with infinite propositions is necessary. Root individuals already form ω^S. Let z=0_e and let s be the root successor operation. Replacement applied to finite recursion forms the sequence a_n=s^n(z) for n∈ω^S and its range O⊆D_{ν_e}^r. The root domain at ν_e t has every S-subset of D_{ν_e}^r as a current extension, so O is represented by an admitted root predicate. It contains zero and is successor closed, giving N_e⊆O by the definition of N. Conversely induction in S on n proves N_e(a_n), so N_e=O currently.

The a_n are distinct inside S. At the current root, a_n counts exactly the n-element subsets of ω^S, by finite-cardinality induction; the initial segment [0,n) distinguishes different n by finite pigeonhole. The same finite combinatorics identifies the Frege addition and multiplication graphs with S's ordinary arithmetic. Thus the root's current e-arithmetic is ω^S, including its nonstandard numbers, and preserves the chosen arithmetic counterexample. This is the precise place where the internally represented numeral-orbit set is used; external standard numerals are not substituted for it.

The audit therefore closes the typed-consistency-to-component-model and finite-root-algebra steps of the proposed upper bound on Max's arithmetic shadow. The separate dependency is the parent/Frege lane's theorem providing, from the relevant current arithmetic model, a same-ω model S with enough finite powersets and the required true Π₁ statements. Only after that dependency and the lower bound are combined should the exact-shadow theorem be stated. No additional completeness for action models is needed for the argument audited here.

## 38. Pure Maximalism forbids a numerical predecessor operation at every type

This is a single-counting-base arithmetic obstruction, stronger in simplicity than the cross-base examples of §§34–35. Fix any admitted counting type σ, put ν=ν_σ, and define

    PredOp_σ := ∃f^{νν} ∀n^ν [N_σn→f(S_σn)=n].

Only the left-inverse equation is required; imposing the additional usual equation f(0_σ)=0_σ would strengthen the demand. All types are admitted because ν is relational.

**Theorem.** C proves PredOp_σ⇒I_σ. C+Plenitude proves I_σ⇒PredOp_σ, with f0=0 available as well. Pure Max proves ¬PredOp_σ, although it proves I_σ. Consequently Max refutes the individual Plenitude instance with both input and output type ν_σ, at every fixed σ.

The first implication is immediate: if S_σn=S_σm for numbers n,m, apply f and use its two equations to get n=m. Thus numerical successor is injective, which is I_σ (or the equivalent I*_σ convention).

For the positive implication, C induction proves that every number is either zero or the successor of a number. Under I_σ that predecessor is unique. Define the total relation on all of ν by

    U(x,y) :=
      [N_σx ∧ x≠0_σ ∧ N_σy ∧ x=S_σy]
      ∨ [(¬N_σx ∨ x=0_σ) ∧ y=0_σ].

Its current totality and uniqueness follow from the preceding numerical facts, and its value at zero is zero. The Plenitude instance at (ν,ν) yields an operation f realizing U. Since S_σn is a nonzero number whenever n is a number, its U-output is n, proving PredOp_σ. Without Plenitude the displayed U is still the admitted canonical total unique predecessor graph under I_σ.

For the Maximalist failure, choose the full one-world Henkin model with one individual. At the fixed type σ its domain has some positive externally standard finite size m. In that model the following closed pure sentence is true:

    ψ_σ := ((m+1)_σ=(m+2)_σ) ∧ (m_σ≠(m+1)_σ).

Indeed the two higher cardinalities are empty, while m_σ counts the universal σ-property. This verifies C-consistency of ψ_σ directly; one need not prove that a short description of the model determines the cardinalities of every type. Pure Max therefore gives ◇ψ_σ.

Suppose f witnessed PredOp_σ at the current point. Every fixed standard numeral belongs to N_σ already in C, so f satisfies

    f((m+1)_σ)=m_σ,
    f((m+2)_σ)=(m+1)_σ.

NI makes each of these two actual identities necessary. At the possible ψ_σ point, equality of their inputs forces equality of their outputs, contradicting the other conjunct of ψ_σ. Thus no such f exists. This argument uses only two fixed numeral values, ordinary pure Max and NI. It does not box the universal predecessor condition, invoke BF, add parameterized possibility, or presume Strong Possibility.

Because Max supplies I_σ, the graph U above is a current total unique graph there. Its failure to have an operation witness explicitly refutes P_{ν_σ,ν_σ}. The contrast is therefore mathematically narrow: ordinary Peano predecessor exists as a definable graph, while the corresponding intensional operation is unavailable. Boxed Functional Choice with the relevant actual Infinity supplies the operation through its Plenitude consequence. No claim is made that the lack of an operation destroys the current relational arithmetic interpretation.
