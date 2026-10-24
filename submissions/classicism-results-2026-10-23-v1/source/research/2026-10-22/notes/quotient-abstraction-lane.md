# Quotients, canonicalization, and an extensional retract of C

Research notes, 22 October 2026. Original arguments below; no novelty claim and no human checking claimed. No database or Lean edits. The standing framework is C in the fixed relational type system. Types with output e are never introduced. Statements called boxed close all object variables before the box; proofs from optional premises are not necessitated without discharge.

## Ranked reading index and final status

1. **Existing conjecture resolved by a new collaborative argument:** C + RC + BC implies TC; at σ, RC_{σt,σt} and BC_{σt} suffice. The complete proof is in `.reproduction/classicism-research/relational-choice-boolean-completeness-transversal-proof.md`. Sections 14–15 below audit its graph Bourbaki–Witt step and sharpen BC to well-ordered chain completeness. Directed completeness equals full BC already in C.
2. **Transparent quotient characterization and countable strengthening:** Actuality is principality of Null_ρ at any one relation type (§18). Under CBC_{κ,t} alone, it is also equivalent to Null_ρ having an admitted κ-countable cofinal family (§19, strengthened in §19.4). The latter uses no RC; its internal recursion and countability transfers received an independent extension-lane audit. Section 21 further proves, type-locally, that an internally countable Boolean type with countable completeness is internally finite already in C, without I_κ or RC (§21.3). The unconditioned finite/countable-complete characterization in §21.1 retains I_κ for its converse countability assertion.
3. **Progress on RC alone, with limits preserved:** finite-cell TC, finitely many exceptional infinite cells, and CBC_{κ,σt}+ND_σ for countable cells (§§13,17). The unrestricted implication RC⇒TC remains unresolved here. Exact coherent-choice and quotient-invariant-choice formulations appear in §§16.1,20.
4. **Language-resource boundary:** unbounded parameterized infinitary lambda comprehension plus C5 gives full S5 representation, whereas every fixed regular bounded infinitary arity admits the support countermodels (§§5,8,10–11). A single pure countable term standardizing Frege numbers already obstructs original Maximalism under the specified semantic extension; an explicit omega-rule version is separate (§12). These are extensions of the language/proof resources, not contradictions in original finitary Maximalist Classicism.
5. **Structural interpretation:** Actuality/quotient-operation equivalences (§§1–2), the normalized operation core under □FC (§4), atom-profile/world exactness (§6), and stable quotients (§9). The weaker relational core under TC (§16) is a parameterized Henkin interpretation, not a claim of external full powersets.

All new claims are ordinary mathematical proofs or explicitly marked semantic constructions. No human verification, Lean status, or novelty is asserted. This lane edited only this scratch report; original records were preserved.

## 1. Actuality is exactly operation-valued extensional canonicalization

Write X ≈ Y for actual coextension. For a fixed type σ define

EC_σ: there is K:(σt)→(σt) such that, for every X,Y:σt,
KX≈X and (X≈Y → KX=KY).

The converse implication KX=KY → X≈Y follows from the first clause. This is a canonicalization OPERATION, not merely a property containing one representative per coextension class. Each EC_σ, including σ=e, is equivalent over C to Actuality (assuming the standing nonempty type domains).

Forward proof from Actuality. Let w be true and entail every actual truth. Define KX:=λz.(w∧Xz). It is coextensive with X. If X≈Y, Actuality applied to the true proposition ∀z(Xz↔Yz) gives □(w→∀z(Xz↔Yz)). Consequently KX and KY are necessarily coextensive, hence identical by Intensionality. No choice and no Plenitude is used.

Converse. Given EC_σ, put c_p:=λz^σ.p and f(p):=K(c_p). Since σ is nonempty, c_p≈c_q iff p↔q. Since K preserves extension, f(p)=f(q) iff p↔q. Let T(p):=(f(p)=f(⊤)). Then ∀p(Tp↔p). NI makes T a persistent truth predicate: C proves □∀p(Tp→□Tp). Set a:=∀p(Tp→p), which is true. For each true p, Tp, hence □Tp by NI; the theorem a→(Tp→p), transported under the box, yields □(a→p). Thus a entails every truth and witnesses Actuality.

The same proof works for any finite argument tuple, including the nullary propositional case.

The cut K_w has additional algebraic structure for free: necessarily K_w²=K_w, K_w preserves finite meets, joins, and bottom; its image consists exactly of the relations Y satisfying Y≤λz.w. Relative complementation in that image is Y↦λz.(w∧¬Yz), and its top is λz.w. K_w identifies precisely actual coextension classes. Thus Actuality realizes the actual extension quotient as a Boolean corner, rather than as the ambient Boolean algebra. The modal scope of the algebraic identities follows from C's Boolean identities with parameter w; extension-preservation and kernel exactness are actual-point claims.

## 2. Identity-kernel quotient abstraction is also exactly Actuality

QA_σ says: every actual equivalence relation R:σσt has q:σ→(σt) with

∀x,y ((Rx)y ↔ qx=qy).

The all-type schema QA is equivalent over C to Actuality. Actuality gives qx:=K_w(λz.(Rx)z). Equivalent points have coextensive rows and hence identical q-values. Conversely qx=qy gives coextensive rows; reflexivity, symmetry, and transitivity recover Rxy.

For the reverse implication only σ=t and the single equivalence relation R(p,q):=(p↔q) are needed. Let T(p):=(qp=q⊤), and use the preceding persistent-truth-predicate proof. Do not claim QA_e alone implies Actuality: on a singleton individual domain every equivalence relation on individuals is trivial.

Equivalent reformulation: every actual equivalence relation is coextensive with a persistent, necessarily equivalence relation. From QA use the kernel E(x,y):=(qx=qy); its equivalence axioms and persistence are C theorems. Conversely the truth-equivalence instance and E(p,⊤) supply a persistent truth predicate. This version does not need operation codomains in its wording.

Consequences with exact scope:

* EC and QA are consequences of Plenitude, hence of □Functional Choice. They are not strict additions to that benchmark.
* Their boxed schemata are equivalent to □Actuality. The forward and reverse C-derivations are first discharged, then necessitated instancewise. No illicit boxing of Actuality occurs.
* Unboxed QA/EC are compatible with pure Maximalism: the recorded coalesced maximalist root satisfies Actuality. Their boxed forms are incompatible with pure Maximalism, by the recorded incompatibility with □Actuality.
* QA/EC do not imply Strong Actuality: the full two-object double-retraction model satisfies Actuality and refutes Strong Actuality.

A useful universal-property consequence under Plenitude: if q codes R as above and h:σ→τ is actually constant on R-classes, τ≠e, then h factors on the q-image through an operation from σt to τ. Define the graph on code A by the unique h-value of an x with qx=A, and use ⊥_τ outside the q-image. It is total and single-valued; Plenitude supplies its operation. This is a consequence, not a new strengthening. The uniqueness of the factor is only on the q-image. Without Plenitude this argument establishes no operation-valued factorization.

## 3. Why the naive quotient of the whole type hierarchy fails

Actual coextension is not a congruence for arbitrary higher-order application. If a≈b but a≠b, the predicate F:=λx.(x=a) distinguishes them: Fa is true and Fb false. Therefore the assertion

for every predicate F:τt, a≈b implies Fa↔Fb

at every relational τ is equivalent to ambient Extensionality. The reverse direction is substitution of actual identicals. Thus a proposal to quotient every type by actual coextension and simply inherit ALL application is exactly the strong Extensionality proposal, not a harmless quotient construction.

Explicit countermodel already at C+□Functional Choice: take two worlds W={0,1}, D_e a singleton, D_t=P(W), and D_{στ}=all set-functions D_σ→D_τ. Interpret identity crisply, connectives as Boolean operations, quantifiers by meets/joins; evaluate at 0. Every type domain is finite, so full function domains validate Functional Choice at both worlds and hence its box. Let p={0}; p and ⊤ are actually coextensive but distinct. The identity predicate above separates them.

This model is the elementary finite Boolean-valued version of the map's full non-extensional S5 examples. Direct verification: H-equivalent formulas have identical Boolean values under every assignment, so Logical Equivalence holds; crisp identities give □ND; the full function domains supply actual choices at each of the two designated evaluations.

## 4. A recursively normalized classical extensional hierarchy

This is the main structural result. It is an INTERNAL/HENKIN interpretation, not a theorem that all external powersets exist.

Use the parent lane's independently established bivalent-evaluation lemma: ND+Actuality is equivalent to the existence of b:tt such that

p → bp=⊤, and ¬p → bp=⊥, for every p.

All the following is available under □Functional Choice. For the basic unboxed retract construction it suffices to assume such b and Functionality; choices use the corresponding unboxed choice axioms. Every b-value is ⊤ or ⊥, and b fixes both.

Recursively define normalizations r_τ. At e, r_e(x)=x is METALANGUAGE notation only; there is no ee-typed object. At t, r_t=b. At an admitted arrow type στ (τ≠e), define

r_{στ}(f):=λx^σ.r_τ(f(r_σx)).

Every displayed operation has a permitted relational output. For σ=e the inner r_σx is just x.

### 4.1 Idempotence

Inductively r_τ(r_τx)=r_τx. At t this follows because b fixes its two possible outputs. At στ, for each x,

r_{στ}(r_{στ}f)(x)
= r_τ(r_τ(f(r_σ(r_σx))))
= r_τ(f(r_σx))
= (r_{στ}f)(x).

The two induction hypotheses justify the middle equality; Functionality identifies the operations. Put E_e(x):=⊤ and E_τ(x):=(r_τx=x) otherwise. Every r_τx belongs to E_τ. The propositional fixed points are exactly ⊥ and ⊤.

### 4.2 Characterization of the fixed operations

A fixed f:στ has, for every raw x,

f x = r_τ(f(r_σx)).

Consequently all its outputs are fixed and f x=f(r_σx). Conversely those two properties imply f=r_{στ}f by Functionality. This is a transparent alternative definition of the core arrow domains: operations that land in the output core and depend only on the input's normalization.

If f,g are fixed and agree on all fixed inputs, then for any raw x,
f x=f(r_σx)=g(r_σx)=g x.
Functionality gives f=g. Thus core functions are extensional on core arguments. Application of a core function to a core argument stays in the core.

More generally r_{στ}h is the unique core operation whose value at each core x is r_τ(hx). This is an exact normalization property, not unrestricted functoriality: normalizing arbitrary composable raw maps need not commute with composition. It does commute for maps that already carry core inputs to core outputs.

### 4.3 Interpretation of ordinary extensional relational HOL

Interpret each type by E_τ, application by its restriction, and truth by the two actual truth values ⊥,⊤. Logical operations are their ordinary operations on those values, represented by their normalized raw operations. Equality is actual equality restricted to the core; its characteristic predicate is normalized. Quantifiers range over E_σ, e.g. the universal formula is represented by

b(∀x^σ.(E_σx → A(x))).

This normalization has value ⊤ exactly when every core x satisfies A. Lambda abstraction is interpreted by normalizing a raw abstraction. On a core argument x, the outer output normalization does nothing because the translated body is already core; hence beta holds. Eta and functional extensionality follow from core extensionality above. Recursive translation gives a core-valued denotation to every term, with all object quantifiers relativized to E. This proves comprehension for every definable core relation, with parameters, and the ordinary classical extensional relational HOL axioms.

There are no new types σ→e: the interpreted logic is the fixed relational type system. One could encode such functions by functional relations, but that is a separate coding convention and is not used here.

### 4.4 Choice transfers into the core

Let R be a core relation serial on core inputs and core outputs. For relational output τ, form the raw serial relation

U(x,y):=E_τ(y) ∧ R(r_σx,y).

Raw Functional Choice gives h with U(x,hx). Its normalization f=r_{στ}h is core and, on every core x, fx=r_τ(hx)=hx. Therefore R(x,fx). Thus Functional Choice transfers to the internal core.

For Relational Choice, including individual outputs, apply raw Relational Choice to the same U, then normalize the selected functional relation at its relational type. On core arguments this preserves its actual truth extension, and the selected y already lies in the core. Hence totality, uniqueness, and containment transfer. Boxed Functional Choice provides both requisite unboxed choices.

### 4.5 Scope, uniqueness, and fullness caveats

The construction proves an internal extensional higher-order hierarchy with definable comprehension and choice. It does NOT prove that its predicate domains contain every external subset. If the ambient model is extensionally full at the evaluation point, then every external graph between core sets can first be represented as a raw relation; Plenitude and normalization then give every external core function. Only with this EXTRA semantic fullness hypothesis is the core externally full.

Under Functionality, the bivalent evaluator b is unique: any two agree pointwise by the two truth cases, so Functionality identifies them. The recursively defined normalizations therefore introduce no arbitrary choice once an actual evaluation is fixed. Nevertheless b need not remain an evaluator of the CURRENT truth at another world. Do not infer ∃b□∀p(bp↔p). That stronger assertion would collapse modality.

A useful stability refinement under □Functional Choice: the range assertion ∀p(bp=⊤∨bp=⊥) is necessary. Each disjunction of identities persists by NI, and BF moves the universal quantifier under the box. The endpoint identities persist by NI. The retraction equations can likewise be expressed as operation identities and then persist by NI. Thus the transported retractions still supply two-valued algebraic cores; the special fact that normalization preserves EVERY ambient proposition's current truth is tied to the original evaluation point.

In the explicit two-world full model above, raw cardinalities satisfy m_e=1, m_t=4, m_{στ}=m_τ^{m_σ}. The extensional core has n_e=1, n_t=2, n_{στ}=n_τ^{n_σ}; in particular raw tt has 256 elements while core tt has four. This gives a concrete model of a classical extensional core inside a genuinely non-extensional modal ambient structure.

## 5. Audit of the parent's infinitary fullness proposal

The proposal is sound with the following precise new resource. Enrich the model's language by arbitrary SET-indexed disjunctions, allowing an arbitrary set-sized family of parameters in each formula, and require the ordinary pointwise truth clause for those disjunctions. This is stronger than any fixed bounded L_{κ,ω} closure. It is a language/semantics extension, not a consequence of finitary C.

For a set-sized model of C+□Plenitude with that closure:

1. At every type, χ_S(x):=∨_{a∈S}(x=a) defines each external subset S of the actual domain. Identity is crisp by NI+ND. No choice is needed to enumerate S: the indexing set is S itself.
2. Every external graph of a set-function f:D_σ→D_τ is thereby a relation in the domain. Plenitude supplies an operation realizing it when τ≠e. Functionality supplies uniqueness. The evaluation map D_{στ}→(D_τ)^{D_σ} is therefore bijective.
3. The recorded Boolean Completeness consequence of □Plenitude, now applied to characteristic predicates of every external subset of D_t, makes D_t EXTERNALLY complete. This avoids any unproved exchange of infinitary meets with Box. Atomicity makes it externally atomic. Therefore D_t is isomorphic to P(W), W its set of atoms.
4. Actuality says the designated true propositions form the principal ultrafilter at one atom w∈W.
5. Quantification is external meet. Universal instantiation gives ∀xFx≤Fa for each a. If p≤Fa for every a, then ∀x□(p→Fx); BF gives □∀x(p→Fx), and hence p≤∀xFx. So ∀ is exactly the meet, with ∃ its dual.

Consequently the pointed algebraic model is isomorphic to a full constant-domain S5 INTENSIONAL hierarchy: D_e an arbitrary nonempty set, D_t=P(W), D_{στ} all set-functions D_σ→D_τ, crisp equality, Boolean connectives, meet/join quantifiers, evaluated at w. It is not an extensional hierarchy: W can have multiple atoms. The retraction theorem above then supplies an externally full classical extensional core at each designated atom.

No metatheoretic Choice is needed for this representation. In ZF, do not infer Functional Choice merely from full function domains: selecting from an arbitrary externally serial relation can require Choice. Conversely, full hierarchies with ordinary set-indexed pointwise infinitary connectives satisfy the stated closure. Proof-rule formulations of the infinitary extension must separately guarantee these semantics; merely adding symbols named big conjunction is insufficient.

## Recorded inputs actually consulted

* topic.yaml and background.md: fixed relational types, C, NI/Intensionality conventions, theoremhood and boxing scope.
* actuality-implies-transversal: Sun's actual-world cut construction, with the recorded Intensionality source locator Classicism §1.5, pp.16–18.
* persistent-comprehension-r-implies-actuality: Classicism §2.3, notes 38 and 40, p.29; persistent truth predicate proof.
* necessary-plenitude-r-implies-necessary-actuality; necessary-plenitude-r-implies-necessary-distinctness-necessary-r; c5-and-completeness/atomicity connections.
* coalesced-maximalist-root; full-two-object-double-retraction; full non-extensional S5 examples.
* Engine(load_topic('classicism')) used with proved-only results/models and no optional engine background. It confirms □FC entails □BF, □Functionality, □Boolean Completeness, □Strong Leibniz, □Transversal Choice, and □Intensional Choice; Extensionality is separated by full S5/group models. It confirms Maximalism excludes □Actuality but is compatible with Actuality at the coalesced root.

All quotient/canonicalization equivalences, the recursive hierarchy argument, and the infinitary representation audit in this note are newly written arguments for this research session. They should be attributed to misc if integrated, with source records serving only as the explicit background inputs above. No literature novelty claim is made.

## 6. A strict simple strengthening: exact qualitative worlds

This section complements the parent's UQV and the extension lane's complete-homomorphism theorem. Work over □Plenitude, and fix R:et. Put

F_R(a):=λx^e.□(a→Rx),     Q_R(X):=∀x^e.(Rx↔Xx).

For each atom a, F_R(a) is rigid. For rigid X,

    a≤Q_R(X) iff F_R(a)=X.                         (Profile lemma)

Forward is the parent's argument: a≤Q gives agreement with X pointwise because X's instances are settled; rigid coextension gives identity. Reverse: for every x, an atom a decides Rx. If a≤Rx then (F_Ra)x is necessarily true; otherwise a≤¬Rx and (F_Ra)x is necessarily false. Thus a≤(Rx↔(F_Ra)x) for every x; BF gives a≤Q_R(F_Ra). Substitute F_Ra=X.

World individuation WI_R means F_R is injective on atoms. In direct terms, two atoms agreeing on every R-instance are identical. Existence of such R is equivalent to an injection of the atoms into the rigid individual profiles: one direction uses F_R; for the other, from an injective assignment F define Rx:=∃a(Atom(a)∧a∧(Fa)x). At atom b, its profile is exactly Fb by the unique-true-atom argument. This is the reverse construction of the parent's WP theorem, without surjectivity.

### 6.1 The simplest exact-profile formulation

    EQW_e : ∃R^{et} ∀X^{et}. Rigid(X) → Atom_t(Q_R(X)).

Read: every complete qualitative specification is a possible world. This is equivalent to a bijection a↦F_R(a) between atoms and rigid individual profiles.

If every Q_R(X) is an atom, then a≤Q_R(F_Ra) implies a=Q_R(F_Ra). Thus equal profiles force equal atoms. Conversely, for each rigid X take the atom a:=Q_R(X); the profile lemma gives F_Ra=X. For the other direction, suppose F_R is bijective. For rigid X let a be its unique preimage. The profile lemma gives a≤Q_R(X). Any atom b below Q_R(X) has F_Rb=X, hence b=a. Atomicity then gives Q_R(X)=a: otherwise Q_R(X)∧¬a has a different atom below it. Thus Q_R(X) is an atom.

This is a genuine strengthening of T=C+□Functional Choice. In the standard full model it says exactly W≅P(D), with R the membership-coordinate field. D=N,W=P(N) is an infinite consistent example. For D a singleton and W three points, UQV holds but WI and EQW fail. For D two points and W two points, WI holds but UQV and EQW fail. D singleton,W two points satisfies EQW. These finite examples require no metatheoretic choice.

WI_t, unlike UQV_t, is already true under □Plenitude: use R(p):=p; distinct propositional atoms are distinguished by a proposition (take one of those atoms). Hence it is the restriction to individual qualitative data that makes WI_e substantive.

### 6.2 Combining separately witnessed possibility and individuation

Under T, UQV_e together with WI_e implies EQW_e even if the original witnesses are different. UQV supplies a surjection from atoms B to rigid profiles A. Functional Choice supplies a section i:A→B, an injection. WI supplies j:B→A, an injection. All relevant output types are relational, so the operations are admitted.

For completeness, internal Schröder–Bernstein needs no natural-number type. Put A0:=A\j(B); let L be the least subset of A containing A0 and closed under j∘i, defined as the intersection of all such properties by ordinary impredicative comprehension. Then

    L = A0 ∪ j(i(L)).

The right side is contained in L, contains A0, and is closed under j∘i, so leastness gives equality. Define a graph h:A→B by h(a)=i(a) on L and h(a)=the unique b with j(b)=a off L. The latter b exists because a∉A0. The two pieces have disjoint images: i(a)=b with a∈L would put j(b)=j(i(a)) in L. Each piece is injective. For b∈B, if j(b)∉L it is hit by the second piece; if j(b)∈L then j(b)∉A0, so the displayed equality and injectivity of j give b=i(a) for some a∈L. Thus h is bijective. Default values outside A/B totalize the functional graphs, and Plenitude represents h and its inverse. The resulting bijection from atoms to profiles gives one EQW relation by the usual atom-indexed construction.

All this concerns actual extensions and identities; no extensionality of arbitrary raw properties is assumed.

### 6.3 Individuation is qualitative supervenience / generation

For fixed R, WI_R is equivalent over □Plenitude to:

for every proposition p, some rigid Y:(et)t satisfies

    p = ∃X^{et}. Rigid(X) ∧ YX ∧ Q_R(X).             (Generation)

Thus every proposition is a rigid classification of R's complete qualitative state. The rigidity of Y is essential: allowing arbitrary Y would let it encode p contingently and trivialize the claim.

Atom-evaluation lemma: for rigid Y and atom a, the right side of Generation is entailed by a iff Y(F_Ra). Each rigid instance YX is settled. The profile lemma identifies the unique rigid X that can match R under a. Formally, atoms are completely prime for object-language existential joins: if a≤∃xφ(x) and no x has a≤φ(x), atomicity gives a≤¬φ(x) for every x; BF then gives a≤¬∃xφ(x), contradiction. This justifies selecting the profile under a without any illicit interchange of actual and possible witnesses.

If WI_R holds, rigidify the predicate

    Y_p(X):=∃b. Atom(b) ∧ F_Rb=X ∧ b≤p.

(Alternatively it is already rigid because its formulas are built from settled identities and quantifiers under □BF.) Its actual value at F_Ra is exactly a≤p, by injectivity. The atom-evaluation lemma shows Generation's right side and p have precisely the same atoms below them; Atomicity gives their identity.

Conversely if Generation holds and F_Ra=F_Rb, the atom-evaluation lemma makes a and b agree on every p. Taking p=a gives b≤a, hence a=b. This proves WI.

The extension lane proves the complementary universal property: fixed-R bijective profiles are equivalent under T to unique extension of every assignment of individual generators into every internal complete atomic Boolean algebra B_τ to a complete homomorphism. This is not a freeness theorem for arbitrary atomless external complete Boolean algebras.

## 7. Countable infinitary comprehension already excludes original Maximalism

This is a SEMANTIC language-extension theorem, not a contradiction of the original finitary C or a claim of a uniform infinitary proof without a specified complete proof system.

Assume a set-sized intended intensional model of C is closed under countable conjunctions/disjunctions with countably many parameter constants and under lambda abstraction of the resulting formulas. Connectives have their ordinary pointwise truth clauses, and parameters transport coherently. Such formulas still have only a finite tuple of free argument variables; the countable family can be named by parameter constants. Ordinary full S5 models satisfy this closure, so it is consistent with T.

### 7.1 Standardizing the internal finite-cardinality domain

Fix a type σ and its Frege number type ν_σ=(σt)t, zero and successor from Background. The predicate

    P(Z):=∨_{n<ω} [Z=Suc_σ^n(0_σ)]

exists by countable infinitary comprehension. At the evaluation point it contains zero and is successor-closed: if Z is the n-th numeral, Suc Z is the (n+1)-th. Impredicative FiniteCardinality, being contained in every such inductive property, is contained in P. Conversely each standard numeral belongs to FiniteCardinality by ordinary finite induction. Thus its actual extension is exactly the externally countable set of standard numeral denotations. Numerals may coincide in a finite or degenerate instance; that does not affect countability.

### 7.2 Internal countability becomes external countability

Suppose Ctbl_{σ,τ}(X), witnessed by R. For every actual y with Xy, the y=y case of the counting condition supplies a numeral n with Ryn. Assign y the LEAST external integer k for which R(y,Suc_σ^k 0_σ) holds. If two X-members receive the same k, they share a number and the counting condition says they are identical. Thus the actual extension of X injects into ω. This uses least integers, not the metatheoretic axiom of choice.

### 7.3 Countable joins supply the required LUB

Enumerate that extension by its integer tags as a finite or countable family (y_k)_{k∈I}, I⊆ω. For relational τ=ρ1…ρn t, including n=0, define

    L:=λu1…un. ∨_{k∈I} y_k[u1,…,un].

At every accessible point and argument tuple, this is the pointwise disjunction of the transported parameters. Hence each y_k≤L. If z is an upper bound for every actual X-member, then y_k≤z for every k; pointwise disjunction gives L≤z. Thus L is the required internal least upper bound. Future new X-members are irrelevant: the source definition of LUB refers to the actual extension of X. No BF or ND is used.

Therefore Countable Boolean Completeness holds at every point, and in particular holds unboxed. The proved local record `possibility-and-countable-boolean-completeness-incompatible` (Goodsell, Arithmetic is Necessary, draft 5 June 2024, Theorems 9 and 11, §§4–6, pp.19–26) states that pure Maximalism plus this principle is inconsistent. Consequently original Maximalism, with reference theory fixed to finitary C, has NO model with the above countable infinitary-comprehension closure.

This is stronger and more economical than requiring arbitrary set-sized conjunctions. It isolates a concrete obstruction: once the finite-cardinality domain contains only the genuine standard numeral values, ordinary countable Boolean completion is incompatible with original Maximalism. A maximalist model must evade such closure/standardness assumptions. Changing the Maximalism side condition to a new reference theory C_∞ is a different proposal and is not assessed by this argument.

## 8. Unbounded infinitary truth-pattern cells

With arbitrary set-indexed parameter conjunctions, one obtains stronger semantic facts WITHOUT □Plenitude, BF, or ND.

At any point w, conjoin all propositions in that point's domain that are true there. The index family is a set. The conjunction is true at w and necessarily implies every conjunct, so it witnesses Actuality. Repeating the construction at every accessible point gives □Actuality.

For Atomicity at the root, let p be nonzero and choose an accessible evaluation v where it is true. For every ROOT proposition q, select q if true at v and ¬q otherwise; take their conjunction a. It is true at v, hence nonzero; it entails p, and for every root q entails q or ¬q. Therefore a is a root Boolean atom below p. Importantly the conjunction uses root propositions only: new propositions at v do not need to be pulled back.

At a relational type τ, choose an accessible argument tuple at which a non-bottom root relation R is true. For each root relation Y choose the literal Y or ¬Y according to its value there, and lambda-abstract the pointwise conjunction over that family. The result is non-bottom, below R, and settles every root relation. It is an atom of the root relational Boolean algebra. Repeating at every point gives boxed all-type Atomicity.

These arguments require the ordinary truth-condition semantics for infinitary connectives, closure under infinitary lambda abstractions, set-sized domains, and the usual intensional fact that a non-bottom relation has an accessible instance. They are semantic representation arguments; no proof-system completeness is silently assumed.

## 9. Exact modal scope of quotient representation

There is a useful theorem in BARE C. If □Equiv(R), the ordinary row map q_Rx:=λz.(Rx)z satisfies

    □∀x,y [q_Rx=q_Ry ↔ □(Rx)y].

An identity of rows gives necessarily equal values; necessary reflexivity then gives □Rxy. Conversely □Rxy and □Equiv(R) make the rows necessarily coextensive, so Intensionality identifies them. To obtain the displayed outer box, first derive the unboxed implication as a C theorem, discharge its premise □Equiv(R), necessitate that theorem, and use 4. No BF is required.

Consequently, under □Equiv(R),

    ∃q □∀x,y [(Rx)y↔qx=qy]    iff    Persistent(R).

An identity kernel is persistent by NI; the row map supplies the reverse implication. Thus the ordinary row construction quotients the NECESSARY core of a necessarily equivalence relation. Necessary equivalence alone does not make current equivalence the kernel of a stable operation.

In particular, over T the schema saying EVERY necessarily equivalence relation has such a stable exact quotient is equivalent to Extensionality. For necessity, take R_p(x,y):=(x=y∨p) on type t. C proves □Equiv(R_p). Comparing ⊤ and ⊥ in a stable quotient makes p necessarily equivalent to an identity, hence p→□p. This collapses all propositions and entails Extensionality under T. Conversely T+Extensionality supplies its necessitation (No Pure Contingency for each closed pure instance), and row maps give the required stable quotients.

A stronger choice-free factorization theorem is also available in bare C. For q:σρ and h:στ, with relational ρ,τ, if

    □∀x,y [qx=qy→hx=hy],

put k(u):=λv̄.∀x(u=qx→(hx)[v̄]), where τ=v̄t. At u=qx0 the fibre is nonempty (x0) and all its h-values are necessarily identical by the premise. Thus k(qx0) is necessarily coextensive with hx0, so Intensionality gives the identity; the boxed hypotheses and 4 give □∀x k(qx)=hx. If q is necessarily onto, Modalized Functionality gives uniqueness of k. This is the stable universal property; it does not require Plenitude.

Actual kernel inclusion is insufficient. In the recorded full two-object chain, let w be the singleton of the root identity arrow and q(x):=λz(w∧z=x), for x,z:t. Actuality makes q actually injective. Let h be the identity on t. There is no k with ∀x k(qx)=x: after the one-way arrow w becomes bottom, so q⊤ and q⊥ coalesce, whereas ⊤ and ⊥ remain distinct. The two hypothetical factorization identities persist by NI, contradiction. This model has □Actuality, so even necessary availability of local quotients does not give this universal property for every chosen quotient operation. The construction is `full-two-object-chain` (Classicism §3.5, p.59, fourth paragraph; p.61).

## 10. A countably supported model separating countable from arbitrary closure

This is an original construction written out here, not a claimed published theorem. Work in ZFC. Let I=ω1×{0,1}, W=P(I), and G=Sym(I), acting on worlds by A↦g[A]. An object has countable support if some countable S⊆I has the property that every permutation fixing S pointwise fixes the object.

Take D_e=N with trivial G-action. Let D_t be all countably supported subsets of W. Recursively, D_{στ} consists of all countably supported set-functions f:D_σ→D_τ, under the action (gf)(x)=g(f(g^{-1}x)). Every type domain is a set and is G-invariant. No functions ending in e are introduced.

Interpret Boolean operations pointwise, identity crisply (W for equality, ∅ otherwise), application ordinarily, and quantifiers by pointwise intersections/unions over the corresponding type domain.

### 10.1 Closure and soundness

Finite Boolean operations preserve countable support. If a predicate P:D_σ→D_t is fixed by the pointwise stabilizer of S, then its intersection ∩_{x∈D_σ}P(x) is fixed by that stabilizer: it permutes the domain and carries P(x) to P(gx). Hence quantifier outputs lie in D_t, and the quantifier operations themselves are equivariant (empty support). The same argument validates the logical constants at their curried types.

For countably many parameters choose countable supports and take their countable union. A term or infinitary formula formed from those parameters is equivariant under that union's stabilizer, by induction using application, Boolean operations, quantifiers, and lambda abstraction. Its denotation therefore belongs to the appropriate type domain. Countable parameterized conjunction/disjunction and lambda comprehension are available. ZFC is used here for the countable union/support choice; no choice-free claim is made for this construction.

The ordinary H axioms are pointwise valid; equality is actual equality of denotations, and beta/eta hold for set-functions. H-equivalent formulas denote the same subset of W under every assignment, so their abstractions denote the same functions: Logical Equivalence holds. This is a model of C, and also of the stated countable infinitary extension.

Crisp equality validates □ND. BF holds because ∩_x P(x)=W iff every P(x)=W; both sides of BF consequently have the same crisp value. The countable-comprehension theorem of section 7 gives Countable Boolean Completeness at all types. The finite-cardinality domains are standard numeral denotations.

### 10.2 Failure of Actuality and Atomicity

For each i∈I, the coordinate proposition C_i:={A⊆I:i∈A} has support {i}. These propositions separate distinct worlds, so any Boolean atom in D_t must be a singleton {A}. Such a singleton has countable support exactly when A is countable or cocountable. Indeed if S supports {A}, every permutation of I\S preserves A\S, so that set is either empty or all I\S; conversely A or its complement is a support in those two cases.

Evaluate at A0=ω1×{1}. Both A0 and its complement are uncountable, so {A0} is not in D_t and no atom is true there. Actuality therefore fails. More explicitly, any true supported proposition contains A0 and some distinct world obtained by swapping one point of A0 and one of its complement outside its countable support; a coordinate proposition separates those worlds, so the true proposition cannot entail every actual truth.

The nonempty set O:={A⊆I:A and I\A are both uncountable} is G-invariant, hence lies in D_t, but contains no supported singleton and therefore no atom. Atomicity fails already at t.

The base N is infinite, and every subset of N has an invariant crisp characteristic predicate. Since FiniteCardinality is the set of standard numeral values, the universal individual property is not assigned a finite cardinality. Thus the individual Axiom of Infinity holds; the proposition domain is also infinite, so the propositional Axiom of Infinity holds. These facts are necessary because the domains and crisp finite-cardinality calculations are constant across W.

This produces, with both infinities, C+□ND+□BF+Countable Boolean Completeness and countable infinitary lambda comprehension, while Actuality and Atomicity fail at the designated point. In particular countable infinitary closure does NOT itself force □Actuality: the arbitrary set-indexed intersection used in section 8 is genuinely stronger. The model still cannot satisfy original Maximalism, because Countable Boolean Completeness already excludes it by the recorded Goodsell result.


### 10.3 Bounded infinitary closure at every regular cardinal

The construction generalizes uniformly in ZFC. Let κ be any infinite regular cardinal, put I=κ×{0,1}, W=P(I), and admit exactly objects having a support of cardinality <κ. Keep D_e=N and the recursive supported-function domains. The stabilizer arguments above are unchanged. A family of <κ parameters has a combined support of size <κ by regularity; therefore the structure is closed under L_{κ,ω} conjunctions/disjunctions and lambda abstraction with <κ parameter families. For κ=ω this says finitary closure, and κ=ω1 gives the countable case. An explicit common bound on parameter families is part of the closure claim.

Coordinate propositions still separate every pair of worlds. A singleton {A} has a support of size <κ exactly when |A|<κ or |I\A|<κ: fixing such a support S leaves the full symmetric group of I\S, whose only invariant subsets are empty and the whole complement. Hence no atom is true at A0=κ×{1}. The invariant proposition O_κ={A⊆I:|A|≥κ and |I\A|≥κ} is nonzero and contains no supported singleton, so Atomicity fails. The proof of this failure requires no regularity; regularity is what guarantees the stated infinitary closure.

Supports here are group-theoretic, NOT a coordinate-measurability restriction. Every subset of W invariant under the pointwise stabilizer of a small S is admitted, even if it is not decided by A∩S. In particular O_κ has empty support, despite depending on the sizes of A and its complement. This distinction is essential to the model and its quantifier closure.

Thus no fixed regular infinitary arity bound forces Actuality or Atomicity from C, even with □ND, □BF and both infinities. For uncountable κ, Countable Boolean Completeness also holds by section 7, so these models still exclude original Maximalism. The arbitrary set-indexed closure theorem in section 8 has a genuinely unbounded hypothesis. This is a semantic separation, not a claim that the infinitary proof systems are complete.

### 10.4 Explicit lambda-closure check

For completeness, let a term T(x) have finitely many free argument variables besides a <κ family of named parameters, with their combined support S of size <κ. The equivariance induction gives [[T]]_{g·assignment}=g[[T]]_{assignment} for every g∈G. Each value [[T]]_{x=a} lies in its prescribed domain by induction. For g fixing S, the function f(a)=[[T]]_{x=a} therefore satisfies f(ga)=g f(a); equivalently gf=f. Hence f has support S and is an admitted lambda denotation. For iterated abstraction, fixing an argument a adds its <κ support to S, so each curried slice is admitted before the outer function is formed. No full unsupported function space is being used silently.

For the universal quantifier, Q(P)=⋂_{a∈D_σ}P(a) has support any support of P, because gQ(P)=⋂_a gP(a)=⋂_a (gP)(ga)=Q(gP). Consequently Q itself is equivariant and is an admitted constant of type (σt)t. The identity operation is equivariant for the same reason: g(W)=W, g(∅)=∅, and a=b iff ga=gb. The Boolean operations are equivariant by their set-theoretic definitions. These facts supply the induction bases, independently of any cardinality bound on D_σ or on the intersection used by a quantifier.


## 11. Sharp representation corollary: C5 suffices with unbounded closure

Section 5 assumed □Plenitude. Sections 8 and 10 allow a sharper formulation. Let M be a set-sized model of C5=C+□ND, closed under arbitrary set-indexed parameter conjunction/disjunction and the corresponding lambda abstractions, with the ordinary pointwise truth clauses. Then section 8 supplies all-type Atomicity. The proved local result `c5-and-atomicity-imply-necessary-plenitude` (Classicism, §2.3 concluding equivalences, p.33) supplies □Plenitude. Hence the full constant-domain S5 representation of section 5 follows already from C5 plus this unbounded comprehension resource.

The critical atom proof is algebraic and does not smuggle in BF. If a non-bottom R:τ is given, Intensionality identifies R=bottom with necessary emptiness, so some accessible point and tuple makes R true. The literal intersection over ALL root Y:τ is true at that point and tuple; it therefore has non-bottom denotation a. For every root Y it has a≤Y or a≤¬Y. If z≤a, the first alternative with Y=z gives a=z, and the second gives z=bottom. This is exactly the atom condition, even if the witnessing point has new relation objects or new argument objects. Only the root relations occur in the parameter family.

For clarity, the resulting representation is the FULL INTENSIONAL S5 relational hierarchy: D_t=P(W) for its set W of Boolean atoms, D_e is any nonempty set, and D_{στ}=D_τ^{D_σ}; propositions are evaluated at a designated w∈W. Equality is crisp, quantifiers are pointwise arbitrary meets/joins, and application is evaluation. This does not assert Extensionality at the designated point, and W need not be a singleton. The set W is nonempty because Actuality supplies a true atom.

In ZFC, every such full hierarchy satisfies □Functional Choice, by selecting a witness separately for each input at each evaluation world. Thus, over a ZFC metatheory, the unbounded infinitary extension of C5 semantically forces T as well as full standard S5 representation. Over ZF, stop at the representation theorem unless the appropriate external choice principle is supplied; full function spaces do not themselves select witnesses from arbitrary serial relations.

For every fixed infinite regular κ the model in §10.3 satisfies C5 and the corresponding bounded infinitary closure, yet fails Actuality and Atomicity. Hence the passage from bounded L_{κ,ω} closure to arbitrary set-indexed parameter closure is mathematically substantive even before asking about Functional Choice. The statement concerns semantic models; no completeness claim for an unspecified infinitary calculus is intended.


## 12. A single pure infinitary abstraction already obstructs original Maximalism

This improves the resource bound in §7. Parameterized countable comprehension is unnecessary for the incompatibility result. It suffices that the language admit, at σ=e, the ONE pure infinitary abstraction

    P_σ := λZ^{ν_σ}. ∨_{n<ω} [Z=ν_n],   where ν_n=Suc_σ^n(0_σ),

with its ordinary pointwise disjunction and lambda truth clauses at every evaluation point. The finite numeral terms are already pure terms of C. The argument is semantic; original Maximalism still has its original finitary C side condition.

### 12.1 Numeral exhaustion, and distinctness under I

At every point, P_σ contains zero and is closed under successor. Impredicative FiniteCardinality therefore implies P_σ, while every ν_n is finite by ordinary finite induction. Thus N_σ consists exactly of the external sequence of numeral denotations.

If I_σ=◇I*_σ holds at a point v, choose an accessible point u satisfying I*_σ. There, zero is not a successor and successor is injective on N_σ, so finite cancellation shows ν_m≠ν_n for every distinct external m,n. If two numeral denotations were identical at v, NI would preserve that identity at u. Hence all numeral denotations are distinct already at v. At every point satisfying I_σ, the structure (N_σ,0,Suc,=) is therefore exactly standard (ω,0,n↦n+1,=).

### 12.2 The existing arithmetic definitions have their standard values

No full relation domain and no additional infinitary formulas are needed here. Fix standard m,n and let ν_k abbreviate the numeral denotations at v. To test the impredicative definition of Sum(m,n,o), every relation containing (0,m) and closed under simultaneous successor contains (n,m+n), by n ordinary steps. For a wrong endpoint o, the following FINITARY lambda relation is a counterexample:

    R_{m,n}(i,j) := [∨_{k=0}^n (i=ν_k ∧ j=ν_{m+k})]
                   ∨ [∧_{k=0}^n i≠ν_k].

It contains the starting pair, is successor-closed on the standard number domain, and at first coordinate ν_n contains exactly the correct second coordinate. The unrestricted tail is what makes this a finite formula despite the infinite domain. Consequently the source's Sum definition is standard addition.

For Prod, use the same formula with ν_{m·k} in place of ν_{m+k}. The starting pair is (0,0), and the recursive step uses the already established standard Sum relation. Again it excludes every wrong endpoint. Thus Prod is standard multiplication. Induction on the finite syntax of an arithmetical sentence A now proves that its truth at v is its ordinary truth in standard arithmetic whenever I_σ holds there.

### 12.3 Necessity of Arithmetic and the exact incompatibility

Choose the standard truth value of any arithmetical A. At EVERY accessible point satisfying I_σ, A has this same value. Hence the original Necessity-of-Arithmetic instance

    □(I_σ→A) ∨ □(I_σ→¬A)

holds. The σ=e instance already contradicts original pure Maximalism by the proved record `possibility-and-necessity-of-arithmetic-incompatible` (Goodsell, Arithmetic is Necessary, §6, Theorem 11 and note14, pp.24–26). The theorem uses recursive enumerability and consistency of the ORIGINAL reference theory C; no claim is made that the enriched theory is recursively enumerable.

Therefore original Maximalism has no intended model admitting even this single pure countable-disjunction abstraction with its ordinary meaning. Full S5 models with infinite individual domain do admit it and satisfy T, so this extension is compatible with T in ZFC. This does not prove a contradiction in finitary Maximalist Classicism: it identifies failure of closure under one particularly natural infinitary description.

Equivalently, in any intended model of original Maximalism, standard Frege numberhood cannot hold at every accessible point satisfying I_e. For a Gödel-undecidable arithmetic sentence supplied by the cited argument, Maximalism requires both arithmetic possibilities; the one disagreeing with standard truth must have nonstandard numberhood. This is an external semantic diagnosis, not an internal predicate of nonstandardness and not a new recorded theorem.

If the whole pure countable-infinitary lambda language is admitted, a further corollary is available: every external relation S⊆ω^k is represented on the numeral domain by λz̄.∨_{n̄∈S}∧_i z_i=ν_{n_i}. Thus the local arithmetic interpretation at every I-point has full second-order relation domains. This stronger observation is unnecessary for the incompatibility proof above.


### 12.4 An explicit proof-rule alternative

One can instead keep the finitary formula language and add an ordinary ω-rule for the intrinsic numbers:

    from φ(ν_0), φ(ν_1), φ(ν_2), ... infer ∀z∈N_e φ(z).

Allow countably branching well-founded derivations, and allow theorem necessitation for the enriched calculus. These are NEW proof rules; the number rule is not sound for all original Henkin models. It is sound for the standard full S5 hierarchies, whose Frege number domain is exhausted by standard numeral values, so this extension remains compatible with T in ZFC.

The local record cited in §12.3 uses the source's Lemma1 to establish arithmetic adequacy of C+I_e (the axioms of Peano arithmetic under the given interpretation). With that recorded adequacy as input, the usual truth induction proves: for each ordinary arithmetical sentence A, the enriched calculus proves I_e→A if A is true in standard arithmetic, and I_e→¬A otherwise. Atomic numeral computations use the arithmetic adequacy; existential truth has a standard numeral witness; universal truth applies the ω-rule to the already derived implications I_e→φ(ν_n), then commutes the fixed antecedent I_e past the restricted universal quantifier. Negation and Boolean connectives use classical logic. Parameters corresponding to finitely many already fixed standard numeral values do not change the argument. This is induction on finite formula complexity, not an effective decision procedure for arithmetic.

The resulting closed theorem I_e→A or I_e→¬A can then be necessitated. Thus the enriched calculus proves every Necessity-of-Arithmetic instance at e and is syntactically incompatible with the ORIGINAL Maximalism schema. The contradiction retains C as the latter's reference theory. This is a precise proof-theoretic counterpart to the semantic one-term obstruction, and it expressly includes the additional modal proof rule rather than assuming an unspecified infinitary calculus is complete.


## 13. Existing conjecture: Relational Choice versus Transversal Choice

The exact recorded conjecture is `relational-choice-r-implies-transversal-choice-r`. Christopher Sun's proved decomposition says Transversal Choice is equivalent to Relational Choice plus Transversal (one property representative for every actual coextension class). The conjecture therefore concerns property representatives, not the stronger OPERATION canonicalizers of §1. Those stronger canonicalizers are equivalent to Actuality and cannot simply be assumed. The ordinary quotient proof's coextension/identity gap remains real.

### 13.1 Bare C rigidifies every internally finite property

Put Fin_σ(X):=∃N(FiniteCardinality_σ(N)∧NX), using exactly the map's Frege definition. Then C proves

    Fin_σ(X) → ∃Y^{σt}(Rigid(Y) ∧ ∀z(Xz↔Yz)).

This is a genuinely internal induction, not a claim restricted to externally standard finite sets.

The haecceity H_a=λz(z=a) is rigid. Persistence is NI. At any accessible point, suppose ∀z(z=a→□Pz). Instantiation gives □Pa; equality substitution at every further point gives □∀z(z=a→Pz). This proves weak inextensibility there. The argument is uniform at every point, so H_a has the source's full boxed inextensibility. Bottom is rigid as well.

Rigid properties are closed under binary union. Persistence is immediate. For weak inextensibility, if every Y∨Z-instance necessarily has P, the same premise holds separately for Y and Z; their bounds Y≤P and Z≤P give Y∨Z≤P. This argument works at every accessible point for rigid Y,Z. Equivalently, necessitate the discharged bare-C weak-rigidity closure theorem and use the boxes in the definition of Rigid. No BF is used.

Now induct on finite cardinalities N with the property that EVERY X satisfying NX has a rigid coextensive representative. At zero, X is empty and bottom works. At Suc(N), choose the witness a∈X with N(X−a). By induction choose rigid Y coextensive with X−a. The union Y∨H_a is rigid and coextensive with X. This proves the displayed assertion for every internally finite cardinality.

Two rigid coextensive properties are identical, by the standard weak-rigidity argument: weak inextensibility of one against persistence of the other gives one algebraic bound, and conversely; Intensionality gives equality. Thus the displayed rigid representative is unique. No operation assembling these representatives is asserted.

### 13.2 Relational Choice settles every equivalence relation with finite cells

Let R be an actual equivalence relation, and suppose

    ∀x Fin_σ(λz.(Rx)z).

By §13.1 each cell has a unique rigid coextensive representative. Apply Relational Choice to U(Y,y):=Yy∨¬∃zYz, obtaining an actually functional S⊆U. Define

    G(y):=∃Y[Rigid(Y) ∧ ∀z(Yz↔(Ry)z) ∧ (SY)y].

For each x, its rigid cell representative Y is nonempty, so S chooses y∈Y. Then Rxy, the cells of x,y are coextensive, and G(y) holds. If y,z in one R-cell both satisfy G, their rigid representative witnesses are coextensive, hence identical; functionality of S gives y=z. Thus G is a transversal.

Therefore RC⇒TC holds for all internally Frege-finite cells, with NO uniform cardinal bound and no assumption that internal finite cardinalities are standard. This uses neither Actuality nor Boolean Completeness nor ND/BF. Any counterexample to the full conjecture must have an internally infinite cell.

### 13.3 Bare C settles a finite number of cells

Suppose an internally finite property A meets every R-cell:

    Fin_σ(A) ∧ ∀x∃a(Aa∧Rxa).

Then C ALONE proves that R has a transversal. Induct on the finite cardinality of A, proving the stronger assertion that there is a partial transversal meeting exactly the classes meeting A, with its chosen elements in A. The empty case uses bottom. At a successor remove a, take a partial transversal G for the remainder, and either keep G if some member is R-related to a, or adjoin H_a if no member is. Equivalence of R verifies both uniqueness and coverage in the two cases. With A covering all classes, the resulting partial transversal is total.

Consequently a prospective RC/TC separator must also have no internally finite class-cover. This is a precise restriction on a countermodel; 'infinitely many classes' should be read in this internal sense, not silently as external cardinality.

### 13.4 Infinitary finite-class analogue

Under pointwise infinitary lambda comprehension, every actual externally small property X has a rigid representative

    Y:=λz.∨_{a∈extension(X)} z=a,

provided the indexed parameter family is admitted by the chosen arity bound. NI gives persistence. At any point, the extension of Y is exactly the transported members of that indexed family; if each of those necessarily has P, the same disjunction shows Y≤P. This establishes inextensibility at every point, even when some members later coalesce. Thus Y is rigid.

In particular, with countably parameterized infinitary lambda comprehension, §7 turns every internally countable cell into an externally countable one. The preceding construction and §13.2's quotient proof show that RC gives transversals for equivalence relations with internally countable cells. Arbitrary set-indexed parameter comprehension gives the full RC⇒TC implication, without C5. These are explicit language-extension results, not solutions of the original finitary conjecture.

### 13.5 Countermodel route and outstanding obligation

The first-order analogue is definable Skolem functions without definable transversals/elimination of imaginaries. A suggestive seed has an equivalence E, a successor bijection s with no finite cycles preserving E, and infinitely many individually named defaults in different E-classes. Finite first-order constraints can choose a witness from iterates of an available parameter in a specified class, or from finitely many defaults outside finitely many forbidden classes. An untouched E-class retains a shift automorphism, obstructing a finitely parameter-definable transversal. This analogy is not a C model.

For C the successor must be relationalized, since ee is not an admitted function type. Moreover, if its orbit structure is rigid across all points, higher-order orbit properties can become canonical and RC destroys the proposed obstruction. A prospective intensional construction must let the relation vary beyond the designated point, while maintaining all-type lambda comprehension, higher-order quantification, Logical Equivalence and RC. No such construction has been obtained here. The existing full-symmetric-hierarchy no-go argument in the conjecture's write-up remains applicable to full symmetric models; a mere appeal to symmetry or definable Skolem functions is insufficient.


## 14. Independent audit: Bourbaki–Witt in C for a functional graph

This addresses the extension lane's proposed proof of the EXISTING conjecture Relational Choice + Boolean Completeness ⇒ Transversal Choice. Only the fixed-point lemma is established here; the Boolean partial-selector construction is separately audited by the parent and extension lane.

**Lemma (bare C).** Let P be a nonempty property on a type ρ. Let ≤ be a represented partial order on P. Suppose every represented chain C⊆P, including the empty chain, has a least upper bound in P. Let f be a represented functional graph from P to P, and assume x≤y whenever P(x) and f(x,y). Then f has a fixed point: ∃x(Px∧f(x,x)). No operation representing f, Plenitude, Relational Choice, Actuality, BF, ND, or extensional identification of properties is required.

**Proof.** Suppose f has no fixed point. Then f(x,y) implies x<y on P. Fix p0∈P. For a property C:ρt put Good(C):=(C⊆P ∧ C is a chain). Define the relation G from properties to elements by

    G(C,z) := [Good(C) ∧ ∃s(Sup_P(C,s) ∧ f(s,z))]
              ∨ [¬Good(C) ∧ z=p0].

Here Sup_P(C,s) includes Ps and the usual least-upper-bound formula with all upper bounds restricted to P. Existence and antisymmetry make its s unique as an ENTITY. Therefore G is functional. Moreover, Good(C) and Sup_P(C,s) depend only on the actual extension of C. If C and D are coextensive, they have the SAME unique s, and functionality of f gives the same z. Thus G is extensional as a relation on property codes, despite no identification of those codes and no operation for f.

For every Good(C), its G-value z belongs to P and is a strict upper bound of C: every x∈C satisfies x≤s<z. This is exactly the input to the conforming-chain part of the repository's proof `writeups/transversal-choice-r-implies-zorn-r.md` (Lewin's argument, with its higher-order translation). That proof's use of Transversal Choice ended once an extensional functional strict-upper-bound relation was supplied. We have just supplied one directly.

For a precise applicability check, define Conf(A) by A⊆P, A well-ordered by ≤, and G(A_{<x},x) for every x∈A. All predecessor properties A_{<x} are represented by lambda abstraction and included in P. Lewin's first two lemmas, using extensionality of G and its functionality, show that conforming properties are comparable by inclusion and the smaller is an initial segment of the larger. His third and fourth lemmas then show that

    U:=λx.∃A(Conf(A)∧Ax)

is itself conforming; it is still included in P. Its G-value z∈P is strictly above every U-member. The one-point extension U∨H_z is conforming by the fifth lemma, since its predecessor at z is coextensive with U and predecessor properties at old points are unchanged up to coextension. Hence z belongs to U by its defining existential, contradicting z being strictly above all its members. This proves the lemma.

Every one of the four explicitly marked (E) steps in the existing write-up is justified here by the proved coextension-invariance of G. No coextensive stage properties are identified. The parameter f is used only as an actual functional graph; its output is never assumed to be an admitted operation. Thus the two specific intensional obstructions in the proposed application are absent.

**Scope for the conjecture.** Boolean Completeness is relevant because it gives UNIQUE chain-supremum entities under algebraic Boolean order. Merely ordering partial selector properties by actual inclusion gives only coextensive suprema, so the construction of G above would lose its extensionality. The lemma therefore does not by itself settle RC⇒TC without Boolean Completeness.


## 15. Under Relational Choice, chain Boolean completeness is full completeness

Fix a relational type τ. By ChainBC_τ mean: every represented family C^{τt} linearly ordered by the algebraic Boolean order ≤_τ has an algebraic least upper bound, including the empty family. This is a formulation introduced here, not an existing database principle.

**Theorem (bare C).** Relational Choice at input/output types (τ,τ) plus ChainBC_τ implies Boolean Completeness at τ. The reverse implication from Boolean Completeness to ChainBC is immediate. Thus under the indicated single RC instance, the two completeness conditions are equivalent.

**Proof.** Fix an arbitrary family X^{τt}. Write

    UB_X(u):=∀x(Xx→x≤u),
    P(b):=∀u(UB_X(u)→b≤u).

P is a represented property, and bottom belongs to P. Every member x of X belongs to P. The Boolean order is antisymmetric, so P inherits a partial order.

Let C⊆P be a represented chain and let j be its ambient least upper bound, supplied by ChainBC_τ. If u is any upper bound of X, every C-member lies below u by membership in P, so j≤u by leastness. Therefore j∈P, and j is also the least upper bound of C within P. Thus P is chain-complete, including at the empty chain.

If P(b) and UB_X(b), b is already a least upper bound of X: it is an upper bound, and P(b) says it lies below every upper bound. If instead ¬UB_X(b), choose x with Xx and x≰b and put c=b∨x. Both b and x lie below every upper bound of X, so P(c). Also b≤c and c≠b, because c=b would imply x≤b. Thus every non-solution b∈P admits a strict progressive extension within P.

Define a serial relation U on the WHOLE τ-domain by requiring, on P-inputs b,

    P(c) ∧ b≤c ∧ (UB_X(b) ∨ b≠c),

and requiring c=bottom off P. Seriality follows from the two cases above. The single RC instance gives a functional subrelation f⊆U. On P this is a progressive functional graph P→P, strict at every non-solution. The bare-C Bourbaki–Witt lemma of §14 supplies a fixed point b∈P. The defining requirement of U forces UB_X(b), so b is the desired least upper bound. This proves Boolean Completeness.

No current family has been identified with a necessarily coextensive family. No selector graph has been upgraded to an operation. The proof uses only algebraic finite joins, chain least upper bounds, the indicated RC instance, and the already audited graph version of Bourbaki–Witt. In fact the same argument works for any represented bounded join-semilattice with bottom and represented chain suprema; Boolean complements are not used.

Consequently the all-type schemas RC+ChainBC and RC+BC are equivalent over C. The proposed proof of RC+BC⇒TC therefore also works with chain Boolean completeness as its stated extra premise. At a fixed σ, it is enough to assume RC at ((σt),(σt)) and ChainBC at σt: first upgrade to BC at σt, then run the partial-selector proof. This states exactly which types of Choice and completeness are used.


### 15.1 Directed completeness already gives full Boolean Completeness in bare C

Let DirectedBC_τ say that every nonempty represented directed family in the algebraic Boolean order has an algebraic LUB. Then C proves DirectedBC_τ iff BC_τ; no Choice premise is needed.

For a represented X, define D(b) to hold iff every represented property Z containing bottom and all X-members and closed under binary join contains b. By comprehension D is represented. The usual intersection argument proves that D contains bottom and X and is binary-join closed. Hence D is nonempty and directed. If u bounds X, the represented downset λb(b≤u) contains bottom and X and is join closed, so every D-member lies below u. Therefore X and D have exactly the same upper bounds. A LUB of D is consequently a LUB of X. The reverse implication is immediate.

This distinguishes the two weakenings: directed completeness equals full completeness in C already, whereas the proof upgrading well-ordered/ordinary chain completeness uses the stated RC instance.

### 15.2 Further audited weakening to well-ordered chains

The extension lane supplied a self-contained f-chain proof of the graph Bourbaki–Witt lemma in §5 of `.reproduction/classicism-research/relational-choice-boolean-completeness-transversal-proof.md`. I independently checked its initial-segment comparison, union well-ordering, and both supremum-adjunction steps. The only existence application of chain completeness is the supremum of the internally well-ordered union of all f-chains, together with the least element/empty join. The LUB conditions for predecessor images are part of the definition of an f-chain and are inherited or explicitly verified; no extra completeness premise is used to obtain them.

Consequently define WOChainBC_τ by requiring suprema only of represented families internally well-ordered by the algebraic Boolean order, including the empty family. The same cut argument proves

    C + RC_{τ,τ} + WOChainBC_τ ⊢ BC_τ.

Thus under the indicated RC instance, WO-chain completeness, chain completeness and full Boolean Completeness are all equivalent. The term 'well-ordered' is the internal one quantifying over admitted subproperties; no external ordinal domain is assumed. The ordinary chain-complete formulation is simpler for presentation, while this refinement records the exact logical resource of the fixed-point proof.


## 16. Transversal Choice supplies a canonical extensional core by RELATIONS

This is distinct from the operation-retraction theorem in §4. It gives a parameterized interpretation in the many-sorted relational presentation of classical extensional relational HOL, using admitted functional graphs for application. It does NOT assert operations representing those graphs, and does not import Plenitude or Functionality into the ambient C model.

Work with any finite collection of types closed under taking the proper types occurring in them. This is enough for every finite proof or formula. Let D_e(x) be true of all individuals and let D_t(p) say p=top or p=bottom. Interpret t as these two entities, with top designated true. Recursively suppose the core argument domains have been selected. For τ=σ1…σn t put

    E_τ(F,G):=∀x1…xn[(∧i D_{σi}(xi))→(F[x̄]↔G[x̄])].

This is an actual equivalence relation on raw τ-entities. Transversal Choice supplies a predicate D_τ selecting exactly one representative of each E_τ-class. Every core domain is nonempty, since the raw domains are nonempty and every equivalence class has a representative. At t the explicit choice {top,bottom} has the same required property for truth equivalence.

Define the normalization GRAPH

    N_τ(F,G):=D_τ(G)∧E_τ(F,G).

It is total and single-valued on raw τ-entities and fixes every D_τ-entity. At e use ordinary equality as the normalization graph. This gives relational retractions, not operations of type ττ (which may not exist, and are forbidden at e).

For F∈D_{σρ}, x∈D_σ, interpret application by the unique y∈D_ρ such that N_ρ(Fx,y). The raw section Fx is a legitimate ambient entity; only its normalization is relational. Equality in each core domain is actual identity of its selected representatives. Two core functions agreeing on all core inputs have coextensive raw sections on all core trailing arguments, hence satisfy E_{σρ}; uniqueness of representatives identifies them. Thus application is extensional, including the usual η law.

To check lambda comprehension explicitly, suppose a translated core term with free variable x is represented by a total single-valued graph B(x,y), y∈D_ρ, on core inputs. Write ρ=ν1…νk t and form the ADMITTED raw relation

    h:=λx v1…vk.∃y(B(x,y)∧y[v̄]).

For each core x, its raw section h x agrees on core trailing arguments with the unique B-value y. Choose the unique D_{σρ}-representative of h. Its interpreted application at x is therefore y. This proves β and gives the λ constructor. Truth-valued translated formulas use the same construction with k=0. Classical Boolean operations, quantifiers restricted by D_σ, and equality interpreted by actual identity are represented by the corresponding raw lambda formulas and then normalized. The standard term/formula induction therefore verifies classical extensional relational HOL. No external powerset or arbitrary function domain is asserted: this is a Henkin interpretation.

Relational Choice transfers to this core. Given a core serial relation, extend it to a raw serial relation by requiring outputs in the core on core inputs, and using a fixed core default otherwise. Ambient RC supplies a single-valued graph S. Canonicalizing its raw relation gives the interpreted relational choice witness. For interpreted Functional Choice with relational output ρ, apply the displayed lambda construction to B=S; the resulting core function has exactly the chosen core values. Outputs of type e remain graphs, respecting the fixed relational type system. Since TC implies RC, C+TC supports the resulting extensional HOL+choice interpretation. The new RC+BC theorem therefore supplies it as well.

**Interpretation status.** The representatives D_τ are existentially selected parameters, one for each required type. Adding names for a finite family of such witnesses is a conservative existential expansion, and every translated proof uses only finitely many of them. Application is interpreted by a definable functional relation, as allowed in a many-sorted first-order relational interpretation; it is NOT a term-to-term embedding using ambient application alone. Constructing one simultaneous core for all types semantically is harmless in ZFC, but no object-language quantification over types or hidden countable choice is claimed.

The contrast with §4 is exact. Under T, the normalization maps are admitted operations and raw application restricted to their fixed points already works. Under TC alone, canonical domains and application graphs suffice, while operation assembly can fail. This is a structural explanation of the extra force of Plenitude, not a claim that ordinary nonchoice extensional mathematics cannot be interpreted in still weaker setoid settings.

### 16.1 A transparent equivalent form of Transversal Choice

At each σ, call S^{(σt)σt} a coextension-invariant choice graph if it is total and single-valued, chooses an X-member whenever X is nonempty, and satisfies

    X≈Y → ∀z[(SX)z↔(SY)z].

The all-type schema asserting such S is equivalent in C to Transversal Choice. From TC use the recorded Transversal+RC decomposition: first replace X by its unique representative from a coextension transversal, then use the RC selector on that representative. Conversely apply S to the rows λz.Rxz of an arbitrary actual equivalence relation; coextensive rows receive the same chosen entity, so the range of those choices contains exactly one member of each R-cell. Empty properties cause no problem because S has an arbitrary total default there. This graph formulation works at σ=e without introducing an ee-valued operation.

This equivalent form makes the original conjecture's gap explicit: ordinary RC supplies a selector for each PROPERTY ENTITY, while TC supplies a selector depending only on its current extension. The new RC+BC proof obtains that coherence through unique algebraic suprema, rather than by assuming coextension is identity.


**Exact instance accounting for §16.1.** To obtain a coextension-invariant choice graph S at σ, the forward construction uses TC at the type σt (selecting one PROPERTY ENTITY from every coextension class) and RC with input σt and output σ. Explicitly, let D select one representative of each coextension class, and let V choose an element of every nonempty property entity, using an arbitrary fixed default on empty properties. Put S(X,z) iff ∃Y(DY ∧ X≈Y ∧ V(Y,z)). These two indicated instances suffice. Conversely S at σ yields TC at σ by applying it to the R-rows. Thus the equivalence stated above is an ALL-TYPE SCHEMA equivalence; TC at σ alone has not been claimed to supply S at σ.


## 17. Cardinal-bounded routes to Transversal Choice, with exact extra resources

These are instance-level refinements of the RC-alone investigation, not a proof of the unrestricted RC conjecture. All equivalence relations in this section are actual equivalence relations, and all orders, covers, graphs, and countability witnesses are admitted entities.

### 17.1 A well-ordered class cover needs no Choice

Suppose A⊆σ meets every R-cell and a represented relation < internally well-orders A. Then C alone gives a transversal:

    T(x):=Ax ∧ ∀y(Ay ∧ Ryx → ¬(y<x)).

For each cell its intersection with A is a represented nonempty subproperty of A, so it has a least element. Totality and antisymmetry of the well-order give uniqueness. This applies in particular when A has a represented injection into a domain already equipped with an internal well-order, by pulling back the order. If that domain is a Frege-number domain, its required well-order property must be justified under the stated arithmetic assumptions; it must not be inferred merely from external countability of A.

A second, distinct meaning of 'countably many classes' is an admitted identity-valued CLASS LABEL graph K⊆σ×J: every x has exactly one label j, and x,y have the same label iff Rxy. Here RC with input J and output σ suffices, irrespective of any ordering or cardinal bound on J. Apply it to the nonempty K-fibres, with a fixed default when a label is unused. The range of choices at used labels is a transversal. Thus represented coding of classes by natural numbers plus this RC instance suffices without CBC. Merely having countably many coextensive row codes is not such identity-valued class coding.

### 17.2 CBC and ND give canonical representatives for countable properties

Fix a counting type κ, any object type σ, and put ρ=σt. Extend the displayed Ctbl formula from the background to properties of σ even when σ=e: X is internally countable if an admitted relation L⊆σ×ν_κ assigns each X-member at least one natural-number label, and no label is shared by distinct X-members. This is exactly the same graph formula; no forbidden individual-valued operation is added.

Assume CBC at the output type ρ relative to κ, and ND at σ:

    ∀a z(a≠z → □a≠z).

For a countable X, let H be the family of haecceities H_a=λz(z=a), a∈X. H is countable: transfer a label n of a to H_a. Haecceities are injective as entities, since H_a=H_b implies a=b by evaluation. The transferred label relation therefore has precisely the required countability property. CBC supplies the algebraic join S of H.

If Xa then H_a≤S, so Sa. Conversely, fix z with ¬Xz and put E_z:=λu(u≠z). For every a∈X, a≠z, hence □(a≠z) by ND. Equality substitution gives H_a≤E_z. Thus E_z is an upper bound of H; leastness gives S≤E_z and consequently ¬Sz. Therefore S≈X.

The join S is weakly rigid, without any further ND use. For every a∈X, H_a≤S gives □Sa; axiom 4 gives □□Sa, hence H_a≤λz□Sz. Since the latter relation bounds H, S≤λz□Sz, so S is persistent. If ∀z(Sz→□Yz), each a∈X satisfies □Ya and hence H_a≤Y. Leastness gives S≤Y, proving weak inextensibility. Coextensive weakly rigid relations are identical, by persistence of one and weak inextensibility of the other in both directions. Thus each countable X has a UNIQUE weakly rigid coextensive representative.

It follows, using RC with input ρ and output σ, that every equivalence relation on σ all of whose cells are internally countable has a transversal. Use the RC selector on the unique weakly rigid representative of each cell. The representative's countability need not be independently assumed: it is coextensive with the original cell. Neither BF nor global Actuality is required. The exact completeness instance is CBC_{κ,σt}, and the exact distinctness instance is ND_σ.

**Why CBC alone does not justify this proof.** An algebraic join of countably many haecceities need not have exactly their actual union: currently false identity propositions may have a currently true algebraic join. The ND assumption above rules this out by supplying the SINGLE upper bound E_z for all haecceities outside z. Countably parameterized pointwise infinitary disjunction instead supplies the actual union directly, as in §13; this is a different language resource and must not be confused with CBC.


### 17.3 Only finitely many exceptional infinite cells also suffice

RC proves TC for an equivalence R whenever an internally finite represented A meets every R-cell that is not internally finite. Indeed, internal finiteness of a property is invariant under actual coextension (prove the invariant cardinality predicate by Frege induction), so being an infinite R-cell is constant on cells. Restrict A to the infinite-cell part and use the finite-cover induction of §13 to choose one member of each such cell. Use the RC/unique-rigid-representative construction on the remaining, finite cells. The two selected predicates lie in disjoint families of cells, so their union is a transversal.

Thus failure of TC under RC requires an equivalence with no internally finite cover even of its infinite cells. In ordinary language it must have infinitely many internally infinite cells; the precise statement is the absence of such an internally finite cover. This is stronger than merely requiring one infinite cell and infinitely many cells in total.

## 18. Actuality is principality of the algebraic null ideal at ANY relation type

Fix one relational type ρ=σ1…σn t, allowing n=0. Define

    Null_ρ(X):=∀z1…zn ¬X[z̄].

This is the kernel of the actual extension homomorphism, formulated entirely internally: the properties/relations currently having empty extension. It is an ideal under the algebraic Boolean order. The following is a single-type equivalence in bare C:

    Actuality ⇔ ∃n^ρ(Null_ρ(n) ∧ ∀X(Null_ρ(X)→X≤n)).

**From a greatest null relation.** Put a:=∀z̄¬n[z̄]. This is true because n is null. If p is any currently true proposition, the constant relation c_{¬p}:=λz̄¬p is null, hence c_{¬p}≤n. Unfolding ≤ gives □∀z̄(¬p→n[z̄]); by logical equivalence and nonemptiness of the argument domains, this entails □(a→p). Therefore a≤p for every true p, so a is an actuality proposition. With no arguments, this is just a=¬n.

**From Actuality.** Let w be true and lie below every true proposition. The relation n:=λz̄¬w is null. If X is null, the proposition ∀z̄¬X[z̄] is true, so w≤∀z̄¬X[z̄]. Unfolding and using classical logic gives □∀z̄(X[z̄]→¬w), that is X≤n. Thus n is greatest null. No BF or ND is used: the quantifier remains inside the box throughout.

This gives a more transparent equivalent version of the quotient/canonicalization result in §1: Actuality says that the ideal of currently empty relations is principal. It does NOT say merely that this ideal has an algebraic supremum; BC supplies a supremum, but it may fail to be currently empty.

**Finite-fibre corollary.** If Null_ρ is internally Frege-finite, C gives its finite algebraic join by induction on its finite cardinality. Bottom is null, and the join of two null relations is null, so this finite join lies in Null_ρ and is its greatest member. Hence Actuality. More generally, for any fixed F^ρ, Boolean symmetric difference X↦X⊕F is an admitted involution carrying Null_ρ bijectively to the actual coextension class of F. Internal finite cardinality is invariant under admitted bijections, by the same Frege induction. Thus internal finiteness of ANY one coextension class at ANY relation type already implies Actuality, with no Choice premise. If Actuality fails, every such coextension class is internally infinite.

These are original ordinary mathematical arguments in this report. No claim is made that the principal-ideal formulation or its finite-fibre consequence is new in the literature.


## 19. CBC rules out countable cofinality of a nonprincipal actual null ideal

Here the extra arithmetic premise is explicitly I_κ (possible injectivity of successor at the counting type κ), which supplies the ordinary Peano arithmetic of the Frege numbers, together with their impredicative induction for every admitted predicate. The repository's write-up `countable-boolean-completeness-implies-necessity-of-arithmetic.md`, Lemmas 2–7, records the relevant facts: I_κ implies I*_κ in C, and Peano arithmetic follows. No standardness of these numbers is asserted or needed.

**Theorem.** In C + I_κ + CBC_{κ,t}, Actuality is equivalent to the existence of an admitted κ-countable cofinal family in the ideal of false propositions. More generally, it is equivalent to such a family in Null_ρ at ANY one relational type ρ. Relational Choice is not required.

'Cofinal' means algebraically cofinal from below: B⊆Null_ρ and every X∈Null_ρ satisfies X≤b for some b∈B. Countability is exactly the admitted labeling-relation definition Ctbl, not external countability.

### 19.1 Relational recursion uses no operation or Choice

For an actual total single-valued graph F on a represented domain D, a0∈D, and Peano numbers N_κ, there exists an admitted actual functional graph n↦a_n satisfying a_0=a0 and F(a_n,a_{n+1}).

Define Hist(H,n) to say that H is a functional graph on the number interval [0,n], takes its values in D, starts at a0, and follows F at successive positions. Histories exist for every n by Frege induction: the length-zero graph is given by equality, and a history of length n extends to n+1 using the unique F-value of its last member and a one-point lambda update. A separate induction on k shows that any two histories defined at k have the same value there: the starting value is fixed, and the successor value is determined by the single-valued graph F. Histories need not be identical entities; only these values agree.

Now define B(n,a):=∃H(Hist(H,n)∧H(n,a)). Existence and uniqueness just proved make B total and functional on N_κ, and the history comparison proves its successor equation. This is an internal graph recursion theorem. It imports neither an operation representing F nor a choice of one history entity for every n. As a separate consequence, RC plus I_κ yields the usual dependent-choice sequence as a GRAPH by first selecting F from the given serial relation and applying this construction.

### 19.2 The countable-ideal argument

Let B⊆{p:¬p} be κ-countable and cofinal, with a countability labeling relation L. For each number n there is at most one b∈B with L(b,n); let p_n be that b when it exists, and bottom otherwise. This defines a total single-valued graph. Every p_n is false, and every B-member occurs. Suppose for contradiction that the false-proposition ideal has no greatest member.

For any false b, some p_k is not ≤b, since otherwise cofinality would make b greatest. The least such k exists by the least-number principle, with the predicate involving the actual parameter b. Define F(b)=b∨p_k for this least k; give F an arbitrary fixed/default value on true propositions. This is a definable single-valued total graph, without any choice axiom. Starting b_0=bottom, relational recursion gives b_{n+1}=F(b_n).

Induction proves that every b_n is false and b_n<b_{n+1}. A second induction gives p_i≤b_n whenever i<n. At step n, all indices below n are already covered. If p_n≤b_n, it remains covered; otherwise the least missing index is exactly n, so the next join covers it. Consequently the sequence b_n is cofinal in the false ideal: each base member p_k lies below b_{k+1}.

Put d_n:=b_{n+1}∧¬b_n. These are nonzero and pairwise disjoint, and d_m∧b_n=bottom whenever n≤m. The family {d_n:n is even} is internally countable: the graph from its even-number indices provides a countability relation. CBC_{κ,t} gives its algebraic join q.

If q is false, cofinality gives q≤b_N. Choose an even m≥N. Then 0<d_m≤q≤b_N, whereas d_m∧b_N=0, a contradiction. If q is true, ¬q is false, so ¬q≤b_N for some N. Choose an odd m≥N. Every even d_n is disjoint from d_m, so each lies below ¬d_m; leastness gives q≤¬d_m and hence d_m≤¬q. Again 0<d_m≤b_N contradicts d_m∧b_N=0. Classical truth exhausts the two cases.

The false ideal therefore has a greatest member. Section 18 gives Actuality. Conversely Actuality gives a one-element cofinal family, which is countable by assigning it the zero label. This proves the equivalence at type t.

### 19.3 Cofinal size is independent of the relation type

For ρ=σ1…σn t define admitted operations

    Σ_ρ(X):=∃z̄ X[z̄],       Δ_ρ(p):=λz̄.p.

They satisfy Σ_ρ(X)≤p iff X≤Δ_ρ(p), and Σ_ρΔ_ρ(p)=p, by logical equivalence and nonempty type domains. Both carry null/false inputs to null/false outputs.

If B⊆Null_ρ is cofinal, Σ_ρ[B] is cofinal in the false-proposition ideal: for false p, Δ_ρ(p)≤b for some b∈B, hence p≤Σ_ρ(b). Conversely, if B is cofinal among false propositions, Δ_ρ[B] is cofinal in Null_ρ: for null X, Σ_ρ(X) is false and lies below some b∈B, so X≤Δ_ρ(b).

Images under admitted single-valued graphs preserve the countability formula directly: assign an image value every number label of one of its preimages. A shared label forces the preimages equal by the original countability witness, hence the image values equal; every image value receives a label. Thus a countable cofinal family exists in Null_ρ iff one exists in Null_t. The same transfer works for smallness measured by labels in any admitted index domain. Only CBC at t is used in §19.2, irrespective of ρ.

**Scope.** This is an internal version of the ordinary Boolean-algebra fact that a nonprincipal ultrafilter on a σ-complete Boolean algebra cannot have a countable base. Its proof was developed here; no novelty claim or external full-powerset interpretation is asserted. The I_κ arithmetic premise is a stated sufficient premise, not a claim that it is indispensable in every finite or degenerate counting case.


### 19.4 Removing I_κ by the finite-index case

The exact strengthened theorem, for ANY fixed relational type ρ, is

    C + CBC_{κ,t} ⊢
      Actuality iff Null_ρ has an admitted κ-countable cofinal family.

No I_κ or RC premise is needed. Preserve §§19.1–19.3 as the proof of the I_κ case. If instead ¬I_κ, the infinity lane's `.reproduction/classicism-research/frege-infinity-20261022-1726.md`, §§27–28, makes every κ-countable property internally finite. Hence a countable cofinal B⊆Null_ρ is internally finite. Its finite Boolean join j exists in C and is still null, by induction using bottom and binary joins of null relations. Every member of Null_ρ lies below some B-member and therefore below j. Thus j is greatest in Null_ρ, and §18 gives Actuality. This finite case does not use CBC at any type.

Conversely Actuality supplies a greatest null relation at ρ; its singleton is cofinal and is always κ-countable by assigning the zero label. This direction needs no I_κ either. The theorem therefore follows by classical cases on I_κ. Finiteness in the finite-index case remains internal Frege finiteness, with no external standardness assumption.

## 20. Transversal Choice as Relational Choice respecting input quotients

For exact types σ,τ, define EInvRC_{σ,τ} as follows. Whenever E is an actual equivalence relation on σ and U⊆σ×τ is serial with E-invariant fibres,

    Exy → ∀z(Uxz↔Uyz),

there is a total single-valued graph S⊆U whose output is identical on E-equivalent inputs. This is a relational principle even when τ=e; no individual-valued operation is introduced.

The precise instance implications in C are

    TC_σ + RC_{σ,τ} → EInvRC_{σ,τ},
    EInvRC_{σ,σ} → TC_σ.

For the first, TC_σ chooses a predicate D containing exactly one representative of each E-class. RC_{σ,τ} chooses a functional graph F⊆U. Set S(x,z):=∃d(Dd∧Exd∧F(d,z)). Unique representatives and functionality give a unique output. E-invariance of U puts that output in U's x-fibre, and E-equivalent inputs use the same d, hence the same entity output.

For the second, apply EInvRC_{σ,σ} to U=E. Seriality follows from reflexivity and fibre invariance from equivalence. The range of S contains exactly one member of each E-cell, so it is a transversal.

Consequently the all-type EInvRC schema is equivalent to the all-type TC schema, using the recorded TC⇒RC implication in the forward direction. No claim is made that TC at one isolated type σ supplies RC at arbitrary input/output types. This gives a direct wording for the obstruction in RC⇒TC: a selected witness should depend only on the relevant input equivalence class. It is an equivalent formulation, not an additional axiom beyond all-type TC.


## 21. An internally countable, countably complete Boolean type is internally finite

**Theorem (type-local; no Choice).** For any relational type τ and counting type κ,

    C + I_κ + Ctbl_{κ,τ}(top_{τt}) + CBC_{κ,τ}
      ⊢ Fin_τ(top_{τt}).

Here Fin is internal Frege finiteness, not external finiteness of the model's domain. The arithmetic premise and graph recursion are exactly those audited in §19. No RC, Plenitude, BF, ND, or Actuality is assumed.

**Finite-interval lemma.** Frege induction proves closure of internally finite properties under subsets, admitted functional images, binary union, and unions indexed by an internally finite property when every fibre is internally finite. For the last claim, remove one index in the successor case, use the induction hypothesis for the remaining fibres, and then take a binary union with the removed fibre; no simultaneous choice of their finite witnesses is required. If c≤b in B_τ and d=b∧¬c, then every x≤b is (x∧c)∨(x∧d). Consequently, if both intervals [0,c] and [0,d] are internally finite, so is [0,b]: it is the union, over x≤c, of the finite images {x∨y:y≤d}. No product type is introduced.

Let E(n,b) be a total single-valued enumeration graph of B_τ by N_κ, obtained from the given countability labels: a number having a label-value takes that unique value, and an unused number takes bottom. Every Boolean entity appears. Suppose B_τ is internally infinite.

Whenever [0,b] is internally infinite, some c satisfies 0<c<b, since otherwise that interval is contained in {0,b}. Choose c by the LEAST enumeration index naming such an element. At least one of [0,c] and [0,b∧¬c] is infinite by the finite-interval lemma. Keep c if its interval is infinite, and keep b∧¬c otherwise. This is a definable total single-valued graph on the infinite-interval elements; extend it by a fixed default elsewhere. Its retained side is strictly below b and still has infinite interval.

Apply the graph recursion of §19.1 from b_0=top. It gives b_{n+1}<b_n with every [0,b_n] infinite. Put d_n=b_n∧¬b_{n+1}. Induction gives nonzero, pairwise disjoint d_n for all internal numbers n. Every use of a sequence here abbreviates its admitted functional graph; no operation representing it is required.

For any admitted number property X, the family D_X={d_n:n∈N_κ and Xn} is internally countable: its index graph assigns each number at most one value and supplies a label to every family member. CBC gives its unique algebraic supremum s_X. For every n∈N_κ,

    d_n≤s_X  iff  Xn.                                  (*)

If Xn holds, the upper-bound property gives d_n≤s_X. If ¬Xn, every selected d_m is disjoint from d_n, so ¬d_n bounds D_X and s_X≤¬d_n. Since d_n≠0, it cannot also lie below s_X. This proves (*), using only the join of this represented countable family.

Now define the admitted diagonal property

    Xn := N_κ n ∧ ∀b d((E(n,b)∧D(n,d))→¬(d≤b)),

where D(n,d) is the graph of d_n. For number n, this says d_n is not below the Boolean entity named by enumeration index n. Let s_X be the join supplied above and choose an index k with E(k,s_X), which exists by surjectivity of E. The diagonal definition gives Xk iff ¬(d_k≤s_X), contradicting (*). Therefore the assumption that B_τ was internally infinite was false.

**Internality audit.** The enumeration and the descending graph are fixed before the diagonal X is defined. No map X↦s_X is selected or represented: the final step uses one CBC witness for the one diagonal property. Least indices, finite histories, and the descent/disjointness inductions use admitted predicates on the possibly nonstandard Frege numbers. They therefore do not assume an externally standard enumeration or external countable choice.

The parent supplied this candidate argument; this lane independently audited the finite-product reduction, label enumeration, relational recursion, and diagonal step. The extension lane supplied a further independent audit and found no correction needed. This remains an ordinary mathematical proof, without a human or Lean verification claim.


### 21.1 Converse and exact equivalence

Under C + I_κ, the theorem is an equivalence:

    Fin_τ(top_{τt})
      iff Ctbl_{κ,τ}(top_{τt}) ∧ CBC_{κ,τ}.

For the converse direction to §21, first prove by Frege induction on the τ-cardinality of X that every internally finite X⊆τ admits a relational bijection with an initial segment [0,n) of N_κ. The empty case uses n=0 and the empty graph. In the successor case remove a∈X, apply the induction hypothesis to X\{a}, and extend its bijection by assigning a to the new index n. Peano arithmetic under I_κ gives [0,n+1)=[0,n)∪{n}, with n outside the old segment. This is a graph update, not an operation or a choice of enumerations. It yields the required Ctbl witness for the whole Boolean type.

Moreover, if the whole B_τ is internally finite, every represented family U⊆B_τ is internally finite by subset closure. A separate Frege induction gives its algebraic join: bottom for the empty family and j∨a when a member a is adjoined to a family with join j. Thus internal finiteness of B_τ implies the stronger BC_τ in C itself, and hence CBC_{κ,τ}. Together with §21 this proves the displayed equivalence. Throughout, 'finite' is internal Frege finiteness; no external finiteness of the model's domain follows merely from this statement.

### 21.2 Actuality corollary

In C, internal finiteness of B_τ at ANY one relational type τ implies Actuality. Its represented subproperty Null_τ is internally finite by subset closure. Its finite Boolean join is still null, because bottom and binary joins of null relations are null; it is therefore the greatest member of Null_τ. Section 18 supplies Actuality. Consequently the countability-plus-CBC conditions in §21 imply Actuality under the stated I_κ premise, without RC, BF, ND, or Plenitude.


### 21.3 Removing the arithmetic premise from the countable-to-finite implication

The infinity lane proves in `.reproduction/classicism-research/frege-infinity-20261022-1726.md`, §§27–28, that already in C,

    Fin_{ν_κ}(N_κ) iff ¬I_κ,

and that under ¬I_κ every property Ctbl relative to κ is internally finite. Its finite-successor-path argument keeps the proof inside Frege finiteness; the Ctbl consequence uses finite images of the label relation, without choosing enumerations or assuming external standardness.

Consequently the exact unconditional strengthening of §21 is

    C ⊢ Ctbl_{κ,τ}(top_{τt})
          → [CBC_{κ,τ} ↔ Fin_τ(top_{τt})].

For the nontrivial direction, assume countability and CBC and split on I_κ. If I_κ, apply §21. If ¬I_κ, the cited finite-index theorem gives Fin_τ(top_{τt}) directly from countability. Conversely internal finiteness gives BC_τ, hence CBC_{κ,τ}, by §21.1's finite-join induction, which used no arithmetic premise. Thus also

    C ⊢ Ctbl_{κ,τ}(top_{τt}) ∧ CBC_{κ,τ} → Actuality,

by §21.2. Both statements concern internal Frege finiteness and use no RC, BF, ND, or Plenitude.

**The remaining I_κ in §21.1 must be preserved.** Without it, internal finiteness need not imply countability relative to κ: the finite numerical domain may have too few labels. For example, in the full one-world extensional model with one individual, N_e has three elements (0,1,bottom), while the Boolean type tt has four entities. The whole tt-domain is finite and complete but is not Ctbl relative to e. Thus the unconditional result is the implication WITH countability assumed above, not the unrestricted equivalence Fin(B_τ) iff Ctbl_κ(B_τ)∧CBC_{κ,τ}.
