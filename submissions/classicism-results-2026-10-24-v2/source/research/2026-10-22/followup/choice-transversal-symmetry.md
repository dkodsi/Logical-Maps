# Relational Choice: selector persistence and supported symmetry

22 October 2026. Further focused work by OpenAI Codex. Original ordinary mathematical arguments; direct source: this note (`misc`). No human check, formal verification, literature-novelty claim, or constructed countermodel. The frozen `notes/` archive and the database are unchanged.

## Target and outcome

The target remains **unboxed all-type Relational Choice ⇒ Transversal Choice over the original fixed C**, including the individual type. A fresh proved-only `load_topic`/`Engine` query, with RC in the premise set, found no entailment, exclusion, or recorded separator. This describes the records, not the literature.

The earlier finite-ambiguity reduction in `choice-transversal.md` remains available. This pass tests a different route: constructing selectors in a restricted intensional hierarchy with symmetries. It establishes two additional obstructions, and a precise ultraproduct assembly lemma. The implication itself remains unresolved.

## 1. Even a two-output persistence repair already amounts to Actuality

Write weak persistence of a graph as

    WP(T) := ∀x y (T(x,y) → □T(x,y)).

No outer box is assumed. Put

    B(p,q) := (p ∧ q=⊤) ∨ (¬p ∧ q=⊥),    p,q:t.

Bare C already makes B an actually total functional graph, with two possible outputs. Call T a truth selector when it is actually total and contained in B. Functionality then follows from containment.

**Theorem. Over C, Actuality is equivalent to the existence of a weakly persistent truth selector.**

The persistent-truth step below adapts the recorded proof of `persistent-comprehension-r-implies-actuality` (Bacon–Dorr, *Classicism*, 16 May 2023 draft, §2.3, notes 38 and 40, p. 29). The restriction to a choice graph and the construction tests here are the present calculation.

Suppose T is such a selector. Let η(p):=T(p,⊤). Actual totality and containment give η(p)↔p, since ⊤≠⊥. Set

    a := ∀p(η(p)→p).

Then a is actually true. For any actually true p, η(p) holds and weak persistence gives □η(p). Necessary universal instantiation gives □(a→(η(p)→p)). Hence □(a→p), so a entails every actual truth and witnesses Actuality. Only the chosen edge at output ⊤ was used; no future functionality, future seriality, ND, or BF was assumed.

Conversely let u witness Actuality and define

    T_u(p,q) := □(u→B(p,q)).

Actually T_u(p,q)↔B(p,q): right-to-left is the defining entailment property of u; left-to-right uses u and T. Therefore T_u is an actual truth selector. Its weak persistence follows from the bare-C law □r→□□r. This does not necessitate the optional Actuality premise. QED.

Thus finite output range does **not** justify replacing an arbitrary graph by a persistent one. The obstruction occurs for a graph already definable without any choice axiom.

### Application to membership selectors

Let S at types (tt,t) choose an actual member of every nonempty proposition-property. Define

    A_p(q) := (q=⊤ ∧ p) ∨ (q=⊥ ∧ ¬p),
    η_S(p) := S(A_p,⊤).

Every A_p is actually singleton, and membership selection gives η_S(p)↔p. If all the true edges η_S(p) are necessary, the preceding proof again gives Actuality. Consequently, in a C+RC+¬Actuality model, **every** such S has some actually true p for which

    S(A_p,⊤) ∧ ¬□S(A_p,⊤).

In particular a membership selector cannot be reified as a graph whose proposition values are all literally ⊤ or ⊥ at the evaluation point: that would make every true edge necessary. This applies even when no selecting operation is admitted. It is a separate obstruction from the previously identified operation-valued ε trap.

The proved records contain RC+¬Actuality, with `finite-support-permutations` verified again by the engine. Thus persistent selector normalization cannot follow from RC. This is not a TC refutation: that recorded model also has TC.

Every proposed RC+¬TC separator must fail Actuality, by the recorded RC+Actuality⇒TC implication. The contingent-edge restriction therefore applies to the target construction.

### A further zero-filling obstruction, with an explicit ND premise

Add **unboxed ND_t**, namely ∀r s(r≠s→□(r≠s)). Suppose a membership selector S has the zero-filling property

    ∀A q (¬S(A,q) → S(A,q)=⊥).

Define D(A,q):=(S(A,q)≠⊥). Actually D↔S: a true proposition cannot be bottom, and zero-filling gives the converse. Thus D is another actual membership selector. ND_t makes D weakly persistent, and the preceding argument yields Actuality.

Consequently, under C+ND_t+¬Actuality, every such S must have an actually false edge whose proposition is nevertheless non-bottom. This is in addition to the true nonnecessary edge proved above without ND. A proposed realization that assigns bottom to every externally unselected pair and a true proposition to each selected pair therefore fails under ND_t, even if the true values themselves are allowed to vary later. Actuality follows from taking the nonzero test; it is not necessary to assume a selecting operation or a rigid original graph. No ND premise is added to the main target.

### A normalization that *is* available in bare C

Future functionality is different from persistence of a chosen edge. Given any actually total functional S at (α,β) and any default a:β, including β=e, there is an actually coextensive graph T which is **necessarily total and functional**. Put

    G(x,y) := S(x,y) ∧ ∀z(S(x,z)→z=y),
    T(x,y) := G(x,y) ∨ (¬∃z G(x,z) ∧ y=a).

At each point G has at most one output: two G-outputs are identified by the uniqueness conjunct of either. When G has an output, T agrees with G; otherwise its sole output is a. This is an unconditional H argument for every S and a. Necessitating that theorem and instantiating its parameters by bare-C CBF gives □Functional(T), without necessitating the optional actual functionality of S.

At the actual point, functionality of S gives G↔S and makes the default clause false, so T↔S. Hence, for inhabited output types, RC equivalently permits a necessarily total functional choice graph for each **actually** serial U, with containment in U still only actual. In the membership application a default is already supplied by applying S to the empty property. The default can violate U elsewhere. No graph persistence, selecting operation, or identity T=S follows.

This is a useful positive boundary: a countermodel construction may impose future totality and functionality on its chosen graphs by this formula. It must retain their contingent choices and cannot upgrade containment or persistence for free. Indeed the two-output graph B itself is necessarily functional in C, while making its true edges persistent is exactly the Actuality problem above.

## 2. Finite orbits obstruct RC without any fullness assumption

Work with a C model and a group of automorphisms of its **entire interpreted structure**, preserving the designated evaluation, application, and logical interpretation. Fix an admitted type σ, possibly e, and an actual membership selector S at (σt,σ). Let K be any subgroup fixing the entity S.

**Theorem. Every externally finite K-orbit in D_σ is a singleton.**

For a nonempty finite orbit O={a₁,…,aₙ}, form

    P_O := λx (x=a₁ ∨ … ∨ x=aₙ).

It is admitted in bare C. Every g∈K permutes O, so g(P_O)=P_O: the two finite disjunctions differ only by reordering, and H Logical Equivalence identifies their abstractions. Equivalently, P_O is the unique rigid property with extension O. The latter fact also follows from `notes/quotient-abstraction-lane.md`, §13.1.

S chooses y∈O. Because g fixes S and P_O, automorphism invariance gives S(P_O,gy); actual functionality gives gy=y. Thus y is fixed by every g∈K. Since O is its K-orbit, O={y}. QED.

In particular, if an automorphism g fixes S, it has no nontrivial finite cycle on D_σ. The image of the stabilizer of S in Sym(D_σ) is torsion-free. These are statements about **external finite orbits**; an internally finite Henkin set need not be externally finite.

For example, a construction with independently swappable pairs indexed by I, in which every entity is fixed by all swaps outside some proper small support J⊊I, cannot have the relevant membership selector. Choose a swap outside the selector's support and apply the theorem to its two-element orbit. This does not require symmetric ideal fullness, an admitted moved-element complement, or a definable fixed-point set. The pair-swap example in the archived compactness note was only a support counterexample, not a C+RC model, so there is no conflict.

The actual-evaluation and entity-fixing hypotheses are essential. A finite pinning set in an action model is not automatically a support for evaluation-preserving automorphisms. In particular this argument does not refute RC in the recorded nonsymmetric `finite-support-permutations` model.

## 3. Countable orbit closure is a genuine extra assumption

Consider the external semantic condition CR_σ:

> Every externally countable subset of D_σ is the actual extension of an admitted rigid σ-property.

Under CR_σ the preceding argument applies to the cyclic orbit

    O={gⁿa : n∈Z}

of any automorphism g fixing S. Its unique rigid representative is fixed by g, so the selected member is a fixed point of g in O; hence ga=a. Therefore:

**Under CR_σ, every automorphism fixing S acts identically on D_σ.**

CR_σ follows in the natural infinitary semantic extension which admits countable parameterized disjunctions of haecceities, with their ordinary truth conditions at every accessible evaluation and the corresponding abstraction identity laws. Such a disjunction is rigid: its instances at any later point are the transported named elements, and persistence and inextensibility follow pointwise from those of the haecceities. No operation uniformly enumerating the countable sets is claimed.

This is an **extended-closure conclusion**, not a theorem of the original finitary C. In particular, internal Countable Boolean Completeness is not silently substituted for CR_σ: an external orbit need not be an internally represented countable family. Nor does a trivial selector stabilizer by itself supply the omitted transversal predicate in a restricted Henkin model.

For the proposed shear constructions, CR_e is already fatal. A shear τ_i translates its protected class without fixed points, and each cyclic orbit {τ_iⁿa:n∈Z} is countable, even if the whole class is uncountable. Thus admitting these countable rigid orbit properties rules out a selector fixed by an unused shear. Countable infinitary comprehension would close, rather than assist, this particular countermodel route.

## 4. A bounded-support ultraproduct can retain the no-transversal invariant

There is a useful alternative to demanding that an ultraproduct preserve *finite* supports. The following assembly statement is metatheoretic, in ZFC, and constructs no factors.

Let I be uncountable and let G=⊕_{i∈I} Z, with generators τ_i. Suppose a sequence of many-sorted structures M_n has compatible G-actions by evaluation-preserving automorphisms. Every entity in every sort of M_n has finite coordinate support: generators outside that finite set fix it. Suppose each M_n has a G-fixed actual equivalence entity E_n and individuals b_{i,n}, with

    E_n(τ_i b_{i,n}, b_{i,n}),
    ∀x (E_n(x,b_{i,n}) → τ_i x≠x).

Take a nonprincipal ultraproduct M over N and use the **diagonal action of each fixed g∈G**. Every entity [a_n] has countable coordinate support: choose a finite support J_n of a_n and use J=⋃_n J_n. If i∉J, τ_i fixes every a_n and hence [a_n]. No claim that J is finite is made.

Łoś's theorem preserves the displayed protected-class conditions for each fixed i, as well as equivalence of E=[E_n]. If T were an admitted E-transversal in M, choose i outside its countable support. Then τ_i fixes T and E, and preserves the class of b_i=[b_{i,n}]. Its unique T-member would be fixed by τ_i, contradicting the second displayed condition. Thus M still has no E-transversal.

This also handles newly appearing individual elements: the universal fixed-point-free condition holds for **all** ultraproduct members of the protected class. No assertion that every new individual stays in the original finite vector hull is needed.

Consequently, if such M_n could satisfy the first n sentences of a fixed countable many-sorted first-order presentation of C+RC, the ultraproduct would give a countermodel to the target. The support and protected-class calculations themselves are complete. The **finite-fragment existence hypothesis is not proved**. In particular the known shear fixed-set obstruction still rules out factors with the corresponding represented moved-element complements; enlarging the index set does not repair a factor in which RC already fails. The unrepresented fixed reservoir and the lambda/quantifier/selector extension problem remain substantive requirements, not consequences of compactness.

## Stopping point

The pass yields a two-output persistence criterion exactly equivalent to Actuality, a safe normalization to necessary functionality, a fullness-free finite-orbit obstruction, its explicitly conditional countable version, and a bounded-support assembly lemma. Neither the original implication nor a separator is obtained. The credible construction route now needs actual finite-fragment factors with coherent choice graphs; another generic compactness invocation would only repeat that unproved hypothesis. No original-framework conclusion is inferred from the infinitary permission.
