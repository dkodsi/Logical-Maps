# Finite axioms, topology of completions, and effective presentation obstructions

Original proof notes by OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematics; no Lean claim and no database edits. The word “new” here concerns this research session, not a verified novelty claim about the literature.

## 1. Fixed framework and exact positive packages

Use the fixed relational types of C: e,t and σ→τ only for τ≠e. All type schemas below are instantiated over that effective collection. Max_C has precisely the old pure side condition C⊬A=B; it is not redefined relative to any added assumptions.

Write P_G for C+□Plenitude, equivalently C5+Atomicity, and P_F for C+□Functional Choice. Define the **single closed pure sentence**

    V_G := [□∀p^t q^t (p≠q → □(p≠q))]
           ∧ [∀p^t (p=bottom ∨ ∃a^t(Atom(a) ∧ a≤p))].

Then

    P_G = C + V_G                                      (1)

as theories/consequence sets, with the fixed deduction conventions. This is relative finite axiomatizability over C, not an assertion that C itself is finitely axiomatized.

Proof. The first conjunct is □ND_t. The recorded proposition `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` gives all of C5; C5 gives BF; `atomicity-t-and-bf-imply-atomicity` gives Atomicity at every relational type. The recorded concluding equivalence `c5-and-atomicity-imply-necessary-plenitude` gives □Plenitude. Conversely □Plenitude gives C5 and Atomicity, hence their type-t instances. The source proof of □ND_t→C5 necessitates a discharged logical implication; no optional premise is illicitly necessitated here.

The proved-only Engine was queried with the two optional conjuncts in its premise set, and confirmed both directions. Direct records used:

* `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` — Bacon–Dorr, 16 May 2023 draft, Proposition 2.2, p.22.
* `necessary-nd-implies-bf` — Proposition 2.3, p.22.
* `atomicity-t-and-bf-imply-atomicity` — Cian Dorr's observation of 23 September 2026 and the existing detailed write-up.
* `c5-and-atomicity-imply-necessary-plenitude` — concluding equivalences, p.33.
* `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`, `necessary-plenitude-r-implies-atomicity-r`, and the restriction records.

Adding the quantified Frege Axiom of Infinity at e, at t, or both still gives a single finite conjunction with V_G. Full Gallin models with E=W=ℕ witness the consistency of all these packages in the ordinary choice metatheory. This statement concerns the quantified axioms, not the infinite finite-distinctness schemas; those schemas need not be silently treated as single sentences.

## 2. The space being compared

Let S(C) be the space of complete consistent pure theories extending C. Equivalently, it is the Stone space of the Boolean Lindenbaum algebra of pure sentences modulo C-provable material equivalence. For a pure sentence F, write

    [F] := {Γ∈S(C) : F∈Γ}.

These are clopen basic sets. A finite list of conditions has the same basic set as its conjunction. [F] is nonempty iff C+F is consistent. The usual finitary Lindenbaum argument supplies a complete extension; the paper's general Henkin/BBK completeness gives models when a semantic formulation is wanted. Since the language is countable, S(C) is a compact metrizable zero-dimensional space. None of this invokes full higher-order semantics or its invalid compactness principle.

For any theory T⊇C let S(T)={Γ∈S(C):T⊆Γ}. It is closed, being the intersection of its axiom clopens. This remains true when T is not effectively axiomatizable. Effectiveness is relevant to the following nowhere-density argument, not to ordinary compactness itself.

## 3. Maximalism is a closed nowhere-dense locus

We use the independently established metatheorem:

> No consistent computably enumerable theory extending C can entail all of Max_C.

For completeness, the short proof is as follows. If such T existed, decide whether a closed pure A=B is a C-theorem by racing a C-proof search for A=B with a T-proof search for A≠B. Exactly one succeeds by consistency and Max's side condition. But the pure C identity word problem is Σ⁰₁-complete: relational first-order validity reduces to pure C theoremhood by universally closing the relation symbols as higher-order variables, and then to identity with top by theorem necessitation. Full ordinary extensional C-models give the converse direction of the reduction. The bare non-r.e. Max result is already stated by Bacon–Dorr in the accessible 1 July 2022 draft, §2.4 p.35 n.52; the stronger no-effective-strengthening formulation is what is used here. See `max-degree.md` for details and version caveats.

Now S(Max_C) is nonempty (the recorded coalesced maximalist root witnesses consistency) and closed. It has empty interior. Indeed, let [F] be any nonempty basic open subset of S(C). The theory C+F is consistent and c.e.; therefore it fails to entail some Max axiom A≠B, where C⊬A=B. Thus

    C + F + (A=B)

is consistent. Consequently [F∧A=B] is a nonempty open subset of [F] disjoint from S(Max_C). This proves that the complement of S(Max_C) is dense, and, since S(Max_C) is closed, that it is nowhere dense.

More generally, for **every consistent c.e. T⊇C**, the locus

    S(T) ∩ S(Max_C)

is closed and nowhere dense in S(T); it may of course be empty. Apply the same proof to T+F whenever its relative basic set is nonempty. This includes effective ambient constraints compatible with Max, such as the individual Frege Infinity axiom recorded in the coalesced maximalist model.

An explicit description of the open dense complement is

    S(C) \ S(Max_C) = ⋃{[A=B] : A=B closed pure and C⊬A=B}.

So every failure of Max has a single finite equality witness, while no consistent finite description can guarantee Max. The quantification over all non-theorems is essential to the latter property.

This is a category statement in the space of complete theories. It supplies no probability, no canonical measure, and no claim that an arbitrary labelled-structure space or isomorphism quotient has the same topology.

## 4. The Gallin package is a nonempty clopen locus

By (1),

    S(P_G) = [V_G].

It is nonempty and clopen. It has nonempty interior by construction, whereas the nonempty Max locus has none. The same holds for P_G plus either or both quantified Frege Infinity axioms: replace V_G by the corresponding finite conjunction, which is consistent in full Gallin E=W=ℕ.

Thus the topological contrast survives these Infinity additions without comparing a finite-domain example against an infinite-domain theory. It also has a finite-description interpretation: once V_G is stipulated, every further consistent completion remains within P_G. In contrast, every finite description compatible with Max has a further consistent refinement that violates Max.

The two packages are also incompatible by the existing `maximalist-distinctness-incompatible-with-nd` result and □Plenitude→ND. The topology does not establish incompatibility; that uses the separate mathematical proof. Nor does a nowhere-dense locus amount to an inconsistent theory.

## 5. A nonextensional clopen region inside the Functional Choice locus

There is a finite pure condition implying all of □Functional Choice, with a genuinely nonextensional full Gallin model. This gives a nonempty clopen subset of S(P_F) without assuming that P_F itself is finitely axiomatizable.

For fixed positive natural numbers n,m, let AtMost_n(σ) be the first-order finite-cardinality sentence at type σ. Set

    V_n,m := □ND_t ∧ □AtMost_n(e) ∧ □AtMost_m(t).

For every admitted type τ, define a finite external bound recursively by

    b_e=n,   b_t=m,   b_(στ)=(b_τ)^(b_σ).

C+V_n,m proves □AtMost_(b_τ)(τ) for each fixed τ. The induction uses C5→□BF→□Functionality: an operation is determined by its application table, and a finite input domain with at most b_σ values and finite output domain with at most b_τ values has at most (b_τ)^(b_σ) such tables. This is an ordinary finite pigeonhole argument at each fixed pair of types, expressible without function types ending in e. It is not an object-language quantification over all types.

Fix one input type σ and relational output type τ. At an arbitrary accessible point, a serial relation U from σ to τ has finitely many distinct input representatives a₁,…,a_k covering the domain. Choose y_i with U(a_i,y_i), using only finitely many existential eliminations. Write τ=ρ₁…ρ_rt. Define

    f := λx^σ z₁^ρ₁ … z_r^ρ_r .
           ⋁_(i=1)^k [(x=a_i) ∧ y_i[z₁,…,z_r]].

At x=a_i, C5 makes each equality mask a rigid top/bottom proposition, so f(a_i)=y_i as entities, not merely as actual extensions. Distinct masks are bottom by ND and the matching mask is top by reflexivity. The defining operation is admitted because its output is relational. Thus U(x,f(x)) holds for every x. The same finite argument is valid at every accessible point because the base bounds and ND were boxed, yielding the corresponding □Functional Choice instance. Repeating externally over the admitted types proves the schema.

For n=1,m=4, a full Gallin model with one individual and exactly two worlds satisfies V_n,m and ¬Fregean: its four propositions include contingent ones. Hence

    [V_1,4 ∧ ¬Fregean]

is a nonempty clopen subset of S(P_F). This is a useful finite nonextensional region, not a model with individual Infinity; no such Infinity claim is made in this paragraph. General Gallin low models supply the separate Infinity comparison in `positive-effective.md`.

## 6. Effective hidden-variable axiomatizations cannot remove Max's obstruction

Let L⁺ be a recursive expansion of the pure language by any computably specified auxiliary symbols or sorts. Suppose an effective finitary theory U in L⁺ is consistent, its reducts satisfy C, and its proof system is sound and complete for the intended general Henkin semantics. If all reducts of U-models satisfied Max_C, completeness would make every pure Max axiom a U-consequence. The pure consequences of U are c.e.; they form a consistent c.e. extension of C entailing Max_C, contradicting §3.

Thus no satisfiable r.e. auxiliary Henkin presentation can **force** the Max reduct class, even when the auxiliary structure is later forgotten. This applies to finite effective first-order/typed Henkin descriptions and effective definitional expansions. It does not apply to a non-effective side condition, an uncomputable parameter, full higher-order semantics lacking effective completeness, or a bare structural recipe whose term interpretation is noncomputable. These exceptions matter: a schematic term quotient for the C word problem is computably describable with c.e. equality, but deciding its quotient equality already costs 0′.

## 7. Scope of the comparison

The precise conclusions established here are finite relative axiomatizability and topology of complete theories. The companion notes compare effective presentation and theoremhood complexity. Full Gallin models have a simple recursive type construction but noncompact, non-effective full validity. General Henkin semantics is the appropriate setting for compactness, low-basis arguments and the completion spaces used above. No mathematical theorem here equates naturalness with category, effectiveness, or consistency.

## 8. Perfectness and dense low completions

The later exact degree arguments in `max-degree.md` §§8–10 give a useful refinement. Max is c.e. relative to 0′, but every complete actual pure theory extending Max computes a binary DNR function relative to 0′, and therefore is not computable in 0′. It follows that **S(Max) has no isolated points**. If Γ were isolated, some finite sentence F would make Max+F complete. That theory is c.e. in 0′; completeness would make it decidable in 0′ by racing proofs of a sentence and its negation. Its unique complete extension Γ would contradict the DNR lower bound.

Thus S(Max) is nonempty, compact, metrizable, zero-dimensional and perfect. By the standard topological characterization it is homeomorphic to Cantor space. In particular there are continuum many pairwise distinct complete pure Max theories, and each has a countable general Henkin/BBK model. No full model or effective model is being inferred from this countable-model claim.

The same abstract Cantor-space conclusion holds for S(P_G+Infinity) and S(P_F+Infinity), where Infinity is at least one quantified Frege axiom and the package is consistent. Those theories are c.e., and every complete extension computes a completion of PA by the interpreted Frege arithmetic. A finite condition isolating a completion would make it a decidable complete extension of an arithmetic-interpreting theory, impossible. Consequently the **ambient position** distinguishes the Gallin and Max loci (clopen versus nowhere dense), while their abstract underlying topological spaces can be homeomorphic. This prevents an unwarranted claim of a global topological classification hierarchy.

Low completions are dense in S(T) for every consistent c.e. T extending C: apply Low Basis to the complete Henkin extensions of each consistent finite T+F and then restrict to the pure language. In contrast Max has no low completion and indeed no 0′-computable completion. Relative-low completions are dense in S(Max): apply relative Low Basis to Max+F for every consistent finite F. The resulting complete theories have degrees d with

    0′ <_T d <_T 0′′,       d′ ≡_T 0′′.

The strict lower bound uses the later DNR argument, not Low Basis by itself. These statements describe existence densely among completions, not the degrees of every model.

## 9. Equational conservativity and idempotence of maximalization

Every consistent extension T of Max_C is conservative over C for **closed pure identities**:

    T⊢A=B  iff  C⊢A=B.

If T proved a new identity, it would contain both A=B and the Max_C axiom A≠B. The implication from C follows because T extends C. This remains true even though `max-degree.md` proves that the full theoremhood set of Max_C is Σ⁰₂-complete whereas C's identity theoremhood is Σ⁰₁-complete.

Accordingly, if relative maximalization is defined in the distinctness form

    Maximalize(T) := T + {A≠B : A=B closed pure and T⊬A=B},

then every consistent T extending Max_C is already a fixed point: Maximalize(T)=T. In particular Maximalize(Max_C)=Max_C. Iterating this operation therefore does not automatically yield an oracle-jump hierarchy. Its reference-theory equality problem has stabilized, even though the full actual theorem theory has become harder.

This also pinpoints the modal bookkeeping issue. An arbitrary new actual theorem of a strengthening T must not be necessitated as though it were an original C-theorem. Were that licensed, every new pure theorem P would give the pure identity P=top and violate the displayed conservativity. Optional premises remain optional.
