# Hyperarithmetical axiom sets and standard-number model bases

OpenAI Codex (GPT-6), 22 October 2026. Independent ordinary-mathematics audit of the proposed generic extension, now also stated in `positive-effective.md` §20. No main records edited and no Lean or human-check claim.

## 1. Audited lemma

**PASS.** Fix an admitted counting type σ and a set T of original pure axioms, computably enumerable in a fixed hyperarithmetical oracle A, with C among its consequences. Assume there exists a BBK model satisfying T+I_σ whose actual N_σ-domain is exactly the distinct standard numeral denotations. Put U=T+I_σ. Then each of the following solution families has exactly HYP as its common Turing information and as its common hyperarithmetical information:

* complete original pure theories realized by such standard-number U-models;
* canonical adequate countable BBK codes for such models, including parameterized term interpretation and actual truth;
* numbered original application/equality/valuation codes for such countable models, with effective sorted-domain enumeration.

Every solution in these families is nonhyperarithmetical. Each family has a solution Q with Q<_T O, O not≤_h Q, and ω₁^Q=ω₁^CK. Each family has no least Turing degree or hyperdegree, and its class of oracles computing some solution has no least Turing degree. Given any countable family of nonhyperarithmetical reals, there is one solution avoiding every member even under hyperarithmetical reducibility.

The below-O existence statement and arbitrary countable avoidance are separate conclusions; no simultaneous below-O bound for an arbitrary, ineffectively specified avoidance family is needed here.

If T already entails I_σ, U is just T. The formulation with U also covers the proposal in which only the particular standard-model witness is assumed to satisfy I_σ. A hyperarithmetical axiom set is a special case by taking its own characteristic set as A. Conversely an A-c.e. axiom set with hyperarithmetical A is itself hyperarithmetical, since it is computable in A′.

## 2. The code class and removal of the parameter

Use a fixed effective language with infinitely many fresh constants at each admitted type and the usual successive Henkin witness axioms. Extend the whole fixed C schema to this language, keeping every optional T axiom and every reference-theory schema in its original specified language. The witness theory U^H is A-c.e. Fresh-constant conservativity preserves H-theoremhood in Logical Equivalence; no optional assumption is necessitated.

Let K_U be the set of complete consistent decision codes D extending U^H and satisfying, for every closed term u of numerical type ν_σ,

    D(N_σu)=1 ⇒ ∃n∈ω D(u=numeral_σ(n))=1.          (2.1)

Completeness, consistency, deductive closure and containment of U^H have a Π⁰₁(A) description in the usual characteristic coding. Equation (2.1) is Π⁰₂ in D. Consequently K_U is Π⁰₂(A), hence arithmetical in the **fixed** hyperarithmetical parameter A.

The passage to lightface analytic is legitimate. Since A is hyperarithmetical, its singleton {A} is lightface Δ¹₁. If R(D,Z) is the arithmetic predicate defining the displayed code conditions with oracle Z, then

    D∈K_U ⇔ ∃Z [Z=A ∧ R(D,Z)].                    (2.2)

Use a lightface Σ¹₁ definition of Z=A and combine its real witness with Z; the remaining R is arithmetic. This is a lightface Σ¹₁ definition of K_U. No jump predicate inside the theory, no self-certifying J-coordinates, and no recovery of A from D are needed for this descriptive-set-theoretic step.

The restriction to fixed hyperarithmetical A matters. For an arbitrary additional real parameter one obtains only relative analyticity, with correspondingly relativized basis conclusions. Nothing here uniformly recognizes valid hyperarithmetical descriptions or supplies one uniform ordinal bound for varying theories.

## 3. Exact nonemptiness and model output

The assumed standard U-model expands to the fresh constants by successive actual witnesses. Its complete expanded-language theory belongs to K_U. This remains valid if the starting model is uncountable; the language and set of closed terms are countable. Thus the nonempty analytic class follows from standard-model existence, not merely from consistency.

Conversely, each D∈K_U gives the usual BBK term model. Choose the least closed-term code in each D-identity class, substitute representatives to interpret terms under finite assignments, and decide actual proposition truth by D-membership. Every numerical object has a closed-term representative; (2.1) makes any such object satisfying N_σ equal to a standard numeral. The I_σ interpretation supplies distinct numerals and standard arithmetic recursion on them. Hence the output is a countable standard-number U-model.

The adequate model code and its original pure complete theory are computable from D without an additional oracle. Dropping the full interpreter gives the specified application/equality/valuation output, also computable from D. These are the only output reductions the basis proof needs.

## 4. The lower bound survives the weaker original code

The fixed pure term L_σ from `positive-effective.md` §18 is available in every C-model satisfying I_σ plus external number standardness. Its actual numerical extension is a fixed point of the fixed positive arithmetic operator from Gregoriades. The proof does not require the represented sets to be externally powerset-full: arithmetic comprehension supplies Φ(X), and impredicative comprehension supplies the intersection L of the available prefixed sets; monotonicity then proves Φ(L)=L. Standard arithmetic makes this an actual external fixed point.

Gregoriades's Theorem 1 excludes hyperarithmetical fixed points, while Lemmas 13–14 make every hyperarithmetical real a fixed standard numbered column of every such fixed point. Thus each hyperarithmetical H reduces to L_σ, by a reduction with a finite column index depending on H. No effective listing of valid indices for all HYP is asserted. The primary statements are in [On a Question of Jägers, v2](https://arxiv.org/pdf/1905.09609), printed pp.2–3 and 7–8.

A complete pure theory computes L_σ by its answers to the computably generated sentences L_σ(numeral n). An adequate code evaluates those same sentences.

For the weaker original code, hardcode the three presentation indices

    0_ν,   Suc_ν:ν→ν,   L_σ:ν→t.

Starting with 0_ν, n iterations of application compute the nth numeral. Another application computes L_σ at that numeral, and the actual valuation reads its truth. Total application is computable from its decidable graph by searching the effectively enumerable output domain. This computes the nonhyperarithmetical fixed point and each of its HYP columns.

The three denotations need not be uniformly identifiable in an unnamed presentation. Their finite indices give a valid reduction for each code, and named indices make it uniform. Neither a general lambda interpreter nor an elementary diagram is required for this lower bound. Removing valuation requires a separate truth-recovery argument, such as a supplied Actuality witness and the relevant Boolean operation; it is not justified for a generic C-model.

## 5. Basis, common information, and no least degree

Apply the checked Kleene–Gandy basis theorem to the nonempty lightface analytic K_U. It supplies D≤_T O with O not≤_h D and ω₁^D=ω₁^CK. Any of the outputs Q from §3 is reducible to D and is nonhyperarithmetical by §4. Therefore Q<_T O, O not≤_h Q, and ω₁^Q=ω₁^CK.

If X is not hyperarithmetical, the Kreisel avoidance theorem gives D∈K_U with X not≤_h D. Its output Q therefore cannot compute X and does not even make X hyperarithmetical. Conversely every hyperarithmetical X is Turing reducible to every solution by §4. This proves both versions of the exact common-information assertion. The countable-avoidance version follows from the corresponding countable basis theorem.

The relevant primary source is Harrington–Shore–Slaman, [Σ¹₁ in every real in a Σ¹₁ class of reals is Σ¹₁](https://math.berkeley.edu/~slaman/papers/Sigma1116.pdf), draft of 11 July 2016: the Kreisel explanation at printed p.2, countable avoidance Theorem 2.6 at p.6, and Kleene–Gandy Theorem 2.9 at p.7. Its statements apply to the class established above without adding A as a remaining parameter.

A least solution degree would itself be common information, hence hyperarithmetical, contradicting §4. The same reasoning works for hyperdegrees. If a least oracle degree computing some solution existed, choose a solution below that oracle; the solution's own degree is also capable, so leastness would make them equal and give the already excluded least solution degree. These are no-least assertions, not no-minimal-element assertions or spectra of one fixed model.

## 6. Additional strengthening: preserve a supplied standard completion at its exact degree

**Proved supplement.** Given the characteristic function of a complete original pure Γ⊇C+I_σ, promised to have a standard-number model, one uniformly constructs a standard-number BBK model of Γ whose adequate operational code has exactly deg(Γ).

Use the Γ-guided Henkin construction in `exact-completion-model-spectra-20261022.md` §5. For a finite expanded-language commitment set Δ, consistency with Γ is equivalent to membership in Γ of its pure existential closure E_Δ, obtained by replacing all newly adjoined constants by typed variables. This equivalence also means that every such consistent finite Δ is realizable by an interpretation of its constants in **one fixed standard model of Γ**: that model satisfies E_Δ because Γ is complete.

In addition to the ordinary sentence-decision and witness requirements, schedule every closed numerical term u. At its stage, first decide N_σu consistently using the existential-closure test. If it is false, no further commitment is needed. If it is true, search n=0,1,… until

    E_(Δ∪{u=numeral_σ(n)}) ∈ Γ,

where Δ now includes N_σu. This search terminates: realize Δ in the fixed standard Γ-model; the denotation of u is then one standard numeral, so that equality gives a true existential closure. Add the equality and continue.

Every finite stage remains Γ-consistent. Fair scheduling decides all sentences, provides all existential witnesses, and makes every eventual term satisfying N_σ a standard numeral. Other objects of the numerical sort may remain nonnumbers. The limit D and its canonical term model are Γ-computable. Their original pure theory is Γ, so evaluation gives the converse reduction and the model code has exactly Γ's degree.

Freshness is checked against the whole original language and the current finite commitment set; the scheduled term may introduce additional constants, which are included in the existential closure. An existential witness uses a constant absent from the current commitments. These finite conventions prevent any clash between number-standardization stages and witness stages.

This is a promised-input construction: if Γ has no standard model, a numeral-search stage may fail to terminate. No algorithm deciding whether Γ admits a standard model is obtained. Under the stated promise, it yields a uniform equivalence between the standard complete-theory and adequate standard-model solution problems, with a degree-preserving construction from each supplied completion. It does not establish degree preservation when the output is further reduced to bare application/valuation data.

The same scheduling works for a fixed computable list of counting types, provided one Γ-model is standard at all of them. In an auxiliary language with an explicit world sort, standardness at every world is handled by scheduling every closed world term together with every closed numerical term, under the stronger promise of one Γ-model standard at every such world. The present original-BBK lemma asserts standardness at the actual evaluation point; it does not invent world objects absent from that language. Conceptually this is effective omission of the recursive nonstandard-number type relative to a complete Γ. The parent ordinary-mathematics agent independently checked the finite-consistency and numeral-search argument; this is an AI-agent audit, not a human-check attribution.

## 7. Applications and boundaries

The standard coalesced Max root supplies the needed existence hypothesis for old Max at counting type e, so its application is unconditional once that recorded construction is accepted. Every fixed finite iterated theory T_n has a hyperarithmetical axiom oracle; the generic theorem applies only **if T_n has an I_σ+Std_σ model**. The same conditional statement applies to SP and to a 0^(ω)-c.e. limit theory. Their ordinary consistency, and the availability of standard positive Gallin models, do not establish this stronger premise.

No nonstandard-number model is ruled out by the basis result. Indeed any consistent A-c.e. U with hyperarithmetical A has a hyperarithmetical adequate Henkin model by relative Low Basis, so the lower bound forces that particular model to be nonstandard. This also separates unrestricted from standard model construction even for a proposed uniform converter using any one fixed hyperarithmetical oracle.

The generic theorem requires no positive Gallin representation and no actual infinitude of the individual domain beyond the explicitly stated arithmetic/standardness hypotheses. It concerns original BBK semantic data, not arbitrary category/action presentations.

Validation: no main records were changed. The required validator is run after saving this report; its result is given in the parent update.
