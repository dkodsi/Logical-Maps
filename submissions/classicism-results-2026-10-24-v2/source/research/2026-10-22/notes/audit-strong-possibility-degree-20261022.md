# Referee audit: Strong Possibility and the second-jump oracle

OpenAI Codex (GPT-6), 22 October 2026. Independent ordinary-mathematics audit of `strong-possibility-degree.md`; no human-check attribution, Lean work, main record edits, or external messages. The fixed original pure relational language and fixed C/Max reference theories are retained.

## 1. Verdict

**PASS, conditional on Con(SP):** the complete-theory and adequate countable BBK model problems have exactly PA-over-0′′ oracle capacity, while Th(SP) is Σ⁰₃-complete under ordinary computable many-one reductions. The same conclusions hold for every fixed consistent 0′′-c.e. strengthening. The claimed relative-low existence bounds follow under that same consistency hypothesis.

No proof of Con(SP) is supplied or implicit. The implication “every consistent effective strengthening has a high degree” is not an inconsistency argument. The source attribution is appropriately limited: the modal reflection direction precedes these computational deductions in the published-source draft; the computational claims are not attributed to its authors.

The needed presentation conditions are explicit and adequate. A full BBK operational code must include uniform finite-term interpretation and the actual proposition valuation. For the smaller applicative encoding, decidable application graphs over enumerable numbered domains and a valuation suffice for a nonuniform degree lower bound. Bare application/equality data or an unspecified action/category atomic diagram do not receive that conclusion.

## 2. Exact SP definition and consistency boundaries

The record `principles/strong-possibility-r.yaml` defines precisely

    Bp := ∃q(q∧□(◇q→p)),    Dp := ¬B¬p,
    SP := C + {DP : P closed pure and Max_C+P consistent}.

The side condition is external consistency with the unchanged original Max_C. The source leaves Con(SP) open. In the [author-hosted Classicism draft](https://andrew-bacon.github.io/papers/Classicism.pdf), dated 1 July 2022, §2.6, printed p.42, the authors explicitly say, “We do not know whether Strong Possibility is consistent.” This is not the bundle's 16 May 2023 pagination.

SP⇒Max is recorded with a sound proof. For C-consistent pure P, Max proves ◇P and is consistent, so ◇P is Max-consistent. SP gives D◇P; C proves D≤◇, hence ◇◇P and then ◇P. This yields the Possibility form of pure Max and therefore its Distinctness form.

A useful stress test is the separate proved record `strong-possibility-and-infinity-e-incompatible.yaml`: SP implies exactly one individual. This does not contradict the degree proof. Its arithmetic antecedent is I_e=◇I*_e, inherited from Max, not the individual Infinity schema or the strong individual Frege Infinity axiom. Frege number objects live at the relational type ν=(et)t; infinitely many such intensional cardinality objects need not be realized by actual individual predicates of their respective finite cardinalities. No individual-Infinity premise is added anywhere in the audited SP argument.

## 3. Finite-support persistence and exact reflection

Lemma 2.1 is valid. A finite proof Max⊢A uses a finite conjunction Q of Max inequality axioms ¬E_i. The deduction theorem gives C⊢¬A→∨E_i. NI gives each E_i→□E_i, and normal modal reasoning gives ∨E_i→□∨E_i. Hence C⊢¬A→□¬Q, equivalently C⊢◇Q→A. Necessitating this genuine C-theorem yields C⊢□(◇Q→A). The actual Max theorem Q then witnesses BA.

There is no necessitation of Q as an optional hypothesis. Ordinary □-closure of Max is not assumed. The empty-conjunction case uses Q=⊤.

If Max⊬A, Max+¬A is consistent, so SP includes D¬A, i.e. ¬BA. Double-negation replacement inside the modality is justified by the fixed C logical identities, rather than by an unlicensed contextual use of a mere optional material equivalence. Combining this with the positive persistence direction proves the exact signed reflection diagram

    SP ⊢ BA     when Max⊢A,
    SP ⊢ ¬BA    when Max⊬A.

The proof works syntactically whether or not SP is consistent. Consistency is needed to treat these signs as a decision procedure from an SP extension or as actual model truth. The note observes that distinction.

## 4. The definable 0′′ predicate and finite oracle computations

The chosen formula J2(n)=B H(n,J1) is numeralwise correct provided the stated fixed-formula reduction n∈0′′ iff Max⊢H(numeral n,J1) is available. That reduction passes its separate audit: the full coalesced Max root has an available property selecting exactly its standard Frege numerals at the root, with universal component predicates; this forces N to contain exactly those numerals. Arbitrary root extensions similarly give the graph predicates separating wrong sums and products. J1 then agrees with 0′ on the whole numerical domain of this particular reference model.

The standard reference model is a Max model, not an SP model. It is used only to refute the relevant Max theoremhood claim when the genuine oracle machine diverges. The SP model itself may have nonstandard arithmetic and, as §2 notes, only one individual.

**Alternative eliminating this model dependency.** Let p be the ordinary computable reduction supplied by the self-indexing proof in `max-degree.md` §10.4, so

    n∈0′′ iff Max⊢H_0(numeral p(n),J1).

Choose the standard deterministic arithmetic graph Comp_p(v,w) for the computation of p and define, with number quantifiers explicitly restricted to N,

    Q(v):=∃w∈N (Comp_p(v,w)∧H_0(w,J1)),
    J2*(v):=B Q(v).

For each standard n, its finite computation and the PA uniqueness theorem prove Q(numeral n)↔H_0(numeral p(n),J1) in Max. Thus exact reflection makes J2* correct for 0′′ on every standard numeral. PA need not prove that p is total: the verification is separately finite for each standard input. This is a valid alternative to the displayed J2, not a silent change to its definition.

For either version, an actual finite 0′′-oracle computation makes only finitely many standard queries. The correct positive and negative J2 literals verify that specific computation in SP. The impredicative definition of N supplies induction for formulas involving the definable J2, so ordinary oracle-machine determinism is available. A nonstandard apparent run cannot coexist internally with a verified standard run of the other output bit. No arithmetic soundness or external standardness assumption is used here.

All types in these definitions end in t where required. Numerical successor has type ν→ν, which is permitted because ν is relational; there is no prohibited e→e operation.

## 5. DNR lower bound, upper construction, and the code boundary

The one-query extraction d(n)=1 iff H_0(numeral n,J2) belongs to the supplied completion is binary DNR^0′′. Output 0 gives the opposite extracted bit by finite verification; output 1 gives the opposite bit by verification plus determinism. A binary DNR^A function computes A by querying it on indices of programs returning their oracle's kth bit, so the relative degree definition includes 0′′ itself.

An adequate BBK operational code computes the pure completion by evaluation. This is faithful to the source model definition: Bacon–Dorr, [Classicism](https://andrew-bacon.github.io/papers/Classicism.pdf), Definition 3.1 and Theorem 3.2, printed pp.43–45 of the 2022 draft, specifies assignment-dependent term interpretation and a separate proposition valuation. Its n.64 gives the complete witness-theory quotient construction. The audited upper construction computes exactly these data, using least term representatives of decided identity classes.

For application/equality/valuation codes, finitely hardcoded indices for 0_ν, Suc_ν and G=λn.H_0(n,J2) suffice: iterate successor, apply G, and read the actual valuation. Decidable application graphs plus effective domain enumeration permit each application value to be found by search. This establishes the stated Turing-degree lower bound for every such presentation. Discovering those finitely many unnamed indices uniformly is not asserted.

“Atomic diagram” alone is not enough information to classify a code. An atomic diagram explicitly naming the relevant evaluation operations and truth predicate is adequate; application plus the valuation is enough for the preceding nonuniform bound. Without valuation or an independently proved way of recovering it, no PA-over-0′′ conclusion follows from this proof. The pure closed-identity diagram of every SP model remains E_C, of degree 0′, so it must not be substituted for the actual pure theory.

The upper construction uses the 0′′-c.e. SP theory, standard witness constants, and DNR proof-race decisions. The fresh constants must extend the entire fixed C schema conservatively, and the SP side condition must remain restricted to the original pure sentences. This is the same language convention already stated for Max; making it explicit for SP would be a useful editorial clarification. It does not require any new principle. The parameter-elimination argument in `completion-space-parametrization-audit-20261022.md` §5 verifies conservativity without changing H-theoremhood in Logical Equivalence.

Relative Low Basis gives a completion above 0′′ with jump 0′′′. The model code is below that completion and has the DNR lower bound, hence its jump is exactly 0′′′; its degree is strictly between 0′′ and 0′′′. Both strict inequalities are justified, not inferred from lowness alone.

## 6. Robust Σ⁰₃ theoremhood and completion-space corollaries

The two-search self-indexing proof in §6 is valid with A=0′′. The index compiler is ordinary computable; only the compiled program uses A. Disjoint A-c.e. supersets of the two diagonal output sets yield the stated ordinary many-one reduction from A′=0′′′. No extra oracle is used to calculate the reduction, and no standard SP model is needed.

The topological and pointclass statements in §8 also pass. In particular:

* Nowhere density inside S(Max) follows because an open region contained in S(SP) would give a consistent 0′-c.e. theory entailing SP, contradicting the reflection proof's oracle bound.
* The no-isolated-point argument correctly uses 0′′-c.e. proof races to make an isolated completion 0′′-computable.
* A nonempty Σ⁰₂(0′) subclass would have a nonempty Π⁰₁(0′) component and hence a completion computable in 0′′ by relative Low Basis, impossible.
* The absolute Π⁰₂ self-certification in §8.3 is legitimate: the bounded oracle simulations query only finitely many designated Y bits; the two jump equations force exactly 0′ and 0′′; and acceptance of an oracle enumeration is Π⁰₁ after substituting those bits. No uniform replacement of arbitrary Y-dependent quantifiers by a fixed 0′ oracle is being made.

Thus the absolute Π⁰₂ upper bound does not lower the model-construction oracle threshold. The relevant class is not being treated as Π⁰₁(0′).

## 7. Safe strengthening available from the companion exact-spectrum proof

Under Con(SP), the finite-output hypothesis of `exact-completion-model-spectra-20261022.md` applies verbatim with A=0′′ and h_e=H_0(numeral e,J2). Its independent-sentence splitter and reversible decision-plus-bit construction therefore give exact degrees across the whole SP completion class: **every PA-over-0′′ degree is the exact degree of a complete pure SP theory**, and every completion has such a degree. The complete-theory-preserving Henkin construction gives an adequate countable SP model code of that exact degree.

This remains conditional and ranges over all models of SP; it is not the spectrum of the copies of one fixed isomorphism type. It also corrects only an unnecessary limitation in the current §5 wording: preserving a supplied complete theory is possible uniformly without a higher oracle, as the separate proof establishes.

No substantive gap was found. The only suggested clarifications are to spell out the original-pure restriction during SP Henkinization and to retain an explicit operational/valuation convention whenever “model code” or “atomic diagram” is used.

Validation: no main records were edited. The required bundle validation is run after saving this report and reported in the parent update.
