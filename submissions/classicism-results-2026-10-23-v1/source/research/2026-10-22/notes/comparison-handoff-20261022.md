# Computability and model comparison

22 October 2026. Mathematical results, scope and proof references.

For an overview, see [comparison-root-final-handoff-20261022.md](comparison-root-final-handoff-20261022.md).

## 1. Scope and notation

Keep the original relational type system and C fixed. Write B = C + necessary Plenitude = C5 + Atomicity, F = C + necessary Functional Choice, and Max = the original pure Max_C. SP is the original Strong Possibility. Its consistency is not established.

An adequate code includes term interpretation and actual valuation. Where application/equality alone suffices, this is proved separately and may use finitely many hardcoded object indices. Oracle thresholds below concern the ability to compute some model or completion, not the degree spectrum of a fixed isomorphism type. Weak Infinity means the external collection of all finite domain-size lower bounds; the quantified Frege Axiom of Infinity is stronger.

In the arithmetic sections, I_sigma means the background's arithmetic premise Diamond I*_sigma, where I*_sigma asserts the Peano zero/successor conditions on the Frege numbers. It is not the quantified Frege Axiom of Infinity of the counting domain sigma. Max and SP imply the arithmetic premise even when the actual individual domain is finite; never infer actual individual infinitude from that premise.

## 2. Main unrestricted comparison

| Theory / hypotheses | Theoremhood | Oracle capacity for an adequate model | Common information in all codes |
| --- | --- | --- | --- |
| B or F, with weak Infinity at a fixed admitted type | Sigma-1 complete | ordinary PA degrees | computable sets |
| original Max | Sigma-2 complete | PA degrees over 0′ | sets below 0′ |
| original SP, if consistent | Sigma-3 complete | PA degrees over 0′′ | sets below 0′′ |
| optional T_n, if consistent, n >= 1 | Sigma-(n+1) complete | PA degrees over 0^(n) | sets below 0^(n) |
| optional T_omega, if every finite stage is consistent | Sigma-1(0^(omega)) complete | PA degrees over 0^(omega) | sets below 0^(omega) |

Each theoremhood statement is robust under consistent strengthenings enumerable in the indicated axiom oracle. Finite-condition consistency has the complementary complete complexity. Relative Low Basis supplies matching low models; there is no least solution degree. Max's pure identity diagram, including at standard points, is exactly C's pure identity theorem set, of degree 0′. This does not give a degree-0′ adequate Max model.

Proof routes: `positive-effective.md` §§13–17 and 22; `max-degree.md` §§8–10; `strong-possibility-degree.md` §§2–6; `iterated-possibility-degrees.md` §§1–4; `limit-possibility-degree.md` §§2–7; common-information proof in `effective-refinements.md` §8.

The non-r.e. Max conclusion itself is already in Bacon–Dorr's 1 July 2022 draft, §2.4 p.35 n.52. That draft §2.6 p.42 also explicitly states the relevant Strong Possibility reflection. Exact degree refinements here are session deductions; do not reattribute the original reflection as a new result.

## 3. Standard numbers change the problem

For any fixed hyperarithmetically enumerable extension of C + I_sigma which has a model with externally standard N_sigma at its actual point:

* Every adequate standard code is nonhyperarithmetical and computes every hyperarithmetical real, individually.
* There are standard codes strictly below Kleene's O, with omega_1^code = omega_1^CK and O not hyperarithmetical in the code.
* Exactly HYP is common information in all standard solutions, for Turing or hyperarithmetical reducibility. There is no least solution degree.
* No fixed hyperarithmetical procedure converts every unrestricted solution into a standard one.

Standard models exist unconditionally for B and F with the specified Infinity packages, and for original Max. This does not assert standard-model existence for every consistent strengthening of a positive package. Applying these conclusions to SP or T_omega requires a standard-model existence hypothesis in addition to consistency. No such existence result has been obtained here.

Proof routes: `positive-effective.md` §§18–20. The lower bound uses the actual omega-model of full second-order comprehension and Gregoriades' positive arithmetic fixed-point operator; the upper/basis assertions use the checked Harrington–Shore–Slaman source. The code and arithmetic qualifications matter.

Ordinary finitary compactness shows that no consistent finitary theory extending C + I_sigma can force all its models to have standard N_sigma, irrespective of axiom complexity. For hyperarithmetical axiom theories, the low-basis construction gives the stronger conclusion of a hyperarithmetical nonstandard code.

For B or F with I_e and externally standard N_e, finite-condition satisfiability is Sigma-1-1 complete and validity Pi-1-1 complete, already in the pure identity fragment; the specified stronger Infinity packages have the same bounds. Standard-N_e Max has the same whole-sentence complexities, but its pure identity fragment remains Sigma-1 complete: every Max model fixes that fragment. See `positive-effective.md` §21 and `max-degree.md` §13.

Full standard Gallin witnesses and the full standard coalesced Max root realize every external numerical branch graph, so their complete actual pure theories compute O. The sub-O standard models are other models, not elementary submodels preserving those full theories.

## 4. Presentation and actual truth

An Actuality witness a recovers actual valuation by p true iff a meet p = a. Thus original application/equality codes under Actuality inherit the corresponding valuation-code lower bounds, including the standard-number result. For the ordinary PA lower bound, Actuality is unnecessary: even possible weak Infinity at any admitted type suffices in C, by compiling the finite-trace proposition and testing whether it is nonbottom. A B/F model has a computable application/equality presentation exactly when both bases are finite, equivalently when it is a finite-base full Gallin structure.

For Max without an Actuality hypothesis, application/equality alone is known here to compute 0′ by the fixed finite tuple of term indices in `max-degree.md` §4; no matching complete classification of bare applicative presentations is asserted. The information shared by all such bare codes is exactly the sets below 0′. A least bare solution degree exists if and only if a degree-0′ bare model exists, which remains unresolved; see `effective-refinements.md` §10. Adding actual valuation gives the PA-over-0′ lower bound. Conditional SP + Vicinity yields 0′′ from application/equality; conditional SP + Actuality yields PA-over-0′′. These are conditional lower bounds, not consistency claims for either extension.

No closed pure proposition can witness Actuality in a Max model, and no actually true closed pure proposition can be a Boolean atom there. This does not make the entire pure proposition algebra atomless: finite Fregean isolators can be false pure atoms in the profile construction. The interval below I_e in the pure C Lindenbaum algebra is atomless, and every actual Max completion lies in that interval.

More generally, every consistent c.e. pure-complete extension of C has a finite actual domain at each admitted type, with its exact cardinality recursive as a function of the type code (the theory is fixed). The stronger possible-trace argument gives a recursive necessary finite upper bound at each type: possible arbitrarily large finite domains would already yield a binary DNR function. These results close the local-finiteness question in the profile note §18 and bound accessible-world domains; they neither prove B nor make every object pure-definable. See `effective-refinements.md` §§9.3–9.4.

Such a complete theory also determines a unique actual typed application/valuation structure, including the pure-term interpretation, up to type-preserving isomorphism; that structure has a computable adequate copy using fresh Henkin names. This uniqueness concerns the actual typed structure, not arbitrary world, category, or action presentations. See `effective-refinements.md` §9.5.

The necessary finite bounds also force necessary Actuality, Atomicity and Boolean Completeness at every relational type, and every necessary Relational Choice instance, including individual outputs. The last principle chooses a currently functional subrelation by a finite equality table; it does not produce an output-valued operation. A finite coalescence over one finite extensional component has a computable complete pure theory and all these necessary principles, but fails C5 and current Functional Choice at (t,t). See `positive-effective.md` §23, especially §23.6.

Routes: `positive-effective.md` §22; `sp-diagram-hat-audit.md` §6; `effective-refinements.md` §9; the existing `profile-root-construction-20261022.md` construction for false atoms.

## 5. Topological comparison

B has one finite relative axiom, V_G = necessary ND_t and Atomicity_t. Therefore S(B) is a nonempty clopen part of S(C). Max's completion locus is closed nowhere dense, including in every consistent c.e. ambient region which meets it. No consistent c.e. auxiliary Henkin axiomatization with a computable interpretation of the original language and effective sound and complete consequence can force all its reducts to satisfy Max; a raw structural recipe or a quotient with merely c.e. equality is a different kind of presentation.

There is also a concrete single-axiom strict intermediate theory: B is strictly weaker than C+□FunctionalChoice_(t,t), which is strictly weaker than F. A second intermediate C+□Sel_t packages all Choice instances with output t. Here Sel_t asserts an operation choosing a member of every nonempty property of propositions; it is equivalent to FunctionalChoice_(tt,t), whose input is tt. The second intermediate entails the first, but their equivalence or strict separation is not settled here. The two nominal models below prove the strict outer separations. More generally, one global-selector assertion at each relational output type packages all input-type Choice instances; whether finitely many output assertions suffice for F remains unresolved.

For both B and F, isolated completions are exactly the finite-base full Gallin completions, equivalently decidable complete theories. Their first Cantor–Bendixson derivative is already perfect, and equals the union of the weak-Infinity-at-e and weak-Infinity-at-t loci, also the weak-Infinity-at-et locus. It is an effectively closed class, topologically a Cantor space, with dense low completions. Each fixed nontrivial ambient Functional Choice failure locus in S(B) is a nonempty clopen perfect Cantor space with ordinary PA model capacity; such failure forces weak Infinity at both its input and output types.

Despite the successive jumps in theoremhood, in fixed recursive sentence-bit coding in Cantor space, the original Max, conditional SP, later finite optional stages, and omega-stage completion loci all have absolute lightface Pi-2 descriptions: the code certifies its own finite jumps or omega-join. They have no nonempty lightface Sigma-2 subclass. These loci are topologically closed; no topological Pi-2 completeness claim is intended.

Routes: `theory-space-comparison.md`; `gallin-comparison.md` §§14.1–14.4 and 21.2–21.3; `effective-refinements.md` §§2–5; `strong-possibility-degree.md` §8.3; `limit-possibility-degree.md` §8.

## 6. A concrete positive model separating all ambient Choice

The finite-support construction with E = omega fixed pointwise, W = omega, all world permutations, finite/cofinite propositions and finitely supported higher maps satisfies B, both boxed quantified Infinity axioms, and standard Frege numbers. Its ordinary hereditary e-core is full and satisfies every ordinary core-translated Choice instance. Nevertheless every admitted nontrivial ambient unary Functional Choice instance fails, necessarily; nonempty polyadic inputs follow by fixing other arguments. Nullary choice is excluded from that statement.

There are countable standard elementary submodels, with restricted rather than full cores. Separately, the c.e. theory of B, both boxed Infinity axioms, core Choice, and all those boxed ambient failures has low countable models, whose Frege arithmetic is nonstandard. These are different constructions preserving different properties.

A second variant moves the individuals E=omega and fixes two worlds. It satisfies B and boxed individual Infinity with standard individual numbers. Every type built only from t is finite and full, so all Choice instances with such an input or output hold. Every unary e-input Choice instance also holds, hence so do finite polyadic e-input instances by repeated choice and currying. Yet Choice_(et,et) fails by the impossibility of selecting an individual singleton from each two-element rigid individual property with finite support. Its externally countable individual domain is internally amorphous and relationally Dedekind-finite, and admits no numerical code at any counting base. This variant's ordinary e-core is not claimed to be full or choice-satisfying.

Route: `gallin-comparison.md` §§12, 12.1, 17 and 20. The finite-support machinery is standard nominal mathematics, with the checked Pitts JACM 2006 source. The specific typed model verdicts are this session's application, not a claim to invent the construction. These examples alone do not settle finite relative axiomatizability of F.

## 7. Optional extensions and boundaries

The finite and omega possibility iterations are explicitly new optional theories. They preserve the original C/Max reference theories and do not silently redefine SP. If T_3 is consistent, it refutes actual Vicinity and Actuality; if every finite stage is consistent, their union gives all external finite hat inequalities. This does not by itself express the internal No Collapse axiom with an internally closed operator family.

Ordinary relative distinctness maximalization is different and already idempotent here. Every consistent extension T of Max_C has exactly C's closed pure identity theorems: any new identity would contradict its Max_C distinctness axiom. Recomputing the distinctness schema relative to T therefore adds nothing. The optional jump hierarchy instead iterates hatted possibility and reflection; it is not iteration of this stabilized distinctness operation.

An external computable infinitary Pi-2 sentence can describe old Max without changing its object-language entities. Genuine countable disjunction inside lambda comprehension is different: every number at every world must then be the value of a standard numeral, and at I_sigma worlds these numeral values are distinct. This conflicts with the nonstandard arithmetic possibilities forced by old Max. External standardness only at the evaluation point remains consistent with Max. Unrestricted infinitary comprehension also has separate uncountability consequences.

Counting-base standardness transfers precisely. Already C+I*_rho gives a canonical successor-preserving surjection from N_rho to N_sigma, so externally standard distinct source numerals imply that every target number is a standard numeral value. Target I*_sigma makes those values distinct; alternatively target weak Infinity gives both distinctness and quantified Infinity_sigma. With both I* hypotheses, external Peano standardness is equivalent at the two bases. These are current-point claims in C. Under B, numberhood and numeral denotations are world-invariant, so actual standardness propagates to all represented worlds. In particular B plus both base Infinity axioms and standard N_e has standard Frege numbers and quantified Infinity at every original type at every world.

Routes: `iterated-possibility-degrees.md`; `limit-possibility-degree.md`; `theory-space-comparison.md` §9; `gallin-comparison.md` §§13 and 19. No SP or higher-stage consistency proof has been found. Finite relative axiomatizability of the full F schema is also unresolved by the checked sources and constructions; its schema form alone does not prove failure of a finite axiomatization.

## 8. Verification boundary

The notes include independent mathematical cross-audits and direct source checks. Repository validation passed: 132 principles, 447 results, 162 models. The runtime is the existing `.reproduction/classicism-research-venv`; no toolchain or packages were installed. Statements in the notes remain research arguments to be reviewed before any record promotion. No current proof is labelled human-checked or Lean-verified.
