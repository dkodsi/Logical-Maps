# Independent hostile audit: exact-degree standard Henkin construction

22 October 2026. Gallin-audit agent. Audited `audit-hyperarithmetical-standard-model-basis-20261022.md` §§2,6 against `exact-completion-model-spectra-20261022.md` §5, and rechecked the cardinal assumptions of `countable-support-choice-countermodel-20261022.md` §9. Ordinary mathematical audit; no main records, Lean, human-check attribution, or novelty claim.

## 1. Exact-degree supplement: PASS

Input: the characteristic function of a complete consistent original pure theory Gamma extending C+I_sigma, with the external promise that Gamma has a model whose actual N_sigma extension is exactly its distinct standard numeral objects. Output: a countable standard-number BBK model with complete original theory exactly Gamma, and canonical adequate operational-plus-truth code of degree exactly deg(Gamma). The uniformity is relative to the supplied complete Gamma and the standard-model promise.

The strongest useful invariant is the following. Fix one promised standard Gamma-model M for the proof only; the algorithm never accesses M. If Delta is the finite set of current commitments in the fresh-constant language, let E_Delta be its pure existential closure after replacing all fresh constants occurring in Delta simultaneously by distinct appropriately typed variables. Maintain

    E_Delta belongs to Gamma.

Since M has complete theory Gamma, this says exactly that Delta can be realized by an interpretation of its finitely many constants in M. Different stages may use different interpretations in M: no coherent infinite embedding into that one M is claimed or needed. The actual commitments themselves increase monotonically.

For any sentence chi, if E_(Delta+chi) belongs to Gamma, adding chi preserves the invariant. Otherwise every realization of Delta in M satisfies not-chi, so E_(Delta+not-chi) belongs to Gamma. This gives a decidable choice using Gamma alone. Conversely the existential-closure criterion agrees with Gamma-consistency: Delta proves E_Delta by existential introduction, while any E_Delta in Gamma has the just-described model realization.

Fresh expanded C instances are valid in every expansion of M. An H-proof mentioning finitely many new constants remains an H-proof after replacing them by variables, with capture avoided. Its Logical Equivalence instance is therefore a parameterized instance of the fixed C schema. This introduces no equivalence derived from Gamma or an optional axiom into the H-theoremhood gate. Optional axioms, including any pure maximalist reference schema, retain their original language and are not expanded to the new constants.

If the positive existential sentence exists x eta(x) is committed, choose a constant c absent from the entire current Delta and that sentence. Any realization of Delta in M extends by choosing an actual witness for c. Thus adding eta(c) preserves the invariant. In particular a constant already mentioned in a numerical requirement cannot be reused as fresh.

At a closed nu_sigma-term u, first consistently decide N_sigma(u). If it is false, that term can never later become a number in the limit. If it is true, realize the current Delta in M. Standardness in M supplies an external standard n with u=z_n at that realization. Consequently E_(Delta+u=z_n) belongs to Gamma for some n, and the sequential Gamma-search terminates. The equality is permanently added to Delta. This does not need an effective map from M's elements to standard integers.

Fair computable interleaving of sentence decisions, existential witness obligations and all closed nu_sigma terms gives a complete consistent witness theory D. Every true N-number in the term model is represented by a closed term that received the numeral requirement and therefore equals a standard numeral. Conversely every numeral is a number; I_sigma gives their distinctness and the intended arithmetic. The algorithm remains total under the promise and may diverge without it.

D is Gamma-computable: simulate to the fixed decision stage of a queried sentence. Canonical least-term representatives, parameterized term substitution and actual truth are D-computable. Hence the output K satisfies K≤_TGamma. Its complete original theory is exactly Gamma, so evaluation of pure original sentences gives Gamma≤_TK. This proves equality of degrees without padding or a jump.

### Two precision points

- The exact construction uses **dynamically fresh witnesses**, as in the cited §5. It need not extend the separately preassigned Henkin theory U^H from the generic analytic-class argument. Overlaying predetermined witness axioms after deciding their constants would require a different consistency test; the present text does not do that.
- The phrase “makes every eventual numerical term a standard numeral” should be read as “makes every term satisfying N_sigma a standard numeral.” The full numerical sort nu_sigma also contains objects not satisfying N_sigma, and the algorithm explicitly permits those. This is a wording clarification, not a proof defect.

## 2. Hyperarithmetical-parameter elimination: PASS

If the fixed axiom enumeration is A-computable for hyperarithmetical A, the complete consistent Henkin decision codes with the displayed numeral condition form Pi^0_2(A). The standardness clause is forall-u exists-n with oracle-decidable matrix; the proof/axiom/consistency requirements are Pi^0_1(A).

A hyperarithmetical real A has a lightface Delta^1_1 singleton. Thus, for an arithmetic predicate R(D,Z) expressing the code requirements,

    D∈K iff exists Z (Z=A and R(D,Z))

is lightface analytic: take a lightface analytic definition of Z=A and combine its real witness with Z. This removes a **fixed** hyperarithmetical parameter for the basis theorem. It does not uniformly recognize hyperarithmetical indices, recover A from D, or justify removal of an arbitrary real parameter.

The nonemptiness proof uses the supplied standard model, not bare consistency. Its successive witness expansion gives a complete expanded theory satisfying every numeral requirement. The original term-model output requires no oracle beyond its decision code. Hence the generic standard-basis argument and the exact Gamma-preserving supplement have compatible, correctly separated roles.

## 3. Singular-cardinal support theorem: PASS with explicit ambient assumptions

The exact theorem is in ZFC, for an infinite cardinal kappa and a set A with |A|≥kappa, with G=Sym(A), W=A, E=N trivial, and all objects/functions whose supports have cardinality <kappa. These conditions must remain explicit.

For all infinite kappa, finite unions of <kappa supports are <kappa. Hence lambda closure, quantifier equivariance, singleton-point atoms, C5 and standard Frege arithmetic hold even for singular kappa. The proposition domain consists exactly of <kappa-small and cosmall subsets of A. No least-support principle is used.

For regular kappa, the generic-world IC proof makes <kappa many exceptional witness choices. Regularity ensures the union of their <kappa supports is still <kappa. This includes kappa=omega. The remaining worlds form a nonempty permutation orbit because |A|≥kappa and the excluded support has size <kappa.

For singular kappa, mu=cf(kappa)<kappa is infinite. A strictly increasing cofinal sequence of infinite cardinals kappa_i<kappa exists; kappa is then a limit cardinal in ZFC. Choose mu distinct s_i and let S={s_i}. The proposed F assigns p the worlds s_i for which |p|=kappa_i, and assigns empty the complement of S. Every value is small/cosmall, F is supported by S, and every world has a witness. It is irrelevant that the external cardinality rule need not be definable by a pure original term: the domain contains **all** supported functions.

If G is a selector with support T<kappa, its unique output q_i at s_i is fixed by Fix(T union {s_i}). Since |q_i|=kappa_i<kappa and all points outside T union {s_i} are interchangeable, q_i must be contained in T union {s_i}; the alternative contains a set of size |A|≥kappa. Choose i above the cardinal max(|T|,aleph_0); cofinality supplies kappa_i greater than that bound. Contradiction.

Thus the exact family classification `all-type Box IC iff IC_t iff kappa regular` survives the edge checks. Every uncountable kappa admits the countable shift witnessing DedInf_t, while kappa=omega retains the finite-fixed-proposition obstruction to Dedekind Infinity. The fresh-pair FC failure works in all cases since the complement of any <kappa support has at least two members. No claim is made for |A|<kappa, where the whole atom set itself becomes an allowed support and the model becomes full.
