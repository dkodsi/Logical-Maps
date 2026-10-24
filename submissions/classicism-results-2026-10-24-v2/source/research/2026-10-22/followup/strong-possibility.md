# Pure Strong Possibility: Boolean models and arithmetic constraints

22 October 2026. Original ordinary mathematical argument by OpenAI Codex; direct source: misc, this note. Not human checked or formalized. No claim of literature novelty. The frozen notes, C, the original relational types, and pure Max are unchanged. No signature Max, optional boxed axiom, or infinitary language is used.

## Exact target and result

The assignment is consistency or inconsistency of pure SP. The known equivalence with Max's existential-identity disjunction property and the essential-quotient/Henkin-truth gap are taken from `../notes/sp-algebraic-findings-20261022.md`, `sp-essential-extension-20261022.md`, and `sp-failed-disjunction-20261022.md`, §17.

**Current status:** pure SP consistency remains unresolved; no failed existential-identity disjunction has been obtained. The modified genuine Max construction retains Boolean elementarity and reaches targets splitting A_1, refuting Fin_e and refuting RC_(e,e), but still fails SP. Its full pure H-diagram is exactly the intersection of its distinguished roots' theories.

The next continuation is saved in [Strong Possibility: the one-way arithmetic frontier](strong-possibility-one-way.md). It strengthens the construction obstruction: genuine return maps force arithmetic isomorphism, so merely adding nonstandard roots cannot repair the retract construction. It also proves that unconstrained term profiles remain standard even with arbitrarily many fresh parameters, and reformulates the immediate consistency target as a one-way full-term embedding between Max models disagreeing on G. A quotient can remove the unwanted H(G) witnesses algebraically; preserving that condition through a genuine Henkin completion remains unproved. These are self-checked deductions, not an independently checked resolution.

The additional hour yields a sharper arithmetic boundary: the standard-root policy forces H(G) for a specific true Pi^0_2 arithmetic sentence G independent of Max, whereas SP proves G and not H(G). More generally SP admits the one-step C+I omega-rule proved below and therefore contains true Pi^0_2 arithmetic; if consistent, it nevertheless permits a false Sigma^0_3 arithmetic sentence. The note also extends Boolean elementarity to several fixed evaluations, proves a disjunction theorem for guarded numerical and Boolean witnesses, and checks that actual numerical elements survive B-preserving quotients. These are ordinary mathematical deductions with the stated source and syntax limitations, not a completed SP construction. Earlier stages are retained below with their separate scopes.

Let R be the genuine singleton pure-profile Max model from the saved construction. Its proposition Boolean algebra is A=2×B, where B is the algebra of pure one-individual proposition terms. If u:B→2 is R's truth on those terms, their inclusion is j(b)=(u(b),b); actual truth on A is its first coordinate. The saved `sp-henkin-minimal-20261022.md`, §6.1, proves that u contains no atom of B.

**Theorem.** Every finite existential Boolean identity diagram over j(B) realized in A can be realized in j(B) while also preserving the actual truth of every Boolean polynomial in its witnesses and coefficients. Consequently B with its inherited truth satisfies the Henkin clause for one block of proposition quantifiers whose matrix is any Boolean combination of:

- Boolean proposition polynomials beta(p,c), used as formulas;
- identities beta(p,c)=gamma(p,c);
- formulas box beta(p,c) and diamond beta(p,c).

Here c is a finite tuple from B. Coefficient terms may themselves contain arbitrary operations, but no quantified witness may occur inside them. In the last item beta is Boolean: nested witness-dependent modalities and identities comparing modal VALUES are not admitted. All coefficients and extracted witnesses are pure terms in the one original individual parameter.

## Proof of truth-preserving absorption

We prove an abstract Boolean-algebra lemma. Equip B with the unary predicate u and 2×B with the first-coordinate truth predicate. Then j is an existential embedding for quantifier-free formulas in the language of Boolean algebras, equality, and that unary truth predicate, provided u contains no atom.

Fix coefficients c_1,...,c_l and witnesses (epsilon_i,b_i), i=1,...,k, in A. The coefficients partition 1 into their nonzero Boolean cells c_s. Exactly one such cell c_* belongs to u. The b_i partition each c_s into cells

    d_(s,t) = c_s ∧ conjunction_i b_i^(t_i).

The corresponding A-cell has a nonzero first coordinate exactly when s=* and t=epsilon. Thus its required zero/nonzero pattern agrees with d_(s,t), except that the (*,epsilon) cell is necessarily nonzero even if its B-coordinate is zero.

For s!=*, retain the existing partition. Below c_* let m be the number of patterns required to be nonzero. Partition c_* into m nonzero pieces, with the epsilon-labelled piece in u and all the others outside u. Such a partition exists: repeatedly split the piece in u into two nonzero pieces, retaining its unique u-member for the next split. That piece is never an atom, by hypothesis. After m−1 steps there are exactly the required pieces. Assign zero to patterns not required to be nonzero.

Let b_i' be the union of the new cells whose ith pattern bit is 1. Every coefficient-and-variable cell has exactly the same zero/nonzero status as in A. Hence every Boolean polynomial equality, and its negation, has the same truth value: equality is vanishing of a symmetric difference, a union of these cells. Also u(b_i')=epsilon_i. Boolean homomorphism then gives the same actual truth for EVERY Boolean polynomial in the variables and coefficients. All atomic tests in the stated language, hence every finite Boolean combination of them, are preserved. The converse direction follows from the embedding j. This proves the lemma.

This adds a designated true cell to the saved Boolean absorption proof (§6.2); that proof preserved entity equalities and disequalities but did not require preserving witness truth.

## Modal and Henkin consequences, with their exact scope

In a genuine C model, the actual truth of box beta is exactly beta=top, and that of diamond beta is beta!=bottom. These are Boolean-algebra equality tests. Thus the lemma applies to the displayed one-modal-layer matrix fragment. For example it preserves a true partition witness satisfying

    p∨q=c,  p∧q=bottom,  p!=bottom,  q!=bottom,  and p.

Preserving the last conjunct together with all the entity equations is the additional content. Equivalently, order/zero conditions can be written using box of Boolean implications and negated diamond of Boolean intersections.

Let E(c)=exists pbar phi(pbar,c) be a proposition in B from this fragment. Since R is a genuine model, u(E)=1 gives witnesses in A; absorption supplies witnesses in B with u(phi)=1. Conversely any such B-witness is a witness in R. Therefore

    u(E(c))=1 iff some bbar in B has u(phi(bbar,c))=1.

Boolean duality supplies the corresponding one-block universal clause.

The extracted witnesses are permanent under any later full-term algebra embedding of B into a C-equational algebra Q, equipped with an identity-correct Boolean truth extending u. Their entire matrix propositions lie in B and retain their truth. Moreover the C existential-introduction inequalities phi(qbar,c)≤E(c) hold in Q; so if E is false, no new Q-witness can become true. The same reasoning, dually, establishes the universal clause. Thus these particular one-block quantifier clauses remain correct on Q, not merely on its old B-part. No Henkin clauses for other formulas in Q are assumed in this argument.

## Boundary of the first truth choice

The known boundary example H(E_1) contains r=diamond r, an identity comparing a modal VALUE with its input. It lies outside this fragment; the present proof does not extend to it. Alternating quantifiers, arbitrary higher-type observations, and coefficients newly introduced outside B also remain outside the theorem.

More decisively, the inherited u here comes from the isolated profile root, where Actuality is true. B has no actually true atom, so its inherited truth already fails the Henkin clause for that existential-universal statement. The saved essentiality argument shows that a genuine essential Max model would refute Actuality. Accordingly this particular truth choice cannot complete the full essential-model route. The next section replaces it; no general recursive completion theorem is obtained.

This completed the first bounded pass. The renewed pass below changes the truth choice instead of retaining that obstruction.

## Renewed attempt: all finite Boolean quantifier alternations

Write u_iso for the preceding isolated-root truth and v for the new truth below; they are not interchangeable.

**Atomless-support lemma.** Put I=I_e=diamond I*_e, with I* and its Fregean arithmetic defined in `topics/classicism/background.md`, lines 74–134 (paths starting with `topics/` are bundle-relative). In the common pure a-term Boolean algebra B, the interval B|I is atomless. Moreover I belongs to the truth ultrafilter induced by every genuine Max model.

For the second assertion, I* is C-consistent, as witnessed by the full Henkin infinite-base model, so I itself is a pure Max instance. For the first, suppose 0<b≤I were a B-atom, represented by T(a). Then C(a)+T(a) is consistent: otherwise C(a) proves T=bottom. For every pure a-formula F, atomhood gives b∧[F]=b or b∧[F]=0, so that theory proves F or its negation. It is thus a consistent complete recursively enumerable theory containing I. Its translated arithmetical consequences would be a complete consistent r.e. extension of PA, contradicting Gödel–Rosser. This uses the recorded arithmetic interpretation, `topics/classicism/results/possibility-and-necessity-of-arithmetic-incompatible.yaml`, proof, citing Goodsell, *Arithmetic is Necessary*, draft 5 June 2024, §6, Theorem 11 and note 14, pp. 24–26. The parameter a causes no issue: the translation of arithmetic is pure and the enlarged theory is still r.e. This is the parameter version of the frozen profile-root note's §18 argument. No new inspection of the source PDF is claimed.

**Abstract elementary-embedding lemma.** Let B be a Boolean algebra with ultrafilter v. Let K be a nonzero atomless Boolean algebra with ultrafilter w. Give K×B the truth predicate (k,b)↦w(k), and put

    j(b)=(v(b)·1_K,b).

Then j is elementary in the first-order language of Boolean algebras with a unary truth predicate if and only if v contains an element e whose interval B|e is atomless.

Necessity is direct. In K×B, (1_K,0) is a true element with an atomless interval. This is first-order expressible by

    exists e [ Truth(e) and
      forall x (0<x≤e -> exists y (0<y<x)) ].

Elementarity transfers the assertion to B.

For sufficiency fix such an e. Decompose B as (B|e)×(B|not e). The second factor carries no true elements and j is its identity. The first factor and K×(B|e) are both atomless Boolean algebras with a designated ultrafilter, and j restricts to a truth-preserving embedding between them.

Here every such embedding is elementary, by the following finite-partition argument. A finite tuple generates a finite Boolean subalgebra. Its nonzero cells, and the unique cell in the ultrafilter, completely determine its quantifier-free type. Adjoining one element splits each cell into up to two nonzero pieces. In an atomless algebra either one-piece or two-piece pattern can be reproduced. On the designated true cell, exactly one nonzero piece is true, and the labels of a proper split can be exchanged to reproduce that choice. The pieces on other cells are false. Hence a finite partial isomorphism preserving the truth predicate extends across any single additional element, in either direction. Repeating this for any prescribed finite number of rounds proves agreement on every finite first-order formula, with any finite tuple of old parameters. For the full products, carry the B|not e coordinate of each selected element across unchanged, and apply the same finite-partition argument to its first coordinate. This preserves equality, Boolean operations and truth, and proves the asserted elementarity of j. QED.

**Application to a genuine Max root.** Use the supported singleton root of `../notes/sp-henkin-minimal-20261022.md`, §13, retaining its complete C-component family and pure one-individual profiles. Let M be its bookkeeping substitution monoid. Its proposition algebra is exactly

    A_sup=K×B,

where K consists of all {0,1}-valued functions on M depending on only finitely many marker images. Actual truth is evaluation of the K-coordinate at the identity substitution. K is atomless: for a nonzero function k choose a substitution where k=1 and a marker outside its finite support; sending that fresh marker to 0_* and to 1_* preserves k and gives a proper split using the corresponding D_i. This is the proposition case of the saved fresh-splitter proof.

Every pure a-term has a constant root coordinate, because every root endomorphism fixes a. Thus the old-term inclusion is exactly j(b)=(v(b)·1_K,b), where v is this root's truth on B. The root is a genuine Max model, so v(I)=1. The atomless-support lemma and elementary-embedding lemma therefore apply.

**Conclusion.** There exists a truth ultrafilter v on the full pure a-term algebra B which is correct for literal identities at every type and satisfies the Henkin truth lemma for the entire first-order Boolean/truth fragment over B, with arbitrary finite quantifier alternation over proposition variables. Its coefficients may be arbitrary pure a-terms, but remain independent of every quantified variable of the fragment. This verifies a particular consistent truth choice on B; it is not a reduction showing that arbitrary SP candidates may be assumed to have this Boolean theory.

Precisely, Boolean TERMS are built from the proposition variables and those coefficients by 0,1,meet,join,complement. FORMULAS are generated from Truth(beta) and beta=gamma by logical connectives and proposition quantifiers. Truth(beta) translates to the C-formula beta. Modal truth tests box beta and diamond beta translate to beta=1 and beta!=0. Identities comparing modality-valued or quantifier-valued terms, witness-dependent higher-type applications, and quantification at other types are outside the grammar. In particular the theorem permits arbitrarily nested quantification as logical FORMULAS, not arbitrary quantified expressions inside a Boolean TERM.

For any formula Phi and old parameter tuple, elementarity identifies its first-order truth in (B,v) with its truth in the genuine supported root. The latter is v([Phi]) because the pure a-term [Phi] belongs to B. This proves the stated Henkin clause, including nested existential and universal subformulas. Identity correctness at other types is inherited separately from the genuine Max root and the common term-algebra embedding; it does not assert their quantifier clauses.

For example, v correctly makes every nonzero subproposition of I split, correctly refutes a true Boolean atom, and correctly refutes Actuality. Thus quantifier ALTERNATION alone was not the essential obstruction in the first attempt. This new v replaces u_iso; it does not repair u_iso.

## Boundary of the renewed result

The supported root still satisfies H(E_1), witnessed by its nonzero root indicator r=(1_K,0), with r=diamond r and r≤E_1. This witness is absent from j(B). In fact no B-witness can satisfy that identity diagram: such a witness would be represented by a pure a-term, its positive identities would be C(a)-theorems, and its nonzero status would hold at every Max point. The same diagram would then hold in every Max model, contradicting the mixed retract Max model with not H(E_1) in `../notes/sp-failed-disjunction-20261022.md`, §§8–9. Hence this v still fails a Henkin clause with just one existential proposition quantifier once a modal VALUE is admitted.

The renewed result is therefore full finite Boolean/truth elementarity for a suitable genuine-Max truth choice, not full term-model generation or SP consistency. It removes the earlier Actuality and Boolean-alternation obstruction in that fragment while leaving a precise modal-value obstruction. Nor does elementarity automatically survive an arbitrary later full-term extension or essential quotient; the earlier permanent-witness argument concerned a one-block fragment and does not supply that stronger claim.

## Preserving the Boolean result while repairing H(E_1)

The preceding obstruction can be moved without sacrificing Boolean elementarity. The following countable-root construction handles every finite individual cardinality simultaneously. It remains entirely in the original pure language.

First generalize the sufficient half of the elementary-embedding lemma. Let h:B→K be any Boolean homomorphism and give K×B truth w on its first coordinate. If e has an atomless B-interval and h(e)=1_K, then

    b |-> (h(b),b)

is elementary for Boolean operations, equality and truth, with old truth v=w h. Indeed split at e as before. On B|not e, h is zero and the map is the identity into the corresponding factor. On B|e it is a truth-preserving embedding between atomless Boolean algebras. The same finite-partition proof applies; h need not have two-element image.

**Construction.** For each positive external integer n take a root o_n with individual set E_n={a_1^n,...,a_n^n} and a countably infinite set D_n of bookkeeping markers. A root arrow o_m→o_n consists of any map E_m→E_n and any substitution D_m→D_n∪{0_*,1_*}. Compose both parts by substitution, fixing the two tokens. These tokens are bookkeeping, not the logical propositions top and bottom.

Attach a C-complete family of component models. For every component object V and assignment s:E_n→D_e(V), include an exit o_n→V. Compose exits using their individual assignments; an exit forgets the bookkeeping substitution entirely. Component-to-component composition uses the original transports. The root and exit compositions are associative.

At a relational type sigma=tau_1...tau_k t, a root-o_n entity consists of a pure term profile T(a_1^n,...,a_n^n), interpreted at all its component exits, together with an extension R_f at every root arrow f:o_n→o_j. Require a finite support S⊂D_n such that root arrows to the same target, with the same individual map and agreeing on S, give equal R_f. Identify profiles that agree at all component exits. Component domains are unchanged. This is an induction on type: all argument domains used by R_f have already been defined.

Here are the closure checks, rather than an assumption that term-generated domains are automatically Henkin:

1. A root-arrow tail has the profile obtained by the corresponding individual substitution. Its support consists of the target markers occurring in the images of S; token images need no support. Thus it lands in the stated target domain. A component tail lands by the profile definition.
2. Two arrows agreeing on the indicated data give equal complete transported entities. After another root arrow their composites still agree on the original support and on the individual map. After a component exit the bookkeeping is forgotten and the individual substitutions agree. This verifies equality of full tails, not just current extensions.
3. A term in finitely many parameters has the substituted pure individual profile and the union of their finite bookkeeping supports. Arrows agreeing on that data give equal parameter entities in the same target domain; consequently every formula has the same truth there, including identity and quantified formulas. Lambda abstraction has the required extension family. The domains of bound variables are the full stated target domains, not their term-generated subsets.
4. These evaluation clauses validate H. H-equivalent abstractions agree at every extension coordinate, so they are identical entities. Logical Equivalence therefore holds with its theoremhood restriction, and the construction is a genuine C-model.

Every new root satisfies pure Max: any C-consistent pure sentence is true at a component object, and any assignment of its nonempty individual domain to the finitely many source markers supplies the required exit. This uses no signature Max for the bookkeeping devices.

**Boolean elementarity at o_1.** Its proposition algebra is K_1×B, where K_1 is the algebra of finite-supported root-coordinate truth functions. It is atomless. Given a nonzero function, choose an arrow where it is 1 and a bookkeeping marker outside its support; changing that marker's image to 0_* and 1_* leaves the function true and supplies its proper split. Pure terms embed by b↦(h(b),b), where h is their root-coordinate family. Since every root target satisfies Max, h(I_e)=1. The atomless-support lemma gives atomlessness of B|I_e. The generalized embedding lemma therefore proves full finite Boolean/truth elementarity at o_1. In particular its inherited old-term truth satisfies all the Boolean Henkin clauses proved above and refutes Actuality. Recall that I_e=diamond I*_e is the arithmetic-support formula; it is not the axiom that the ACTUAL individual domain is infinite.

**Distinctness-preserving access.** For each n choose h_n:o_1→o_n sending the sole individual to a_1^n and sending the bookkeeping markers bijectively to D_n. Choose j_n:o_n→o_1 collapsing all individuals to the sole one and using the inverse bookkeeping bijection. Then j_n h_n=id_(o_1). If q is true at o_1, its h_n-tail is possible at o_n, witnessed by j_n. Thus, for every pure P true at o_n,

    at o_1: forall q [q -> diamond(P and diamond q)],

which is D(P). In particular D(E_n) holds for every standard n, where E_n now denotes the SENTENCE saying exactly n individuals exist. Hence both H(E_1) and H(not E_1) are false at o_1. The new truth choice repairs the former one-modal-value counterexample while retaining arbitrary finite Boolean quantifier alternation. The proof uses an actual single countable-root model, not a compactness inference that might lose term-witness clauses.

**The remaining explicit failure.** Let Fin_e be

    exists Z [FiniteCardinality_e(Z) and Z(lambda x^e.top)].

Every o_n satisfies Fin_e, witnessed by its standard nth cardinality numeral. The root indicator r, true at all root-arrow coordinates and with zero component profile, is admitted with empty support. Its every root tail is nonzero and its every component tail is zero; hence r=diamond r. Also r≤Fin_e and r is actually true. Consequently H(Fin_e) holds at o_1.

Max+not Fin_e is consistent. For completeness, use the archived arbitrary-individual-set profile root (`../notes/profile-root-construction-20261022.md`, §10) with an infinite root individual set. Its arbitrary actual higher-type extensions supply the property whose extension is exactly the external standard numeral denotations. This property is zero-containing and successor-closed, so the impredicative definition of FiniteCardinality admits only those numerals; finite induction admits them all. No standard finite cardinality holds of the infinite universal individual property. That genuine Max root therefore satisfies not Fin_e.

SP would require D(not Fin_e), contradicting H(Fin_e). Thus the new model is explicitly not an SP model. Handling every finite cardinality separately, even together with the full Boolean/truth fragment, has not handled this single quantified finiteness assertion.

There is also an obstruction that adding infinite individual roots would not repair. Let A_1 be the conjunction of the Fregean Axiom and exactly one individual. At every new root, A_1 is false because Max supplies infinitely many distinct propositions. At an A_1-component, all individual parameters have the sole individual value and the full finite extensional structure is unique. Every pure individual-parameter profile is therefore constant on these components. For any root proposition p, the component profile of p∧A_1 is either zero or A_1, and its root coordinates are zero. Hence A_1 is a nonzero Boolean atom at every new root. The root indicator consequently witnesses H(Atom(A_1)). But Max+not Atom(A_1) is consistent, witnessed by the atomless Max target in `../notes/sp-failed-disjunction-20261022.md`, §9.3. This argument uses only individual-parameter profiles, so allowing additional infinite individual sets would leave it intact. A successful extension must change the profile or root-domain policy, not just enumerate more individual cardinalities.

## Relational-type extension of the Boolean argument

The same countable-root model supports a larger, precisely restricted conclusion. Fix any relational type sigma=tau_1...tau_k t and any ONE tuple c_1,...,c_k of pure a-terms of its argument types. Let B_sigma be its pure a-term Boolean algebra, and use the unary truth predicate

    Truth_c(X) iff X(c_1,...,c_k) is actually true at o_1.

Then B_sigma is elementary in the actual sigma-domain for Boolean operations, literal equality and this single evaluation predicate. Thus arbitrary finite quantifier alternation over sigma also has the correct old-term Henkin truth clause in this language. The case sigma=t has the empty argument tuple and is the previous theorem. The conclusion does not permit the evaluation arguments to vary with the quantified witnesses.

Here are the extra checks. Write i_sigma=lambda z_1...z_k.I_e. Its interval in B_sigma is atomless. Otherwise let X be a nonzero atom below i_sigma and introduce fresh argument parameters z_1,...,z_k. The theory C(a,zbar)+X(zbar) is consistent, since inconsistency would make X identically bottom. For every pure formula F(a,zbar), use the relation lambda zbar.F as a Boolean part of X. Atomhood makes X∧(lambda zbar.F) either X or bottom, so the displayed theory decides F. It is a complete consistent r.e. theory containing I_e, again contradicting the recorded PA interpretation and Gödel–Rosser. This argument works also when the argument types are relational; finitely many typed parameters do not change recursive enumerability.

The actual sigma-domain at o_1 is K_sigma×B_sigma, with K_sigma its supported root-extension families. K_sigma is atomless: a nonzero family has an arrow and an argument tuple in its extension; a fresh bookkeeping marker leaves that extension fixed and its lifted splitter separates two such coordinates. Evaluation of the K_sigma-coordinate at the identity arrow and the fixed actual tuple cbar is an ultrafilter w_c. Pure terms embed as (h_sigma(X),X), and h_sigma(i_sigma)=1 because I_e is true at every root target. The generalized elementary-embedding lemma now applies verbatim, with truth v_c=w_c h_sigma.

Coefficients may again be arbitrary old pure a-terms of sigma. Mixed sorts, several independent evaluation predicates on the same sort, variable argument positions, composition between quantified relations, and identities comparing quantified or modal term VALUES have not been proved covered here. In particular this is a family of single-sort Boolean/evaluation fragments, not full higher-order Henkin closure.

## Exact modal threshold and final status

For a closed pure P, consider the one-template algebraic existence assertion in B:

    E_P := exists r [r!=0 and r=diamond r and r∧P=r].

It holds in B exactly when Max proves P. In the forward direction, a term witness T(a) has its positive identities proved by C(a). The one-individual Max lemma gives Max⊢forall a T(a)!=0 (equivalently, use the common term-algebra embedding). Those identities then prove H(P), and hence P. In the reverse direction, take the finite conjunction K of pure Max axioms used in a proof of P (K=top if none are used). Each axiom is a pure disequality, and C proves its identity with its own diamond; finite meets preserve that property. Deduction gives C⊢K≤P. Consistency of Max gives K!=0 in B. Hence K is the required B-witness. This uses the finite-Max-axiom argument already saved in `../notes/sp-failed-disjunction-20261022.md`, §17, rather than necessitating a Max premise.

Accordingly, for a truth v inherited from a genuine Max model, correct Henkin clauses just for ALL these E_P already say

    H(P) is true iff Max proves P.

The negative instances are precisely D(not P) whenever Max+not P is consistent, namely the SP scheme under renaming. Conversely SP gives these clauses. Thus extending the present theorem to that one fixed existential modal-value template with arbitrary closed pure coefficients would already settle SP consistency; it is not a routine additional quantifier-elimination step.

**Final outcome of the renewed bounded attempt:** a genuine Max model with Boolean/truth elementarity of its pure one-individual term algebra, its stated relational-type extension at one fixed old argument tuple, no Actuality, and D(E_n) for every standard finite n; explicit failures at D(not Fin_e) and D(not Atom(A_1)); and the exact single-template modal threshold. Pure SP consistency remains unresolved. No failed Max existential-identity disjunction or general essential-quotient/Henkin completion theorem has been obtained. No language extension, database record, generated map, or Lean file was changed.

## Second continuation: audit and a changed profile policy

22 October 2026. This continuation keeps the original finitary C and pure Max, and introduces no object-language constants or infinitary connectives. It changes the semantic profile/domain policy and the inherited truth v, not the algebra B. The previous constructions and their stated failures remain as separate examples.

### Audit of the two inputs

The arithmetic input needed above is the effective first-order interpretation of PA in C+I_e, with quantification restricted to N_e and the recorded zero, successor, Sum and Prod. A complete consistent r.e. extension of C with finitely many typed parameters and with I_e would induce a complete consistent r.e. theory in the ordinary arithmetic language: enumerate its proofs of translated arithmetic sentences. The translation preserves Boolean connectives, the PA axioms are supplied by the interpretation, and completeness decides each translated arithmetic sentence. Gödel–Rosser therefore applies. No external standardness, omega-consistency, Choice, or Countable Boolean Completeness enters this argument. In particular adding finitely many typed parameters in the relational-atom argument changes neither effectivity nor the pure arithmetic translation.

This premise is explicitly recorded in `topics/classicism/results/possibility-and-necessity-of-arithmetic-incompatible.yaml`, proof and source note, citing Goodsell's Lemma 1 and Theorem 11 for r.e. extensions of HK consistent with I. The separate CBC write-up's introductory phrase saying that C extends HKC must NOT be used to import Countable Boolean Completeness into C; that would be an invalid strengthening. The relevant recorded steps are the PA interpretation and I→I*, not the later CBC step. Fresh access to the [author's archived manuscript](https://philarchive.org/archive/GOOAIN) again returned 403; the full source premise has not been independently re-read. The atomless-support lemma remains an argument from the explicitly recorded PA-interpretation input, with that source-access limitation retained. No published or database proof was edited.

For the nonconstant-h embedding, write B=(B|e)×(B|not e). The hypothesis h(e)=1 forces h(b)=h(b∧e), hence the map is exactly

    (x,y) |-> ((h(x),x),y)

into (K×(B|e))×(B|not e). On the first factors it is an embedding of atomless Boolean algebras preserving the designated ultrafilter. In the finite-partition back-and-forth proof, include e among the initial parameters, reproduce every selected first-coordinate split, and copy its second coordinate y unchanged. This preserves the full finite product subalgebra and truth at each round, including when B|not e is degenerate. It proves elementarity for arbitrary h under the stated hypothesis, without requiring h(B)⊆{0,1} or any atomlessness outside e.

The syntax audit also passes with its narrow scope. Quantified formulas remain FORMULAS of the first-order Boolean/evaluation language. Only Boolean polynomials are TERMS in its equality atoms. After all free witnesses have been replaced by old terms, the resulting whole C-formula has an old proposition value whose truth is read by v. That final observation does not license putting a witness-dependent quantified formula or modal value inside a Boolean term. The modification below uses exactly this grammar.

### Construction: a symmetric target with live relational profiles

Retain all the finite roots o_n of the preceding construction. Add one root o_* with individual set

    E={i_j:j∈N} disjoint-union {a_j^0,a_j^1:j∈N}.

The external group G=product_(j∈N) C_2 swaps the two a_j's independently and fixes i_j. It fixes every individual at every finite root. At o_* introduce countably many LIVE propositional profile parameters d_j. Unlike the earlier bookkeeping markers, these are assigned arbitrary propositions at component exits. Every root also has its own countably infinite set of ERASED bookkeeping markers b_j, with tokens 0_*,1_* as before. G fixes both kinds of propositional markers and both tokens. All are semantic devices, removed in the pure reduct.

The individual maps of root arrows are: every map between finite roots; every map from a finite root into E; constant maps from E to a finite root; and the G-permutations or constant maps E→E. They are closed under composition. An arrow from o_* substitutes each d_j by a target d_k or logical top/bottom when the target is o_*, and by logical top/bottom at a finite target. Other source roots have no d-parameters. Independently, every arrow substitutes its source b-markers by target b-markers or the ERASED tokens 0_*,1_*. Compose all substitutions normally. Logical top/bottom in a d-substitution are distinct from the erased bookkeeping tokens.

Component exits use all assignments of the source individuals and live d-parameters to the corresponding component domains; they erase the b-markers. Take the same complete family of C-components. G acts on exits by reindexing their E-assignments and fixes the component entities. Its conjugation action on root arrows fixes each permutation E→E because G is abelian. Constant maps and finite-to-E maps have support contained in their finitely many selected E-values; all other individual maps are fixed. Thus EVERY root arrow has finite external support, including arrows with infinitely many d- or b-substitutions.

At finite roots use pure individual-parameter component profiles. At o_* use profiles with finitely many E-parameters and live d-parameters. At every root, require BOTH finite external G-support and finite substitution support for the extension family. The latter is a finite set of source individual, d- and b-markers, containing the free parameters of a profile presentation; arrows to the same target agreeing there must give the same extension coordinate. As previously, domains are defined by induction on argument types, profiles are identified by their component families, and supports are properties rather than extra coordinates.

The closure argument is the combined-support argument of the frozen `../notes/sp-failed-disjunction-20261022.md`, §14, with erased bookkeeping support now imposed also at the finite sources:

- Root transport takes a substitution support to the finitely many nonconstant marker images. A d-substitution into a finite root leaves a pure individual profile. Erased tokens contribute no target support. External support is contained in the union of supports of the entity and arrow, by transport equivariance.
- Agreement on a substitution support gives equality of COMPLETE transported entities after every further root or component arrow. Component profiles agree because the support includes their free parameters; erased markers disappear there.
- The domains are G-invariant and G acts bijectively. Application, literal identity and quantification are equivariant. A lambda term in finitely many parameters therefore has finite external support and the union of their substitution supports. Its component profile is the ordinary substituted term. This proves closure even for quantified and identity-containing terms.

Consequently H and Logical Equivalence hold by the same extension-coordinate verification: this is a genuine C-model. Complete exits make every root a pure Max point. This is not an assumption that arbitrary support-restricted domains preserve Henkin quantification.

### Boolean preservation at the source

At o_1 every old pure a-profile is G-fixed. Thus, at each relational type sigma, the source domain is exactly

    K_sigma × B_sigma,

where K_sigma is the algebra of root-extension families satisfying the two support conditions. The conditions on these families are independent of the old profile: every pure a-profile already has empty external support and no live d-parameters.

K_sigma is atomless. For a nonzero family choose a root arrow and tuple witnessing nonemptiness, then a source b-marker outside its finite substitution support. Changing only its image to 0_* versus 1_* preserves that extension and tuple. The erased splitter, with zero component profile and truth determined by whether that image is 1_*, has empty external support. Its constant relational lift supplies the required two nonzero parts within K_sigma.

Pure terms embed by (h_sigma(X),X). Since every root target is Max, h_sigma(lambda zbar.I_e)=1. The audited atomless-support and nonconstant-h lemmas therefore give exactly the previous Boolean/truth elementarity at o_1, including the one-fixed-old-argument-tuple relational variant. This is a NEW inherited truth assignment v; arbitrary old quantified sentences need not retain their truth from the earlier model. Source Actuality is false. The source still makes A_1 an atom, either by its pure profile argument or by Boolean elementarity.

### The previously blocked possibilities now coexist

At o_*, each live d_j has an admitted splitter D_j with profile d_j, root truth true exactly when its image is logical top, and empty external support. Given a nonzero relation X, choose d_j outside its finite substitution support. At a witnessing root arrow, vary just that d-image between logical top and bottom; at a witnessing component exit, vary just its assigned proposition. X and the witnessing tuple stay fixed, while D_j changes truth. Therefore EVERY relational Boolean algebra at o_* is atomless. In particular A_1 is split there. Live relational profiles, rather than additional individual markers, perform the missing split.

The same target refutes RC_(e,e). Use the invariant serial relation U with pairs U(i_j,a_j^0), U(i_j,a_j^1), and U(a_j^epsilon,a_j^epsilon). Give it this extension at root arrows landing at o_*, empty extensions at finite targets, and zero component profile. It has empty supports. Any admitted functional serial subrelation has finite external support; swapping a fresh pair preserves it while fixing i_j, contradicting its selection of exactly one member. The erased-marker enrichment does not admit a selector without finite external support.

The target also satisfies not Fin_e, with the quantified Fregean definition of Fin_e already used above. To check this rather than infer it from external infinitude, admit W:nu_e t with zero component profile and, at each root target v, extension exactly the standard numeral denotations in D_nu_e(v). This family depends only on the target object, so has empty substitution support. Pure numerals are fixed by G, so its external support is empty too. W contains zero and is successor-closed at every new root; the defining induction clause forces its N_e-extension to consist exactly of standard numerals. Max makes these numerals distinct. At o_* none of their finite cardinalities holds of the infinite universal individual property. This proves not Fin_e. W is a permitted semantic entity, not an infinitary formula, and its zero component tails impose no standardness on the original C-components.

For each finite o_n there is a return pair h_n:o_1→o_n, j_n:o_n→o_1 with j_n h_n=id, using inverse bijections of erased markers. There is also such a pair through o_*: send a to any b∈E, collapse all E back to a, send the d_j to logical bottom on return, and use inverse erased-marker bijections. Hence every actual target truth P has D(P) at o_1, by the existing return-arrow proof applied to EVERY source truth q. The source consequently retains all D(E_n) and now also satisfies

    D(not Fin_e and Atomlessness_t and not RC_(e,e)).

Any finite list of relational-type atomlessness instances can be added to this same conjunction. In particular H(Atom(A_1)), H(Fin_e), and H(RC_(e,e)) are all false at the source. Their opposites also have false H, since the source itself satisfies Atom(A_1), Fin_e and RC_(e,e). Thus the modification repairs these particular modal-value/Henkin counterexamples while keeping the established Boolean clauses. It does not merely increase the list of finite individual cardinalities.

### A surviving concrete obstruction and stop decision

This construction is still not SP. Put P=Fin_e or Atomlessness_t. Every finite new root satisfies its first disjunct, and o_* satisfies its second. The erased root indicator r has r!=0, r=diamond r and r≤P, so H(P) holds at o_1.

But Max+not P is consistent: the ordinary infinite-individual pure-profile root from `../notes/profile-root-construction-20261022.md`, §10, has not Fin_e by the checked standard-numeral argument, and has the nonzero atom A_1 because its profiles contain only individual parameters. Thus it refutes Atomlessness_t. SP would require D(not P), which the new source fails. Equivalently its inherited v still gives the internal E_P value true although the old term algebra has no E_P witness. This is a specific remaining modal-value failure, not an assertion that the genuine ambient model lacks Henkin witnesses.

The concrete modification survives: live relational profiles plus external symmetry can split A_1, supply quantified Infinity and Choice failure at a return target, and retain Boolean/truth elementarity at the source. The general obstruction has nevertheless returned as a pure assertion shared by all selected roots. Adding another specially chosen target for this disjunction would not itself supply a completion theorem. I stop here rather than count further target additions as a solution. Full modal-value witness preservation, unrestricted higher-type/application Henkin clauses on B, and pure SP consistency remain unresolved. No new language, database record, generated output, or Lean proof was introduced.

## Third continuation: an arithmetic obstruction to the whole root policy

22 October 2026. The subsequently authorized additional hour supersedes the preceding stop decision. The following arguments are new deductions in this note, not database verdicts or claims of literature novelty.

### An effectively specified arithmetic sentence independent of Max

There is a true first-order arithmetic sentence G, which may be taken Pi^0_2, such that neither G's pure Frege-arithmetic translation G# nor its negation is provable in Max. This uses two already available inputs: Max has a standard-arithmetic model, and its theoremhood is Sigma^0_2. The frozen `../notes/max-degree.md`, §§3, 7 and 10.1–10.2, supplies these inputs independently of SP. Here is the diagonal argument, including why ordinary effective incompleteness must not be applied directly to the non-r.e. theory Max.

Fix a recursive coding of the original syntax and of the arithmetic translation A↦A#. A certificate for a Max proof records the finitely many C-enumeration witnesses and ordinary deduction steps, together with finitely many eligible disequality axioms whose corresponding identities have no C-proof. Its correctness is therefore Pi^0_1. Thus an arithmetic formula Pr_Max(z) of complexity Sigma^0_2 expresses actual Max theoremhood on standard sentence codes. The ordinary diagonal lemma, applied to the arithmetic formula not Pr_Max(code(A#)), gives G with

    PA proves G iff not Pr_Max(code(G#)).

The standard coding substitutions preserve the Pi^0_2 complexity of the right-hand side. This specifies a finite original-language arithmetic sentence by an effective fixed-point construction; it introduces neither an object-language truth predicate nor an extra axiom for Max.

If Max proved G#, its standard-arithmetic model would make G true. The standard fixed-point equivalence would then say that this very proof does not exist, a contradiction. Therefore Max does not prove G#, and the same equivalence makes G true in the standard natural numbers. Standard-arithmetic soundness also rules out a Max proof of not G#. Consequently both Max+G# and Max+not G# are consistent. The existence of the standard Max model is essential here; mere consistency of a Sigma^0_2 theory would not justify this soundness argument.

Pure SP therefore implies BOTH D(G#) and D(not G#), hence

    not H(G#) and not H(not G#).

This is one precise arithmetic coefficient at which full modal-value Henkin preservation must differ from the construction above. It is not a proof that an SP model's ACTUAL number field must be nonstandard: a standard actual point could in principle have the required modal variation.

### Why changing only supports or the menu of roots cannot fix this

The supported roots above have externally standard N_e, not just externally infinite individual sets. The semantic W argument proves that N_e consists exactly of the distinct standard numeral denotations. Addition and multiplication are standard too: for a fixed standard m, admit the relation whose extension at each root target v is respectively

    {(k_v,(m+k)_v): k in omega},
    {(k_v,(m k)_v): k in omega},

with zero component profiles. These families have empty substitution support and empty external support, since their members are denotations of pure numerals. They are valid even at a root with finitely many individuals. In the definitions of Sum and Prod, finite induction supplies the correct instances; these admitted inductive relations exclude every incorrect standard instance. This is the proof of `max-degree.md` §10.2 adapted to the supported root coordinates, with no appeal to full external powersets at those coordinates.

More generally, suppose a profile construction has any family of distinguished roots such that (i) their arithmetic reducts are standard and (ii) the proposition r, true at every distinguished-root coordinate and zero in every component profile, is admitted and satisfies r=diamond r. Then every standard arithmetic truth A# satisfies r≤A#, so every distinguished root satisfies H(A#). In particular it satisfies H(G#), and therefore fails SP.

The construction is consequently immune to a repair consisting merely of more cardinalities, live-parameter contexts, or finite-support group variants while those two features persist. Finite support alone does not exclude the standard-number predicate or its arithmetic graph relations: all have empty support. A successful use of this strategy must change which semantic extension families are admitted, or remove the separating possibility-fixed root indicator, or provide roots whose arithmetic is not uniformly standard. Adding another standard root to repair Fin_e or Atomlessness_t does none of these.

External nonstandardness alone is insufficient: a nonstandard model of TRUE arithmetic still satisfies G. Elementary extensions or ultraproducts of the present standard-arithmetic roots keep G true. If the root indicator is retained, at least one new root must actually falsify G to remove this particular H(G) witness.

**Exact root-family diagnostic.** In the current construction, more generally, for every closed pure P,

    source satisfies H(P) iff every distinguished root satisfies P;
    source satisfies D(P) iff some distinguished root satisfies P.

The forward obstruction is exact: when every root has P, the admitted root indicator witnesses H(P). If a root has not P, its return pair gives D(not P) at the source, excluding H(P). Complementing yields the second equivalence. These statements concern closed PURE coefficients; they are not assertions about arbitrarily transported parameters. Consequently a construction with these two features would satisfy SP exactly when its root family realizes every Max-consistent pure sentence. A countable family would suffice in principle because the pure syntax is countable. No construction here allows arbitrary preassigned Max models to be inserted as roots while preserving their theories and the return maps, so this is an exact diagnostic, not a gluing or completion theorem.

There is also a useful consistent strengthening on the Max side. Let arithmetic H-settlement be the ORIGINAL-language schema

    H(A#) or H(not A#), for each closed first-order arithmetic sentence A.

Every standard-root construction just described satisfies it, choosing the standardly true side. Thus Max plus this entire schema is consistent, whereas SP plus it is inconsistent by the single instance G. This is an unboxed schema at the chosen root, not ordinary Necessity of Arithmetic and not an asserted boxed result. No new principle record is being introduced.

## Several fixed evaluations: a larger verified Boolean fragment

The earlier one-evaluation restriction can be relaxed without crossing the modal-value boundary. Fix a relational type sigma and ANY family of tuples cbar_i of old pure a-terms of its argument types. Expand its Boolean algebra language by predicates

    U_i(X) iff X[cbar_i] is actually true.

At the supported singleton source, B_sigma is elementary in the actual sigma-domain for this entire language, including arbitrary finite quantifier alternation. Each formula uses only finitely many predicates, so it suffices to prove the finite-family case.

The needed abstract fact is this: an embedding of atomless Boolean algebras with finitely many named ultrafilters is elementary if it preserves their predicates and their coincidence pattern. To verify it, take a finite Boolean partition. A new element splits each cell into two possibly empty pieces. Match which ultrafilters choose each piece. Distinct ultrafilters on the old algebra can be separated by Boolean elements, so any requested allocation of a finite family of distinct ultrafilters is possible. Coincident ultrafilters cannot be separated on either side. If a required nonzero piece receives no ultrafilter, atomlessness supplies a spare nonzero subpiece missed by every named ultrafilter: divide an appropriate nonzero cell into more pieces than there are ultrafilters. This reproduces both emptiness and all predicate memberships. Successive finite-partition extensions give quantifier elimination for each fixed coincidence pattern, and therefore elementarity. No saturation or countable intersection of filters is used.

Apply this to the same decomposition at e=i_sigma=lambda zbar.I_e. All U_i contain e, B_sigma|e is atomless, and h_sigma(e)=1. In the first factor, j is x↦(h_sigma(x),x), with ultrafilters w_i on K_sigma and v_i=w_i h_sigma on B_sigma|e. Their coincidence patterns agree. Indeed two evaluations at literally equal actual tuples agree everywhere. If the old tuples differ, the old pure relation lambda zbar.(zbar=cbar_i), intersected with e, is true at cbar_i and false at cbar_j. It separates v_i,v_j and hence also w_i,w_j. The second factor B_sigma|not e is copied unchanged, just as in the one-ultrafilter proof.

The same conclusion holds for a disjoint many-sorted combination of these languages, at any collection of relational types. In a finite back-and-forth argument, make the relevant move in its own sort. This permits quantifier alternation between different sorts when they interact only through the outer Boolean connectives and their named truth predicates. It does NOT introduce application maps between variable sorts.

Thus several fixed argument tuples and disjoint mixed-sort Boolean reasoning are now covered. Variable argument positions, identities between evaluated proposition VALUES, composition/application between quantified entities, and witness-dependent modal or quantified term values remain outside the theorem. In particular the arithmetic E_(G#) instance is still excluded; the extension is not a solution to SP.

## A one-step omega-rule consequence of pure SP

There is a stronger consequence of the standard-root comparison, independent of the Boolean embedding construction. Let P(n) be a fixed PURE original-language formula whose only free variable has number type nu_e. Suppose, externally, that for every standard k,

    C proves I_e -> P(numeral k).

The same premise may use any fixed finite tuple of numerical variables. No uniform proof bound and no object-language infinite conjunction are assumed. Form the single finitary universal identity sentence

    U_P := forall n [N_e(n)=top -> (I_e∧P(n))=I_e],

where the right-hand equality means the proposition identity (I_e∧P(n))=I_e. Then pure SP entails U_P and consequently

    forall n in N_e P(n), and forall n in N_e H(P(n)).

**Proof.** Use the genuine standard-arithmetic Max root from `max-degree.md` §10.1. At every current number n there, n is literally the denotation of some standard numeral k. The stipulated C-theorem at k equationalizes to (I_e∧P(k))=I_e; necessitation here applies to that whole C-theorem, not to a Max assumption. Thus this root satisfies U_P. U_P is a closed universal finite Boolean combination of identities between pure terms. P may contain quantifiers, but it is a TERM inside the displayed identity, which is allowed by the exact universal-identity reflection theorem. Accordingly Max+U_P is consistent, SP supplies D(U_P), and C's D(U_P)→U_P gives U_P. See `../notes/reflection-universal-core-20261022.md`, §§3–4, for that reflection theorem.

In C, numbers are necessarily numbers, so N_e(n) implies N_e(n)=top. This is the elementary induction proof in `topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md`, Lemma 3; it uses no Countable Boolean Completeness. Since SP entails Max and hence I_e, U_P implies P(n) for every actual number. Also I_e=diamond I_e by the S4 idempotence law, because I_e=diamond I*_e. Therefore the actually true q=I_e witnesses H(P(n)): the identity in U_P says exactly Box(I_e→P(n)). This proves the second conclusion too. QED.

This is a consequence rule for SP with C+I_e as its reference theory, not an identification of SP with an omega-rule closure. Its premise mentions separate standard finite proofs. It is not an effective inference rule, and iterating it with SP in place of C+I_e has not been justified.

**Uniform-reflection corollary.** Let T=C+I_e and fix any pure formula P(n) with numerical parameters. Use the ordinary arithmetized finite-proof certificate predicate Check_T(n,p) for a T-proof of P(numeral n). Then SP entails forall n,p∈N_e (Check_T(n,p)→P(n)). For each standard pair k,l, either l is such a proof, in which case T proves P(k), or the finite certificate check fails, in which case PA and hence T prove not Check_T(k,l). Thus T proves the displayed implication at every standard pair. The tuple version of the rule supplies its universal closure. This is a schema with a separately fixed P, not a truth predicate for all original formulas, and not reflection for SP itself. No claim that Max fails this reflection schema is needed.

### Pure SP contains true Pi^0_2 arithmetic

Let A be any true ordinary Pi^0_2 arithmetic sentence. In a standard prenex form write A=forall n P(n), with P Sigma^0_1; tuples can be coded by the ordinary PA pairing definitions. For each standard k, P(k) is a true Sigma^0_1 sentence and therefore has a finite PA proof. The recorded arithmetic interpretation translates that proof to C⊢I_e→P#(k). The preceding rule gives SP⊢A#. All uses of PA here refer to the effective interpretation already audited above.

It follows also that SP proves the standardly correct side of every closed Sigma^0_2/Pi^0_2 arithmetic sentence; if SP is consistent, it cannot prove the incorrect side as well. A false Sigma^0_2 sentence has a true Pi^0_2 negation. A true Sigma^0_2 sentence has a standard existential witness whose Pi^0_1 matrix is true, and true Pi^0_1 sentences are included in the preceding Pi^0_2 conclusion. No standardness assumption on a hypothetical SP model's actual number field is used. No claim about all arithmetic sentences is obtained.

In particular SP proves the true independent G# constructed above, while also proving D(not G#) and therefore not H(G#). This does not contradict reflexivity: actual truth does not imply H-necessity. It identifies the precise shape a successful construction must permit.

### A fixed pure arithmetic witness to the numerical H-Barcan failure

Choose G in the Pi^0_2 form forall n P(n) used above. Then SP entails

    forall n in N_e H(P#(n)),
    not H(forall n in N_e P#(n)).

Thus the Barcan implication for H with quantification restricted to N_e fails at this one fixed PURE matrix in every hypothetical SP model. This is not an appeal to a general unrecorded H-Barcan law. The first line is the proved U_P consequence; the second is the admitted SP instance D(not G#), since Max+not G# is consistent. This is exactly where collecting the separately correct numerical instances into one distinctness-preserving neighborhood would be invalid.

One can also name a pure relation

    F := lambda n . I_e and N_e(n) and not P#(n).

Max entails F!=bottom: the consistent C-sentence I_e∧not G# supplies a point with a true instance of F, so F=bottom is not a C-theorem. But SP entails forall n not F(n), since it entails G#. More strongly, for every ACTUAL number n, U_P gives the literal identity F(n)=bottom. Consequently F is a nonzero pure relation with empty actual extension, and it vanishes as an entity at each actual numerical argument. The stronger literal statement is deliberately restricted to N_e; a nonnumber may become a number elsewhere. This concrete arithmetic example is separate from the previously saved finite-cell ghosts and uses no new constants or language.

The finite-neighborhood problem is now sharper. The still-unsettled conjunction Max+G#+D(not G#) would supply a Max point making this true arithmetic sentence actual but H-contingent. Its consistency is not established by the separate consistency of Max+G# and Max+not G#. Proving the universal implication G#→H(G#), on the other hand, would conflict with the SP consequences just proved. Neither direction has been established here.

## Arithmetic checks on the term and quotient routes

### Numeral canonicity of the common term algebra

For a pure one-individual term T(a) of type nu_e,

    C(a) proves N_e(T(a))
      iff C(a) proves T(a)=numeral k for some standard k.

The reverse implication is numerical induction. For the forward implication, evaluate the term at the supported singleton Max source already constructed. Its actual number field is standard, so T(a) there equals some standard numeral. The common-term embedding identifies equality of pure a-terms at this Max point with C(a)-provable equality. Hence the displayed equality is a C(a)-theorem. This is semantic canonicity; it does not assert that searching for the numeral has a recursive bound.

Consequently ANY genuine Max model all of whose nu_e entities are pure a-term denotations has standard N_e. If n=T(a) is an actual number, necessary numberhood makes N_e(T(a))=top true. Common-term identity correctness makes that a C(a)-theorem, so the previous paragraph applies. It follows in particular that any full Henkin truth V on the fixed algebra B, CODED BY ITS TRUTH BITS ON PURE a-TERMS, computes standard first-order arithmetic truth: given an arithmetic sentence, query V on its pure translation. Such a V cannot be arithmetical in that fixed syntactic presentation. This rules out a finite-jump truth-filter construction on B, not the existence of an arbitrary sufficiently complex V.

The restriction is stronger than what is needed for an essential extension. Unnamed numerical elements in an essential extension have not been ruled out. The frozen conditional low-model results for SP (`../notes/strong-possibility-degree.md`, §§5–6) concern models with new elements; they do not furnish a truth interpretation on the fixed domains B.

**Numerical Henkin clauses at the existing source.** More positively, for V inherited from the standard supported source, every OUTER number-restricted quantifier has the correct old-term witness clause, with an arbitrary pure matrix F and arbitrary old parameters:

    V([exists n (N_e(n) and F(n))])
       iff V([N_e(T) and F(T)]) for some old term T.

A true left side has an actual numerical witness, which is a standard numeral and hence old. The reverse direction is existential introduction. No Boolean restriction on F is needed for this one clause, even if F contains modal-valued or quantified terms. Universal numerical clauses follow dually. This does not inductively validate unrestricted inner quantifiers over other sorts: their whole internal values are what V reads in this assertion. Nor can it be combined with Boolean elementarity to justify an outer relational existential followed by infinitely many variable numerical evaluations.

### A disjunction theorem when the witnesses are numerical

Let E be a closed existential finite-Boolean-identity sentence, allowing individual witnesses and numerical witnesses, with each numerical witness explicitly guarded by N_e(n)=top. The identity terms in its matrix may otherwise be arbitrary, including quantified and modal terms. If E is true at the standard supported singleton source, then Max proves E.

Choose actual witnesses there. Every individual witness is the sole a, and each guarded numerical witness is some standard numeral. Substitute these into the finite matrix. Each resulting identity is between pure a-terms, so its true/false value is the same at every selected individual in every Max model, by the common-term embedding. The whole Boolean matrix therefore holds there with precisely these old-term witnesses. It follows that every Max model satisfies E, and Henkin completeness gives Max⊢E.

Consequently Max has the finite disjunction property for this entire guarded numerical/individual witness fragment: evaluate a proved disjunction at the standard source and apply the preceding argument to the branch true there. Equivalently, that same genuine source simultaneously satisfies every Max-consistent universal identity constraint whose potentially violating tuples are guarded numbers and individuals. This includes arbitrary pure coefficient terms and is not restricted to first-order arithmetic matrices.

The theorem does NOT say that every Max-consistent such existential E is Max-provable. A nonstandard Max model can satisfy an E false at the standard source. Nor does it cover an unguarded variable of type nu_e: most entities of that relational type need not be numbers. Any failed disjunction outside this protected fragment must use an essentially nonnumerical relational witness; the proposition r in the modal template E_P is exactly such a witness.

One can also include existential relational witnesses occurring only in Boolean polynomials at their respective sorts, with arbitrary pure coefficients depending on the numerical and individual witnesses. First replace the latter by the standard numerals and a supplied by the source; then Boolean elementarity replaces each relational tuple by old terms while preserving the finite identity matrix. The disjoint many-sorted Boolean version handles several sorts. Evaluation truth tests are not being silently converted to identities here. A remaining failed-disjunction candidate must genuinely use witness-dependent application, modal values, quantified term values, or another operation outside these Boolean fragments.

### Actual numerical elements survive every B-preserving quotient

Let A be the full logical term reduct of a genuine Max model, let B be its common pure a-term subalgebra, and let pi:A→Q be ANY quotient injective on B. Then pi is injective on A's actual numerical domain and sends each such number to an element satisfying N_e(n)=top in Q.

The second assertion follows from necessary numberhood and preservation of equations. For distinct actual numbers n,m, the numerical distinctness lemma gives

    I_e ≤ (n!=m).

This is the literal Boolean inequality supplied by C's Box(I_e→n!=m), under the actual numerical premises; see the recorded arithmetic write-up, Lemma 6. Since I_e is nonzero and belongs to B, pi(I_e) is nonzero. Were pi(n)=pi(m), the displayed inequality would give pi(I_e)≤bottom, a contradiction. Therefore numerical distinctness cannot be erased by an essential quotient, or by any weaker B-preserving quotient.

This does not prove a Henkin truth lemma for Q. A previously nonnumerical unnamed entity can in principle acquire N_e-value top, and a quantified arithmetic term's internal value still needs to agree with quantification over the resulting domain. In particular preserving a nonstandard numerical witness does not preserve every universal formula about it. The obstruction is not simply that all nonstandard numbers must collapse to numerals.

### Max already decides the first arithmetic level

For completeness, the standard-root comparison can be located more precisely in the arithmetic hierarchy. Max decides every closed Sigma^0_1/Pi^0_1 arithmetic sentence correctly. Here is a proof from the recorded arithmetic lemmas, retaining the finite-type syntax.

Under I_e and numerical parameters, every bounded arithmetic formula delta is equivalent both to Box(I_e→delta) and, with its truth reversed, to Box(I_e→not delta). More explicitly, both delta→Box(I_e→delta) and not delta→Box(I_e→not delta) hold under those premises. Atomic equality uses NI and numerical distinctness under I_e; Sum and Prod use the recorded Lemma 7. Numerical order may be defined through Sum: a positive comparison transports its witness, and a negative comparison uses PA trichotomy and the opposing comparison or equality. Boolean combinations follow immediately.

For a bounded universal, prove the positive implication by N_e-induction on its bound m. The step from m to Suc(m) combines the inductive boxed statement for the smaller segment with the boxed matrix instance at m, using the PA decomposition of the larger segment under I_e. A false bounded universal has a bounded counterexample, whose order fact and negated matrix transport. Bounded existentials are dual. All boxed PA facts come from necessitating whole C-theorems with I_e retained as antecedent; no Max or optional premise is necessitated. Arithmetic notation is first translated into the original RELATIONAL Sum/Prod language, before inserting modalities. For a compound arithmetic expression, carry its finitely many numerical value witnesses through the argument; their Sum/Prod equations transport under I_e, and PA uniqueness there identifies the transported values. There is no addition of numerical function symbols inside modal contexts, no choice operation, and no function type ending in e.

If S is the Sigma^0_1 sentence exists n delta(n), define the PURE positive-existential identity sentence

    E_S := exists n [N_e(n)=top and (I_e∧delta(n))=I_e].

The bounded-formula argument and necessary numberhood give C+I_e⊢S#↔E_S (with a finite tuple if needed). A closed positive-existential identity sentence true in any Max model is a C-theorem, by the saved positive-reflection lemma. If a false standard Sigma^0_1 sentence S were Max-consistent, this would make E_S a C-theorem and therefore S# a C+I_e theorem, contradicting the standard C+I_e model. Thus Max proves its negation. True Sigma^0_1 sentences are PA-theorems and hence Max-theorems. This proves the claimed first-level correctness.

The same argument with numerical parameters shows that a true Sigma^0_1 formula S(n) necessitates itself conditional on I_e: transport its numerical witness and the bounded matrix. Consequently, for the Pi^0_2 sentence G=forall n P(n), C+I_e proves G#↔U_G. The forward implication supplies the boxed conditional for each numerical n; the reverse is the earlier reflexivity argument. Thus U_G is an identity-only reformulation of G under the stated arithmetic premise, not an extra arithmetic assumption.

**Second check of the Pi^0_2 bound.** Under I_e, every Sigma^0_2 arithmetic sentence S satisfies S→H(S). Write S as exists n in N_e not T(n), with T Sigma^0_1, and replace T(n) by its positive-existential identity expression E_T(n). Such a positive expression satisfies E_T(n)↔Box E_T(n) in C. At an actual numerical witness n, take q=I_e∧(E_T(n)!=top). It is true and possibility-fixed: I_e and a disequality are both diamond-fixed, and finite meets of diamond-fixed propositions are diamond-fixed. Necessary numberhood and the guarded equivalence T(n)↔E_T(n) give q≤S, so q witnesses H(S). This does not assert Box(S). Now if A is true Pi^0_2, Max+A# is consistent at the standard root, so SP supplies D(A#). The implication not A#→H(not A#) just proved excludes not A# at an SP point. This independently recovers SP⊢A# without invoking a Barcan step.

It follows that every true Sigma^0_2 arithmetic sentence is a Max-theorem: choose a standard existential witness and apply the true Pi^0_1 case to its matrix. Conversely no false arithmetic sentence is a Max-theorem, by the standard Max model. Thus Max's Sigma^0_2 arithmetic consequences are exactly the standardly true ones, although a false Sigma^0_2 sentence such as not G can still be CONSISTENT with Max. SP's additional true Pi^0_2 consequences decide this next level; they also entail every true Sigma^0_3 sentence by choosing a standard witness. No Sigma^0_3 soundness of SP is claimed without a standard-arithmetic SP model or another argument.

### The arithmetic correctness bound is sharp if SP is consistent

If SP is consistent, some true Pi^0_3 arithmetic sentence G_3 is NOT an SP theorem. Its false Sigma^0_3 negation is therefore consistent with SP. This uses the preceding lower bound and the elementary effectiveness upper bound, not an assumed standard SP model.

Indeed, Max theoremhood is Sigma^0_2, so its consistency side condition is decidable in 0''. The SP axioms, and their deductive closure, are consequently enumerable in 0''. Suppose SP also proved every true Pi^0_3 sentence. For any Sigma^0_3 arithmetic sentence A, enumerate SP proofs of A# and not A# in parallel using 0''. If A is true, the preceding true-Sigma^0_3 result supplies its proof; if A is false, its true Pi^0_3 negation supplies the other proof. Consistency prevents the incorrect answer. This would decide Sigma^0_3 arithmetic truth, and hence the halting problem 0''', using 0'', contradicting strictness of the Turing jump. Thus such a G_3 exists. This is an existence argument, not a displayed explicit code for G_3. The same enumeration upper bound is independently recorded in `../notes/strong-possibility-degree.md`, §5.

Write G_3=forall n P_2(n) with P_2 Sigma^0_2. Every standard instance P_2(k) is true and therefore SP-provable, yet their universal closure is not. So the earlier one-step omega-rule with C+I_e as reference CANNOT in general be iterated with SP as reference, assuming SP consistent.

There is also a concrete form of the remaining old-term witness problem. The consistent extension SP+not G_3 requires a numerical witness to exists n not P_2(n). No pure a-term can supply one: whenever such a term is an actual number at a Max point, numeral canonicity identifies it with a standard numeral, and SP proves P_2 of that numeral. Thus any model of this extension has a nonstandard number unnamed by the old pure a-terms. This rules out a blanket old-term Henkin witness-density claim even after SP itself is imposed. It does not establish whether SP+G_3 is consistent, or whether any term-generated SP model exists. External countability supplies no internal pure enumeration that would remove this distinction.

**Source check during this continuation.** Fresh search-index excerpts of [Goodsell's archived manuscript](https://philarchive.org/archive/GOOAIN) explicitly display Lemma 1 as an HK theorem translating PA under I (printed p.12), and Lemmas 6–7 as HK statements about numerical distinctness and Sum/Prod under I (printed p.17). These corroborate the precise unboxed base used here and do not add Countable Boolean Completeness. The p.12 excerpt also warns about replacing relational arithmetic by function symbols in intensional contexts; the preceding proof uses the relational translation throughout. Direct opening of the full PDF still returned 403, so this is a partial indexed-source check, not a new full manuscript audit.

## End-of-hour boundary and a concrete next target

The remaining focused two-axiom problem is

    Con(Max + U_G + D(not G#)),

where U_G is U_P for the Sigma^0_1 matrix of the independent Pi^0_2 sentence G. Each added axiom is separately Max-consistent: the standard supported source supplies U_G, and a Max model of not G# supplies D(not G#) by reflexivity. Both belong to the universal identity fragment. Their conjunction would provide the numerical H-Barcan failure required by SP while keeping the actual arithmetic G# true.

By G#↔U_G under I_e, this is equivalently the previously isolated Con(Max+G#+D(not G#)) question. The U_G presentation makes its precise universal-identity syntax visible.

If this conjunction were inconsistent, Max would prove the existential-identity disjunction not U_G or H(G#), with neither branch Max-provable. That would refute SP. A model of the conjunction would repair this specific arithmetic obstruction but would not establish full SP. Neither outcome was obtained in this hour. The source construction, arithmetic bounds, witness-fragment results, and quotient checks above are the completed progress.

Only this follow-up note was edited. Frozen notes, source proofs, database records, generated outputs and Lean files were left untouched. The repository validator passes: 132 principles, 447 results, 162 models. That is a repository validation result, not formal verification of the new mathematics.
